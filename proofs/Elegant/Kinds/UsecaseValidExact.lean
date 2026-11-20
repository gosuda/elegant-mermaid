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
import Elegant.Layered.ExactBorderHardProof
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
import Elegant.Layered.ExactGroupMarkerOrderProof
import Elegant.Layered.ExactLoopMarkerCoreProof
import Elegant.Layered.ExactLoopMarkerSpanProof
import Elegant.Layered.ExactLoopMarkerLayerOrderProof
import Elegant.Layered.ExactFlatC7Forward
import Elegant.Layered.ExactFlatC7Placed
import Elegant.Layered.ExactFlatC7Reversed
import Elegant.Layered.ExactFlatC8b
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactPackedTransportResidualsProof
import Elegant.Layered.ExactStepShortFacts
import Elegant.Layered.LoopFootprintTopSeparationCondProof
import Elegant.Layered.ExecutedPartFrameCoresClosed
import Elegant.Layered.ExactCaptionScopeFitWProof
import Elegant.Layered.ExactFlatC8aCore
import Elegant.Layered.ExactSeamClosureGlue
import Elegant.Layered.ExactPartPosGuardProof
import Elegant.Layered.ExactStepGeometryProof
import Elegant.Layered.ExactFlatC6WProof
import Elegant.Layered.ExactFlatC6ShelfBorderProof
import Elegant.Layered.ExactCaptionAncestorLinkVerticalProof
import Elegant.Layered.ExactFlatC7ExclusiveKey
import Elegant.Layered.ExactFlatC8bWProof
import Elegant.Layered.ExactFallbackCaptionFactsProof
import Elegant.Layered.ExactOwnerFrameDisjointProof
import Elegant.Layered.ExactCaptionFitFactsProof
import Elegant.Layered.ExactCaptionFallbackProof
import Elegant.Layered.LoopTopSliverGapProof
import Elegant.Kinds.Usecase
import Elegant.Layered.ExactPlainAncestorImpossibleProof
import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.ExactForeignRankPairAnchorsProof
import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.ExactLoopEnvelopeReserveProof
import Elegant.Layered.ExactLoopEnvelopeLeftNonPlainProof
import Elegant.Layered.ExactForwardScopeFreeProof
import Elegant.Layered.ExactNonfwdExtMissProof
import Elegant.Layered.ExactFlatC6KeysPathsProof
import Elegant.Layered.ExactRunPathGroupsProof
import Elegant.Layered.ExactFlatC6LoopSepProof
import Elegant.Layered.ExactFlatC6LoopSepNonSelfProof
import Elegant.Layered.ExactFlatC6LoopScopeProof
import Elegant.Layered.ExactPlainRightNonPlainProof
import Elegant.Layered.LoopHullExtentFitProof
import Elegant.Layered.LayeredAdmission
import Elegant.Layered.ExactCaptionTitleBranchProof
import Elegant.Layered.ExactCaptionSamePartProof
import Elegant.Layered.ExactPlainNodePathProof
import Elegant.Layered.ExactLoopEnvelopeRightProof
import Elegant.Layered.ExactLoopEnvelopeSidesProof
import Elegant.Layered.ExactFallbackStructuralProof
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
// of `topSliverSpanCovered_holds`) for `labelRuns`; `foreignBorderDivergeStable`
// (with both loop-hull covers closed from it by `loopHullRightCover_closed_plain`
// and `loopHullRightNeighborCover_closed_plain` (`LoopHullExtentFitProof.lean`))
// for `captions`, with the
// old `titleExclusiveSamePart` closed by `titleExclusiveSamePart_holds` and the
// old `executedPartFrameCores` closed by `executedPartFrameCores_closed`). There
// is no `routeLabelsPlaced` field: it is a closed proved theorem used inside
// the `labelRuns` term. There is no `bracketMarkersAtRank` field either: the
// proved `bracketMarkersAtRank'` is used directly.
//
// Replaced `flatC7`: derived in `exactBaseSeams` by `flatC7B_layoutX_fitW`
// (`ExactCaptionScopeFitWProof.lean`) over the assembled loop separation
// (`glue_loopEnvelopeMiss` via `X_runLocalLoopSeparation_of_envelopeMiss`)
// and the assembled W scope clearance (`glue_captionScopeFitW` over the
// W title branch (from the `capTitleBand` W field via
// `xctb_captionTitleBranchClearW_of_bandW`), the W descendant
// clearance (from the W title branch plus the `capDescBand` W field via
// `x_captionDescendantSamePartClearW_holds`), and the
// two containments (both from the cases derived from the closed title),
// with the node-border premise closed by `x_ownerResNodeBorderZeroX_holds`).
// Replaced `flatC8a`: derived in `exactBaseSeams` by `flatC8aB_layoutX`
// (`ExactFlatC8aCore.lean`) over the kept `c8aChain` field, the closed
// cluster/order/bracket/plain facts (plain via the closed node-path
// residual), and the side fact derived from the kept chain, shared with
// the caption run, forward clearance, and seams-imply-foreign assemblers
// below.
// Replaced `partFrameCores` and `loopEnvelopeMiss`: derived in
// `exactBaseSeams` by `glue_partFrameCoresW` and `glue_loopEnvelopeMiss`
// (`ExactSeamClosureGlue.lean`) over the kept leaves (`capBelow`,
// `capAlignB`, `c8aChain`, `fwdStrict`, `nonfwdHull`, the plain alignment
// from the kept `foreignBorderDivergeStable`, and the two kept loop
// leaves), the closed caption-run premise (`exactPlainAncestorImpossible`),
// the closed span/order/bracket/plain facts, the side fact from the kept
// chain, the closed forward scope freedom, the nonforward miss from the
// two nonforward residuals, and the loop miss assembly. The remaining loop
// premises cover the group rank and marker order. The seven caption-run premises, the
// dummy-in-dummy premises, and the plain alignment are proved inside.
// `flatC8b` itself is still derived by `flatC8bB_layoutX_W`
// (`ExactFlatC8bWProof.lean`) over these W cores, the closed
// `X_packedPartTransportBounded_closed`
// (`ExactPackedTransportResidualsProof.lean`), and the W fallback clearance
// `X_fallbackCaptionClearBW_closed` (`ExactFallbackCaptionFactsProof.lean`)
// over the two kept narrower open fields below (`fbContain`,
// `fbStrict`) with the closed title and the cases derived from it
// (`X_NonfixedGroupTitleX_holds`, `X_FallbackOwnerCasesX_holds`;
// `fbFix` closed by `xctb_fixedOwnerFitX_holds`). The W owner-frame
// disjointness argument is `XFB_ownerFrameDisjointW_of_chain exactIds
// R.c8aChain` (`ExactOwnerFrameDisjointProof.lean`), so no `fbDisj` field
// remains.
// Replaced `flatC6`: derived in `exactBaseSeams` by `flatC6B_layoutXW`
// (`ExactFlatC6WProof.lean`) over the six kept narrower open W fields below,
// the closed chain keys (via `X6_chainEndpointKeysW_holds`), the closed
// outside-paths fact (via `X6_declOutsidePathsW_holds` over the closed
// `X6_runPathGroupsW_holds`), and the separation fact (via
// `X6_loopFootprintSeparationW_holds` over `x6_loopSep_nonSelf_closed_from_leaves`
// (`ExactFlatC6LoopScopeProof.lean`) from the `x6scopeRest` residual, the closed
// scope-B fact, the closed/kept envelope leaves, and the owner via
// `glue_loopEnvOtherOwner`), with the run-id premise closed by
// `x_exclusiveRunNodeDecl_holds` (`ExactFlatC7ExclusiveKey.lean`).
// Replaced step fields: `stepC6`, `stepC7`, `stepC8a`, `stepC8b` are derived in
// `exactBaseSeams` from the geometry hypothesis fields below via
// `stepC6_layoutX`, `stepC7_layoutX`, `stepC8a_layoutX`, `stepC8b_layoutX`
// (`ExactStepFacts.lean`): `stepC6Geometry_layoutX` over the two named C6
// residuals, `stepC7Geometry_layoutX` over the three named C7 residuals, and
// `stepC8bGeometry_layoutX` over the closed C8b core
// (`glue_stepC8bCoreB` via `XSGL_c8bCore`), the two kept C8b residuals,
// and the closed caption residuals (`glue_stepC8bCapStrictB`,
// `glue_stepC8bCapDisjB` via the `XSGL_` closers), with the box/ancestry/fit
// premises closed by `XG_child_boxes_insetB`, `XG_content_fit_strict`
// (`ExactStepGeometryProof.lean`), and `stepC8aAncestry_layoutX`
// (`ExactStepShortFacts.lean`); the anchor/ancestry/C8a-geometry premises stay
// closed by `stepC6Anchors_layoutX`, `stepC8aAncestry_layoutX`, and
// `stepC8aGeometry_layoutX` (`ExactStepShortFacts.lean`). The narrower
// `c6Geometry_of_seams`/`c8bGeometry_of_seams` derivations do not apply.
// -/
structure ExactSeams (exactIds : List String) : Prop where
  /-- Open separation residual feeding `flatC6B_layoutXW` as `hsepW` via
  `x6_loopSep_nonSelf_closed_from_leaves` (`ExactFlatC6LoopScopeProof.lean`):
  the non-exclusive/component-beyond in-proper cases conclude the footprint
  separation directly. The bounded-exclusive scope half closes outright by
  `x6_loopSep_nonSelf_scopeB_holds`. The loop envelope retains the
  `loopGrpOverlap` and marker-order leaf premises. Strictly narrower
  than `X6_LoopSep_NonSelf_Scope`
  (extra proper bound and non-exclusivity premises), which was FALSE on
  out-of-bounds indices. -/
  x6scopeRest : Layered.PipelineImpl.X6_LoopSep_NonSelf_ScopeRest exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hbridgeW`. -/
  x6bridge : Layered.PipelineImpl.X6_RouteScopeBridgeW exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hchainW` (the run-id antecedent is the closed `x_exclusiveRunNodeDecl_holds`). -/
  x6chain : Layered.PipelineImpl.X_ExclusiveRunNodeDecl exactIds → Layered.PipelineImpl.X6_ChainEndpointKeysW exactIds → Layered.PipelineImpl.X6_DeclOutsidePathsW exactIds → Layered.PipelineImpl.X6_ShelfPositiveW exactIds → Layered.PipelineImpl.X6_ChainCaseW exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hloopW`. -/
  x6loop : Layered.PipelineImpl.X6_ShelfPositiveW exactIds → Layered.PipelineImpl.X6_BorderZeroRealW exactIds → Layered.PipelineImpl.X6_LoopCaseW exactIds
  /-- Narrower residual feeding `glue_loopEnvelopeMiss` as `hgrp` via
  `XLEM_groupOtherRank_holds`: the y-overlap half of the group-owner
  other-rank miss (the y-disjoint half closes outright). -/
  loopGrpOverlap : Layered.PipelineImpl.XLEM_GroupOverlapMiss exactIds
  /-- Narrower open fact feeding the descendant clearance derivation as
  `hfall`: the W fallback band behind `X_CaptionDescendantSamePartClearW`
  (via `x_captionDescendantSamePartClearW_holds` over the W title band
  below). Proved from `X_FallbackOwnerCasesX` by
  `xcb_descendantFallbackBandXW_of_cases`. -/
  capDescBand : Layered.PipelineImpl.X_DescendantFallbackBandXW exactIds
  /-- Narrower open fact feeding `glue_captionScopeFitW` as `htitle` via
  `xctb_captionTitleBranchClearW_of_bandW`: the W title band behind the
  W installed-title branch clearance. Proved from `X_RunTitleBandClearX` by
  `xcb_titleSamePartBandXW_of_runX`. -/
  capTitleBand : Layered.PipelineImpl.X_TitleSamePartBandXW exactIds
  /-- Open leaf feeding `flatC8aB_layoutX` as `hchain` (shared with the
  route-label foreign clearance). Kept: the only closed chain form needs
  the X-twin stability, not the kept plain `foreignBorderDivergeStable`. -/
  c8aChain : Layered.PipelineImpl.X_ForeignBorderChainXAligned exactIds
  /-- Open leaf feeding `glue_captionRunClearXW` as `hbelow`: the marker
  below residual. -/
  capBelow : Layered.PipelineImpl.XCA_MarkerBelowX exactIds
  /-- Open leaf feeding `glue_captionRunClearXW` as `halignB` (shared with
  the seams-imply-foreign assembler). -/
  capAlignB : Layered.PipelineImpl.XB_ForeignBorderChainXAligned exactIds
  /-- Open leaf feeding the forward/leftover assemblers as `hstrict`:
  strict dummy linkage. -/
  fwdStrict : Layered.PipelineImpl.XFR_StrictDummyLinkedX exactIds
  /-- Narrower open fact feeding `glue_nonforward` as `hmiss` via
  `XNonfwd_extMissRem_of_parts` and `XNonfwd_ExtMiss_of_rem`: the
  non-self y-overlap half of the exterior miss (the y-disjoint half
  closes outright). -/
  nonfwdNonSelfY : Layered.PipelineImpl.XNonfwd_ExtMissNonSelfYOverlap exactIds
  /-- Narrower open fact feeding `glue_nonforward` as `hmiss` via
  `XNonfwd_extMissRem_of_parts` and `XNonfwd_ExtMiss_of_rem`: the
  group-self y-overlap half of the exterior miss. -/
  nonfwdGroupSelfY : Layered.PipelineImpl.XNonfwd_ExtMissGroupSelfYOverlap exactIds
  /-- Open leaf feeding `glue_nonforward` as `hhull`: nonforward group
  hull extension. -/
  nonfwdHull : Layered.PipelineImpl.XNonfwd_GroupHullExt exactIds
  /-- Narrower open fact consumed by `X_fallbackCaptionClearBW_closed` as `hcontain`: the fit-conditioned fallback containment. -/
  fbContain : Layered.PipelineImpl.X_OwnerCaptionContainFallbackFit exactIds
  /-- Narrower open fact consumed by `X_fallbackCaptionClearBW_closed` as `hastrict`: W ancestor-frame strictness. -/
  fbStrict : Layered.PipelineImpl.X_AncestorFrameStrictW exactIds
  /-- Narrower open fact consumed by `captions` via `flatC8a_executed`: ordering-stage stability of divergent blocks. Closed to the old alignment by `foreignBorderChainXAligned'` (`ForeignBorderChainXAlignedClosed.lean`). -/
  foreignBorderDivergeStable : Layered.PipelineImpl.ForeignBorderDivergeStable
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
  /-- Open C8b residual consumed by `stepC8bGeometry_layoutX` as `hChildLabelsB`. -/
  stepC8bChildLabels : Layered.PipelineImpl.XG_StepC8bChildLabelsB exactIds
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
  flatC6 := Layered.PipelineImpl.flatC6B_layoutXW exactIds
    (Layered.PipelineImpl.x_exclusiveRunNodeDecl_holds exactIds)
    (Layered.PipelineImpl.X6_chainEndpointKeysW_holds exactIds)
    (Layered.PipelineImpl.X6_declOutsidePathsW_holds exactIds
      (Layered.PipelineImpl.X6_runPathGroupsW_holds exactIds))
    (Layered.PipelineImpl.X6_shelfPositiveW_of_partPosW exactIds
      (Layered.PipelineImpl.X6_PartPosW_of_fixedSizesPositive exactIds))
    (Layered.PipelineImpl.X6_loopFootprintSeparationW_holds exactIds
      (Layered.PipelineImpl.x6_loopSep_nonSelf_closed_from_leaves exactIds
        (Layered.PipelineImpl.xlem_plainRightNonPlain_holds exactIds)
        R.loopGrpOverlap (Layered.PipelineImpl.XLEG_groupMarkerOrderX_of_leaves exactIds (Layered.PipelineImpl.xleg_loopMarkerCoreX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerLayerOrderX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerSpanX_holds exactIds)) R.x6scopeRest))
    (Layered.PipelineImpl.X6_borderZeroRealW_holds exactIds
      (Layered.PipelineImpl.X6_borderHardW_holds exactIds R.c8aChain))
    R.x6bridge R.x6chain R.x6loop
  flatC7 := Layered.PipelineImpl.flatC7B_layoutX_fitW exactIds (Layered.PipelineImpl.X_runLocalLoopSeparation_of_envelopeMiss exactIds (Layered.PipelineImpl.glue_loopEnvelopeMiss exactIds (Layered.PipelineImpl.XLEM_plainReserve_holds exactIds) (Layered.PipelineImpl.XLEM_groupOtherRank_holds exactIds R.loopGrpOverlap) (Layered.PipelineImpl.XLEM_leftNonPlain_holds exactIds) (Layered.PipelineImpl.XLEM_plainRightMiss_holds exactIds (Layered.PipelineImpl.xlem_plainRightNonPlain_holds exactIds)) (Layered.PipelineImpl.XLEG_groupMarkerOrderX_of_leaves exactIds (Layered.PipelineImpl.xleg_loopMarkerCoreX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerLayerOrderX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerSpanX_holds exactIds)) (Layered.PipelineImpl.glue_loopEnvOtherOwner exactIds R.loopGrpOverlap (Layered.PipelineImpl.xlem_plainRightNonPlain_holds exactIds) (Layered.PipelineImpl.XLEG_groupMarkerOrderX_of_leaves exactIds (Layered.PipelineImpl.xleg_loopMarkerCoreX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerLayerOrderX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerSpanX_holds exactIds))))) (Layered.PipelineImpl.glue_captionScopeFitW exactIds (Layered.PipelineImpl.x_captionDescendantSamePartClearW_holds exactIds (Layered.PipelineImpl.xctb_captionTitleBranchClearW_of_bandW exactIds R.capTitleBand) R.capDescBand) (Layered.PipelineImpl.xctb_ownerCaptionContainFallbackFitW_of_cases exactIds (Layered.PipelineImpl.X_FallbackOwnerCasesX_holds exactIds (Layered.PipelineImpl.X_NonfixedGroupTitleX_holds exactIds))) (Layered.PipelineImpl.xcapSamePart_ownerScopeW_of_cases exactIds (Layered.PipelineImpl.X_FallbackOwnerCasesX_holds exactIds (Layered.PipelineImpl.X_NonfixedGroupTitleX_holds exactIds))) (Layered.PipelineImpl.xctb_captionTitleBranchClearW_of_bandW exactIds R.capTitleBand))
  flatC8a := Layered.PipelineImpl.flatC8aB_layoutX exactIds (Layered.PipelineImpl.XB_foreignClusterRankSpans_holds exactIds (Layered.PipelineImpl.XB_foreignRankPairAnchors_holds exactIds)) (Layered.PipelineImpl.XB_foreignBorderLayerOrder_holds exactIds) R.c8aChain (Layered.PipelineImpl.XN_bracketMarkersAtRank_holds exactIds) (Layered.PipelineImpl.XN_plainClearOfSideMarker_of_path exactIds (Layered.PipelineImpl.XN_plainNodePathResidual_holds exactIds)) (Layered.PipelineImpl.XN_sideMarkerSpanAligned_of_chain exactIds R.c8aChain)
  flatC8b := Layered.PipelineImpl.flatC8bB_layoutX_W exactIds (fun {inp o res} execution hwf hfp => Layered.PipelineImpl.glue_partFrameCoresW exactIds (Layered.PipelineImpl.XCA_groupLinkXW_closed exactIds) R.capBelow (Layered.PipelineImpl.exactPlainAncestorImpossible_holds exactIds) (Layered.PipelineImpl.XB_foreignClusterRankSpans_holds exactIds (Layered.PipelineImpl.XB_foreignRankPairAnchors_holds exactIds)) (Layered.PipelineImpl.XB_foreignBorderLayerOrder_holds exactIds) R.capAlignB (Layered.PipelineImpl.XN_bracketMarkersAtRank_holds exactIds) (Layered.PipelineImpl.XN_plainClearOfSideMarker_of_path exactIds (Layered.PipelineImpl.XN_plainNodePathResidual_holds exactIds)) (Layered.PipelineImpl.XN_sideMarkerSpanAligned_of_chain exactIds R.c8aChain) R.c8aChain R.fwdStrict (Layered.PipelineImpl.XFR_ForwardScopeFreeX_holds exactIds) (Layered.PipelineImpl.XNonfwd_ExtMiss_of_rem exactIds (Layered.PipelineImpl.XNonfwd_extMissRem_of_parts exactIds R.nonfwdNonSelfY R.nonfwdGroupSelfY)) R.nonfwdHull (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.glue_loopEnvelopeMiss exactIds (Layered.PipelineImpl.XLEM_plainReserve_holds exactIds) (Layered.PipelineImpl.XLEM_groupOtherRank_holds exactIds R.loopGrpOverlap) (Layered.PipelineImpl.XLEM_leftNonPlain_holds exactIds) (Layered.PipelineImpl.XLEM_plainRightMiss_holds exactIds (Layered.PipelineImpl.xlem_plainRightNonPlain_holds exactIds)) (Layered.PipelineImpl.XLEG_groupMarkerOrderX_of_leaves exactIds (Layered.PipelineImpl.xleg_loopMarkerCoreX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerLayerOrderX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerSpanX_holds exactIds)) (Layered.PipelineImpl.glue_loopEnvOtherOwner exactIds R.loopGrpOverlap (Layered.PipelineImpl.xlem_plainRightNonPlain_holds exactIds) (Layered.PipelineImpl.XLEG_groupMarkerOrderX_of_leaves exactIds (Layered.PipelineImpl.xleg_loopMarkerCoreX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerLayerOrderX_holds exactIds) (Layered.PipelineImpl.xleg_loopMarkerSpanX_holds exactIds)))) execution hwf hfp) (Layered.PipelineImpl.X_packedPartTransportBounded_closed exactIds) (fun {inp o res} execution hwf hfp => Layered.PipelineImpl.X_fallbackCaptionClearBW_closed exactIds R.fbContain (Layered.PipelineImpl.xctb_fixedOwnerFitX_holds exactIds) (Layered.PipelineImpl.X_NonfixedGroupTitleX_holds exactIds) (Layered.PipelineImpl.XFB_ownerFrameDisjointW_of_chain exactIds R.c8aChain) R.fbStrict (Layered.PipelineImpl.X_FallbackOwnerCasesX_holds exactIds (Layered.PipelineImpl.X_NonfixedGroupTitleX_holds exactIds)) execution hwf hfp)
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
        (Layered.PipelineImpl.executedPartFrameCores_closed execution hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.loopFootprintTopSeparation_closed inp o res hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.loopFootprintBeyondProper_closed inp o res hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.topSliverMarkerReady_of_span (inp := inp) (o := o) (res := res) hwf hfp Layered.PipelineImpl.topSliverSpanCovered_holds))) (Layered.PipelineImpl.loopFootprintBeyondProper_closed inp o res hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.topSliverMarkerReady_of_span (inp := inp) (o := o) (res := res) hwf hfp Layered.PipelineImpl.topSliverSpanCovered_holds)) (fun comp hcomp candidate run orderOptions hrun => Layered.PipelineImpl.loopHullRightCover_closed_plain inp o res hwf hfp R.foreignBorderDivergeStable execution comp hcomp candidate run orderOptions hrun) (fun comp hcomp candidate run orderOptions hrun => Layered.PipelineImpl.loopHullRightNeighborCover_closed_plain inp o res hwf hfp R.foreignBorderDivergeStable execution comp hcomp candidate run orderOptions hrun))
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
  stepC8b := Layered.PipelineImpl.stepC8b_layoutX exactIds (Layered.PipelineImpl.stepC8bGeometry_layoutX exactIds (Layered.PipelineImpl.glue_stepC8bCoreB exactIds) (Layered.PipelineImpl.XG_child_boxes_insetB exactIds) R.stepC8bChildLabels (Layered.PipelineImpl.XG_fitStrictB_of_content exactIds) (Layered.PipelineImpl.glue_stepC8bCapStrictB exactIds) (Layered.PipelineImpl.glue_stepC8bCapDisjB exactIds) (Layered.PipelineImpl.stepC8aAncestry_layoutX exactIds) R.stepC8bParentFrame)

 /-- Usecase family validity from the exact seams: the executed nested family run
 `layoutFamilyB (layoutRecursiveX actorIds (m.boxes.length + 1))` underlying
 `Usecase.layout` satisfies the hard constraints. The nested recursion flattens
 through `layoutRecursiveB_compose` to the combined fuel
 `(m.boxes.length + 1) + (m.boxes.length + 1)` over `layoutX actorIds`, and the
 the per-route `layoutRecursiveB_c5`). `WellFormed`, `WithinLimits` and the
 `sizes` equation are the public validity premises, with the user-approved
 admission guard `hadm` (recoverable from a successful `Usecase.layout` run by
 `Layered.admit_ok`) supplying the id, fit, and disjointness premises via
 `Layered.layeredAdmissibleB_spec`; the family theorem derives its own guards
 from the success equation. The draw-shapes post-pass stays a separate draft. -/
 theorem usecase_family_valid_of_exactSeams {m : Model} {fixed : List (String × Size)}
     {res : Layered.FamilyResult}
     (R : ExactSeams (actorIds m))
     (hadm : Layered.layeredAdmissibleB (input m fixed) = true)
     (hwf : WellFormed m) (hlim : WithinLimits m)
     (hfixed : sizes m = .ok fixed)
     (h : Layered.layoutFamilyB
       (Layered.PipelineImpl.layoutRecursiveX (actorIds m) (m.boxes.length + 1))
       (input m fixed) m.options = .ok res) :
     HardConstraints res.scene.layoutDump := by
  have _ := hwf
  have _ := hlim
  have _ := hfixed
  obtain ⟨hids, hdisj, hfix, hpos⟩ := Layered.layeredAdmissibleB_spec hadm m.options
  obtain ⟨hwf', hrec⟩ := Layered.layoutFamilyB_success h
  have hfp := Layered.layoutFamilyB_framed_parents h
  have hboxes : (input m fixed).boxes = m.boxes := rfl
  rw [hboxes] at hrec
  unfold Layered.PipelineImpl.layoutRecursiveX at hrec
  rw [Layered.PipelineImpl.layoutRecursiveB_compose] at hrec
  have S := exactBaseSeams (actorIds m) R
  have hids' : ∀ mm ∈ (input m fixed).boxes, mm.id ≠ "" := hids
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
    Layered.PipelineImpl.layoutRecursiveB_c6 _ S.flatC6 S.canvasMargins S.frameClear S.subInputB
      S.stepC6 ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options res hwf' hfp hpos hrec,
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

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
import Elegant.Layered.ExecutedPartFrameCoresClosed
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
// Replaced `labelRuns`/`captions` (both base-independent): derived in
// `exactBaseSeams` by the same `baseSeams_of_layered` terms over narrower open
// `LayeredSeams` fields below (`loopFootprintTopSeparation`,
// `loopFootprintBeyondProper` for `labelRuns`; `foreignBorderDivergeStable`,
// `loopHullRightCover`, `loopHullRightNeighborCover` for `captions`, with the
// old `titleExclusiveSamePart` closed by `titleExclusiveSamePart_holds` and the
// old `executedPartFrameCores` closed by `executedPartFrameCores_closed`). There
// is no `routeLabelsPlaced` field: it is a closed proved theorem used inside
// the `labelRuns` term. There is no `bracketMarkersAtRank` field either: the
// proved `bracketMarkersAtRank'` is used directly.
//
// Replaced step fields: `stepC6`, `stepC7`, `stepC8a`, `stepC8b` are derived in
// `exactBaseSeams` from the geometry/ancestry hypothesis fields below via
// `stepC6_layoutX`, `stepC7_layoutX`, `stepC8a_layoutX`, `stepC8b_layoutX`
// (`ExactStepFacts.lean`). Every geometry/ancestry hypothesis stays open: the
// proved outright theorems `stepC8aGeometry_holds`
// (`ExpandChildC8aGeometryExecuted.lean`), `stepC6Anchors_holds` and
// `stepC8aAncestry_holds` (`ExpandChildAncestryProof.lean`) are stated over the
// plain `ExpandChildCallContext` (`RecursiveStepFacts`), not the
// base-parametric `ExpandChildCallContextB` (`RecursiveStepFactsB`), so their
// types do not fit the required hypotheses. The `B` twins
// (`stepC8aGeometry_holdsB`, `stepC6Geometry_holdsB`) still take base-stage
// hypotheses, so no step field is proved outright. The narrower parent-frame
// replacement is blocked too: the old plain fields were plain
// `RecursiveStepFacts`, while these fields are `RecursiveStepFactsB`, so the
// plain `c6Geometry_of_seams`/`c8bGeometry_of_seams` derivations do not apply.
// Each remaining field below names in one line the plain-pipeline theorem
// proving its counterpart, for the porting slices. -/
structure ExactSeams (exactIds : List String) : Prop where
  /-- Plain counterpart: the eight narrow `LayeredSeams` residuals via `flatC6_closed`. -/
  flatC6 : Layered.PipelineImpl.FlatC6B (Layered.PipelineImpl.layoutX exactIds)
  /-- `flatC7B_layoutX` still needs the seven exact facts (loop/forward/reversed separation, `X_RouteLabelsPlaced`, exclusive-decl, exclusive-key, caption-scope). -/
  flatC7 : Layered.PipelineImpl.FlatC7B (Layered.PipelineImpl.layoutX exactIds)
  /-- `flatC8aB_layoutX` still needs the exact C8a span facts and `X_ForeignBorderChainXAligned`. -/
  flatC8a : Layered.PipelineImpl.FlatC8aB (Layered.PipelineImpl.layoutX exactIds)
  /-- `flatC8bB_layoutX` still needs three exact facts (part-frame cores, packed-part transport, fallback caption clear). -/
  flatC8b : Layered.PipelineImpl.FlatC8bB (Layered.PipelineImpl.layoutX exactIds)
  /-- Narrower open fact consumed by `labelRuns`: top separation of the loop footprint. Best partial: `loopFootprintTopSeparation_holds` (needs `ForeignBorderChainXAligned` plus sliver/good premises). -/
  loopFootprintTopSeparation : ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
    WellFormed (Layered.inputModel inp o) → Layered.framedParents inp = true →
    Layered.PipelineImpl.LoopFootprintTopSeparation inp o res
  /-- Narrower open fact consumed by `labelRuns`: beyond-proper footprint separation. Best partial: `loopFootprintBeyondProper_holds` (needs `ForeignBorderChainXAligned` plus sliver residuals). -/
  loopFootprintBeyondProper : ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
    WellFormed (Layered.inputModel inp o) → Layered.framedParents inp = true →
    Layered.PipelineImpl.LoopFootprintBeyondProper inp o res
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
  /-- Base-parametric C6 geometry hypothesis consumed by `stepC6_layoutX`. -/
  stepC6Geometry :
    Layered.PipelineImpl.RecursiveStepFactsB (Layered.PipelineImpl.layoutX exactIds)
      Layered.PipelineImpl.ExpandChildC6Geometry
  /-- Base-parametric C6 anchor hypothesis consumed by `stepC6_layoutX`. -/
  stepC6Anchors :
    Layered.PipelineImpl.RecursiveStepFactsB (Layered.PipelineImpl.layoutX exactIds)
      (fun _ _ _ group _ parent child res =>
        Layered.PipelineImpl.ExpandChildC6Anchors group parent child res)
  /-- Base-parametric C7 geometry hypothesis consumed by `stepC7_layoutX`. -/
  stepC7Geometry :
    Layered.PipelineImpl.RecursiveStepFactsB (Layered.PipelineImpl.layoutX exactIds)
      Layered.PipelineImpl.ExpandChildC7Geometry
  /-- Base-parametric C8a geometry hypothesis consumed by `stepC8a_layoutX`. -/
  stepC8aGeometry :
    Layered.PipelineImpl.RecursiveStepFactsB (Layered.PipelineImpl.layoutX exactIds)
      Layered.PipelineImpl.ExpandChildC8aGeometry
  /-- Base-parametric C8a ancestry hypothesis consumed by both `stepC7_layoutX`
  and `stepC8a_layoutX` (both take the same C8a-ancestry hypothesis type). -/
  stepC8aAncestry :
    Layered.PipelineImpl.RecursiveStepFactsB (Layered.PipelineImpl.layoutX exactIds)
      (fun _ _ _ group _ parent child res =>
        Layered.PipelineImpl.ExpandChildC8aAncestry group parent child res)
  /-- Base-parametric C8b geometry hypothesis consumed by `stepC8b_layoutX`. -/
  stepC8bGeometry :
    Layered.PipelineImpl.RecursiveStepFactsB (Layered.PipelineImpl.layoutX exactIds)
      Layered.PipelineImpl.ExpandChildC8bGeometry

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
  flatC6 := R.flatC6
  flatC7 := R.flatC7
  flatC8a := R.flatC8a
  flatC8b := R.flatC8b
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
            (R.loopFootprintTopSeparation inp o res hwf hfp)
            (R.loopFootprintBeyondProper inp o res hwf hfp)))
        (Layered.PipelineImpl.runLocalForwardSeparation inp o res)
        (Layered.PipelineImpl.runLocalReversedSeparation inp o res),
      Layered.routeLabelDumpBridges hwf
        (Layered.PipelineImpl.labelBelongsToRun hwf Layered.PipelineImpl.routeLabelsPlaced)
        (Layered.PipelineImpl.exclusiveBoxInLabelRun' hwf hfp)⟩
  captions := fun inp o res hwf hfp hfit =>
    Layered.PipelineImpl.sceneCaptionBoxContainment_of_fit hwf hfp hfit
      (Layered.PipelineImpl.titleExclusiveSamePart_holds (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) inp o res hwf hfp)
      (Layered.PipelineImpl.titleExclusiveCrossPart (inp := inp) (o := o) (res := res))
      (fun execution => Layered.PipelineImpl.frameLabels_executed execution hwf hfp hfit
        (Layered.PipelineImpl.executedPartFrameCores_closed execution hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (R.loopFootprintTopSeparation inp o res hwf hfp) (R.loopFootprintBeyondProper inp o res hwf hfp) (R.loopHullRightCover inp o res hwf hfp execution) (R.loopHullRightNeighborCover inp o res hwf hfp execution))
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
  stepC6 := Layered.PipelineImpl.stepC6_layoutX exactIds R.stepC6Geometry R.stepC6Anchors
  stepC7 := Layered.PipelineImpl.stepC7_layoutX exactIds R.stepC7Geometry R.stepC8aAncestry
  stepC8a := Layered.PipelineImpl.stepC8a_layoutX exactIds R.stepC8aGeometry R.stepC8aAncestry
  stepC8b := Layered.PipelineImpl.stepC8b_layoutX exactIds R.stepC8bGeometry

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

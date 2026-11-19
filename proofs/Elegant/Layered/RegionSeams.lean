import Elegant.Layered.RegionFlatInset
import Elegant.Layered.RegionCanvasMargins
import Elegant.Layered.RegionFlatC3
import Elegant.Layered.RegionParentInComponent
import Elegant.Layered.RegionMemberFramesNest
import Elegant.Layered.RegionRunTruthProbes
import Elegant.Layered.RegionFlatC2
import Elegant.Layered.RegionCrossCoordsMetadata
import Elegant.Layered.RegionC5Endpoints
import Elegant.Layered.RegionFlatC8b
import Elegant.Layered.RegionSubInputStepC2
import Elegant.Layered.RegionStepAssemblers
import Elegant.Layered.FamilyAssemblyB
import Elegant.Layered.RegionPipeline
import Elegant.Layered.FrameClearanceSeam
import Elegant.Layered.BracketInsidePremisesProof
import Elegant.Layered.DummyNestedMarkerProof
import Elegant.Layered.TitleCopySpanProof
import Elegant.Layered.PartSeparation
import Elegant.Layered.SubInputWellFormedFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Region seams (packet P12 of `local://region-tower-plan.md`).

`RegionSeams` gathers exactly the open named premises of the finished
region theorems, each strictly narrower than its `BaseSeams` target clause.
`regionBaseSeams` fills all 22 `BaseSeams` fields at the reindexing base
`fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'`,
which is the base every finished recursion-step, sub-input, margin, and
inset theorem is stated over. Clauses with no finished region module yet
are carried as the clause itself, marked OPEN CLAUSE. -/

/-- The reindexing base of the region tower: `layoutRIds` at each
sub-input's reindexed region sets. -/
private abbrev rsmBase (exactIds : List String) (idSets : List (String × List String)) :
    Input → Options → Except LayoutError FamilyResult :=
  fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'

/-- Region C6 geometry hypothesis shape, over the reindexing base. -/
private abbrev rsmC6Geometry (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (rsmBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC6Geometry P inp o group titleHeight parent child res

/-- Region C6 anchor hypothesis shape, over the reindexing base. -/
private abbrev rsmC6Anchors (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (rsmBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC6Anchors group parent child res

/-- Region C7 geometry hypothesis shape, over the reindexing base. -/
private abbrev rsmC7Geometry (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (rsmBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7Geometry P inp o group titleHeight parent child res

/-- Region C8a geometry hypothesis shape, over the reindexing base. -/
private abbrev rsmC8aGeometry (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (rsmBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC8aGeometry P inp o group titleHeight parent child res

/-- Region C8b geometry hypothesis shape, over the reindexing base. -/
private abbrev rsmC8bGeometry (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (rsmBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC8bGeometry P inp o group titleHeight parent child res

/-- Region seams: exactly the open named premises of the finished region
theorems, each strictly narrower than its `BaseSeams` target clause.
`partSizing` feeds `flatInset`, `canvasMargins`, the `flatC3` bounded
conjunct, and the `flatC8b` transport; `nestResidual` feeds the `flatC3`
nesting conjunct via `R_memberFramesNestR_holds`; `disjointR` feeds `flatC2`;
`groupBoundary` feeds `flatC5`; the C8b residuals feed `flatC8b`; the step
hypotheses feed the step assemblers. Clauses with no finished region module
are carried as the clause itself, marked OPEN CLAUSE. -/
structure RegionSeams (exactIds : List String)
    (idSets : List (String × List String)) : Prop where
  /-- Executed-run sizing residual (`RegionFlatInset.lean`): open premise of
  `flatInsetB_layoutRIds_reindex`, `exactCanvasMarginsR`,
  `exactComponentPlacementR_of`, and `flatC8bB_layoutRIds`. Stated decoupled:
  for each sub-input, over every executed run at its reindexed sets. The
  coupled premise shapes of the flat theorems are instances of this. -/
  partSizing : ∀ (sub : Input) {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds (reindexRegionSets idSets sub) inp o
      res),
    R_PartSizingR execution
  /-- Narrow region-nest residual (`RegionMemberFramesNest.lean`): open
  premise discharged via `R_memberFramesNestR_holds` into the `flatC3`
  nesting conjunct, per sub-input. -/
  nestResidual : ∀ (sub : Input),
    R_RegionNestResidual exactIds (reindexRegionSets idSets sub)
  /-- Run-level separation residual (`RegionRunTruthProbes.lean`): open
  premise of `flatC2B_layoutRIds`. -/
  disjointR : componentRunR_positions_disjointR_fact
  /-- C5 group-boundary residual (`RegionC5Endpoints.lean`): open premise
  discharged via `flatC5B_layoutRIds_closed` with the closed tail/head
  lookups, per sub-input. -/
  groupBoundary : ∀ (sub : Input),
    R_GroupBoundaryR exactIds (reindexRegionSets idSets sub)
  /-- C8b core residual (`RegionFlatC8b.lean`): open premise of
  `flatC8bB_layoutRIds`, per sub-input. -/
  partFrameCores : ∀ (sub : Input),
    R_ExecutedPartFrameCoresB8 exactIds (reindexRegionSets idSets sub)
  /-- C8b fallback residual (`RegionFlatC8b.lean`): open premise of
  `flatC8bB_layoutRIds`, per sub-input. -/
  fallbackCaption : ∀ (sub : Input),
    R_FallbackCaptionClearB8 exactIds (reindexRegionSets idSets sub)
  /-- C8b title caption-fit residual (`RegionFlatC8b.lean`): open premise of
  the packed-transport closure inside `flatC8bB_layoutRIds`, per sub-input. -/
  titleCaptionFit : ∀ (sub : Input),
    R_ExactTitleCaptionFitB8 exactIds (reindexRegionSets idSets sub)
  /-- Region C6 geometry hypothesis consumed by `stepC6_layoutRIds`. -/
  stepC6Geometry : rsmC6Geometry exactIds idSets
  /-- Region C6 anchor hypothesis consumed by `stepC6_layoutRIds`. -/
  stepC6Anchors : rsmC6Anchors exactIds idSets
  /-- Region C7 geometry hypothesis consumed by `stepC7_layoutRIds`. -/
  stepC7Geometry : rsmC7Geometry exactIds idSets
  /-- Region C7 label-scopes residual consumed by `stepC7_layoutRIds`. -/
  stepC7Scopes : R_StepC7ScopesB exactIds idSets
  /-- Region C8a geometry hypothesis consumed by `stepC8a_layoutRIds`. -/
  stepC8aGeometry : rsmC8aGeometry exactIds idSets
  /-- Region C8a merged-anchors residual consumed by
  `stepC8aAncestry_layoutRIds`. -/
  stepC8aMergedAnchors : R_StepC8aMergedAnchorsB exactIds idSets
  /-- Region C8a group-isolation residual consumed by
  `stepC8aAncestry_layoutRIds`. -/
  stepC8aGroupIsolated : R_StepC8aGroupIsolatedB exactIds idSets
  /-- Region C8b geometry hypothesis consumed by `stepC8b_layoutRIds`. -/
  stepC8bGeometry : rsmC8bGeometry exactIds idSets
  /-- OPEN CLAUSE: no finished region module; the `flatC6` clause itself. -/
  flatC6 : FlatC6B (rsmBase exactIds idSets)
  /-- OPEN CLAUSE: no finished region module; the `flatC7` clause itself. -/
  flatC7 : FlatC7B (rsmBase exactIds idSets)
  /-- OPEN CLAUSE: no finished region module; the `flatC8a` clause itself. -/
  flatC8a : FlatC8aB (rsmBase exactIds idSets)
  /-- OPEN CLAUSE: no finished region module; the `labelRuns` clause itself. -/
  labelRuns :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LabelRunsClearExclusiveBoxes inp o res
  /-- OPEN CLAUSE: no finished region module; the `captions` clause itself. -/
  captions :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o → SceneCaptionBoxContainment inp o res
  /-- OPEN CLAUSE: no finished region module; the `fitClosed` clause itself. -/
  fitClosed : ExpandChildFitClosedB (rsmBase exactIds idSets)

/-- Region base seams at the reindexing base: every `BaseSeams` field filled
from the finished region theorems over the matching `RegionSeams` residual,
with the base-independent `frameClear`, `partsSep`, and `subInputC2` terms
copied from `exactBaseSeams`. Clauses with no finished region module are the
matching OPEN CLAUSE projections. -/
theorem regionBaseSeams {exactIds : List String}
    {idSets : List (String × List String)} (R : RegionSeams exactIds idSets) :
    BaseSeams (rsmBase exactIds idSets) where
  flatInset := flatInsetB_layoutRIds_reindex exactIds idSets
    (fun {s o' res'}
      (execution : SceneExecutionR exactIds (reindexRegionSets idSets s) s o'
        res') =>
      R.partSizing s execution)
  flatC3 := fun sub o' res' hwf hframed hok =>
    flatC3B_layoutRIds exactIds (reindexRegionSets idSets sub)
      (fun {inp o res} =>
        (exactComponentPlacementR_of (fun execution => R.partSizing sub execution)
          (R_memberFramesNestR_holds (R.nestResidual sub))
          R_parentInComponentR_holds :
          ExactComponentPlacementR exactIds (reindexRegionSets idSets sub) inp o
            res))
      sub o' res' hwf hframed hok
  flatC2 := fun sub o' res' hwf hok =>
    flatC2B_layoutRIds exactIds (reindexRegionSets idSets sub) R.disjointR
      sub o' res' hwf hok
  flatC4 := fun sub o' res' hok route hroute =>
    flatC4B_layoutRIds_closed exactIds (reindexRegionSets idSets sub)
      sub o' res' hok route hroute
  flatC5 := fun {sub o' res'} hwf hfp
    (hok : (rsmBase exactIds idSets) sub o' = .ok res') =>
    flatC5B_layoutRIds_closed exactIds (reindexRegionSets idSets sub)
      (R.groupBoundary sub) hwf hfp hok
  flatC6 := R.flatC6
  flatC7 := R.flatC7
  flatC8a := R.flatC8a
  flatC8b := fun sub o' res' hwf hfp hfit hok =>
    flatC8bB_layoutRIds exactIds (reindexRegionSets idSets sub)
      (R.partFrameCores sub) (R.fallbackCaption sub)
      (fun execution => R.partSizing sub execution) (R.titleCaptionFit sub)
      sub o' res' hwf hfp hfit hok
  canvasMargins := exactCanvasMarginsR exactIds idSets
    (fun {s o' res'}
      (execution : SceneExecutionR exactIds (reindexRegionSets idSets s) s o'
        res') =>
      R.partSizing s execution)
  frameClear := fun _inp _o _res hwf hfp =>
    frameClearanceSeam_holds
      (bracketInsidePremises
        (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
        (fun execution => titleCopySpanClearStrict_executed hwf hfp execution))
  partsSep := fun _ _ _ => labelsC7_partsSeparated
  labelRuns := R.labelRuns
  captions := R.captions
  subInputC2 := subInputWellFormedC2
  subInputB := subInputWellFormedB_layoutRIds exactIds idSets
  fitClosed := R.fitClosed
  stepC2 := stepC2_layoutRIds exactIds idSets
  stepC6 := stepC6_layoutRIds exactIds idSets R.stepC6Geometry R.stepC6Anchors
  stepC7 := stepC7_layoutRIds exactIds idSets R.stepC7Geometry R.stepC7Scopes
  stepC8a := stepC8a_layoutRIds exactIds idSets R.stepC8aGeometry
    (stepC8aAncestry_layoutRIds exactIds idSets R.stepC8aMergedAnchors
      R.stepC8aGroupIsolated)
  stepC8b := stepC8b_layoutRIds exactIds idSets R.stepC8bGeometry

end PipelineImpl
end Layered
end Elegant

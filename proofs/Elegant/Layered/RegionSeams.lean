import Elegant.Layered.RegionFlatInset
import Elegant.Layered.RegionPartSizing
import Elegant.Layered.RegionPartSizingClosed
import Elegant.Layered.RegionNotesFitClosure
import Elegant.Layered.RegionCanvasMargins
import Elegant.Layered.RegionFlatC3
import Elegant.Layered.RegionParentInComponent
import Elegant.Layered.RegionMemberFramesNest
import Elegant.Layered.RegionPositionsDisjoint
import Elegant.Layered.RegionCrossCoordsMetadata
import Elegant.Layered.RegionC5ActiveBoundary
import Elegant.Layered.RegionC5Endpoints
import Elegant.Layered.RegionC5NonexactLoopTransport
import Elegant.Layered.RegionC6SelectedCutover
import Elegant.Layered.RegionC7SelectedForwardSameRank
import Elegant.Layered.RegionC7EqualRankCaption
import Elegant.Layered.RegionFlatC8a
import Elegant.Layered.RegionC8aGroupPlainCutover
import Elegant.Layered.RegionActiveFrameLabels
import Elegant.Layered.RegionForeignPartCaptions
import Elegant.Layered.RegionActiveOwnCaption
import Elegant.Layered.RegionActiveDescendantCaption
import Elegant.Layered.RegionFallbackAncestorSelectedStrict
import Elegant.Layered.RegionTitleCaptionFit
import Elegant.Layered.RegionSubInputStepC2
import Elegant.Layered.RegionStepAssemblers
import Elegant.Layered.RegionFrameStepClosure
import Elegant.Layered.FamilyAssemblyB
import Elegant.Layered.RegionPipeline
import Elegant.Layered.FrameClearanceSeam
import Elegant.Layered.BracketInsidePremisesProof
import Elegant.Layered.DummyNestedMarkerProof
import Elegant.Layered.TitleCopySpanProof
import Elegant.Layered.PartSeparation
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.RegionC8aGroupsCutover
import Elegant.Layered.RegionForwardChildCutover

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
inset theorem is stated over. -/

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
`nestResidual` feeds the `flatC3` nesting conjunct via
`R_memberFramesNestR_holds`;
The C8b residuals feed `flatC8b`; the step hypotheses feed the step assemblers. -/
structure RegionSeams (exactIds : List String)
    (idSets : List (String × List String)) : Prop where
  /-- Narrow region-nest residual (`RegionMemberFramesNest.lean`): open
  premise discharged via `R_memberFramesNestR_holds` into the `flatC3`
  nesting conjunct, per sub-input. -/
  nestResidual : ∀ (sub : Input),
    R_RegionNestResidual exactIds (reindexRegionSets idSets sub)
  /-- Same-part C8b clearance for the remaining route cases and captions in
  inactive chosen parts. -/
  partFrameCores : ∀ (sub : Input),
    R_ExecutedPartFrameCoresB8ActiveDescendantCaptionRemainder exactIds
      (reindexRegionSets idSets sub)
  /-- Region C6 geometry hypothesis consumed by `stepC6_layoutRIds`. -/
  stepC6Geometry : rsmC6Geometry exactIds idSets
  /-- Region C6 anchor hypothesis consumed by `stepC6_layoutRIds`. -/
  stepC6Anchors : rsmC6Anchors exactIds idSets
  /-- Region C7 geometry hypothesis consumed by `stepC7_layoutRIds`. -/
  stepC7Geometry : rsmC7Geometry exactIds idSets
  /-- Region C7 label-scopes residual consumed by `stepC7_layoutRIds`. -/
  stepC7Scopes : R_StepC7ScopesB exactIds idSets
  /-- Region C8b geometry hypothesis consumed by `stepC8b_layoutRIds`. -/
  stepC8bGeometry : rsmC8bGeometry exactIds idSets
  /-- C6 for remaining fallback bottom brackets, active forward pieces and
  reversed endpoint stubs, and unsettled emitted loop pairs. -/
  flatC6SelectedResidual : RegionOrdinaryC6.ReindexedSelectedClearanceResidual exactIds idSets
  /-- C7 clearance for selected self-loops against witnessed plain targets outside the settled cases. -/
  flatC7SelectedClearance :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
      Elegant.Layered.PartsSeparated inp o res → LabelRunsClearExclusiveBoxes inp o res →
      SceneCaptionBoxContainment inp o res →
      layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
      ∀ execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res,
        R7_SelectedUnsettledLoopClearance execution

/-- Region base seams at the reindexing base. The `labelRuns` and `captions`
clauses quantify ordinary `SceneExecution`, so they reuse the layered proofs.
Region-executed C7 clearance retains its own residuals. -/
theorem regionBaseSeams {exactIds : List String}
    {idSets : List (String × List String)} (R : RegionSeams exactIds idSets) :
    BaseSeams (rsmBase exactIds idSets) where
  flatInset := flatInsetB_layoutRIds_reindex exactIds idSets
    (fun s => R_partSizingRResidual_holds exactIds (reindexRegionSets idSets s))
  flatC3 := fun sub o' res' hwf hframed hok =>
    flatC3B_layoutRIds exactIds (reindexRegionSets idSets sub)
      (exactComponentPlacementR_of
        (R_partSizingRResidual_holds exactIds (reindexRegionSets idSets sub))
        (R_memberFramesNestR_holds (R.nestResidual sub))
        R_parentInComponentR_holds)
      sub o' res' hwf hframed hok
  flatC2 := fun sub o' res' hwf hok =>
    flatC2B_layoutRIds_closed exactIds (reindexRegionSets idSets sub)
      sub o' res' hwf hok
  flatC4 := fun sub o' res' hok route hroute =>
    flatC4B_layoutRIds_closed exactIds (reindexRegionSets idSets sub)
      sub o' res' hok route hroute
  flatC5 := fun {sub o' res'} hwf hfp
    (hok : (rsmBase exactIds idSets) sub o' = .ok res') =>
    flatC5B_layoutRIds_activeOnly exactIds (reindexRegionSets idSets sub)
      (r_activeBoundaryR_closed exactIds (reindexRegionSets idSets sub)) hwf hfp hok
  flatC6 := (flatC6B_layoutRIds_reindex_iff_selectedClearance exactIds idSets).mpr
    (RegionOrdinaryC6.reindexedSelectedClearance_of_residual R.flatC6SelectedResidual)
  flatC7 := by
    apply (flatC7B_layoutRIds_reindex_iff_captionActive exactIds idSets).mpr
    intro inp o res hwf hfp hfit hsep hruns hcap hok execution
    refine ⟨(r7Selected_routeWithPlainTarget_iff_unsettledLoops execution).mpr
      (R.flatC7SelectedClearance inp o res hwf hfp hfit hsep hruns hcap hok execution), ?_⟩
    exact (r7Caption_activeResidual_iff_activeEqualRank execution hwf hfp).mpr
      (r7Caption_activeEqualRank_holds execution hwf hfp)
  flatC8a := flatC8aB_layoutRIds_reindex_closed exactIds idSets
  flatC8b := fun sub o' res' hwf hfp hfit hok =>
    flatC8bB_layoutRIds_activeDescendantCaptionRemainder exactIds (reindexRegionSets idSets sub)
      (R.partFrameCores sub)
      (R_fallbackCaptionClearB8W_selected_closed exactIds (reindexRegionSets idSets sub))
      (R_partSizingRResidual_holds exactIds (reindexRegionSets idSets sub))
      (R_exactTitleCaptionFitB8_holds exactIds (reindexRegionSets idSets sub))
      sub o' res' hwf hfp hfit hok
  canvasMargins := exactCanvasMarginsR exactIds idSets
  frameClear := fun _inp _o _res hwf hfp =>
    frameClearanceSeam_holds
      (bracketInsidePremises
        (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
        (fun execution => titleCopySpanClearStrict_executed hwf hfp execution))
  partsSep := fun _ _ _ => labelsC7_partsSeparated
  labelRuns := baseSeams_of_layered.labelRuns
  captions := baseSeams_of_layered.captions
  subInputC2 := subInputWellFormedC2
  subInputB := subInputWellFormedB_layoutRIds exactIds idSets
  fitClosed := expandChildFitClosedB_region exactIds idSets
  stepC2 := stepC2_layoutRIds exactIds idSets
  stepC6 := stepC6_layoutRIds exactIds idSets R.stepC6Geometry R.stepC6Anchors
  stepC7 := stepC7_layoutRIds exactIds idSets R.stepC7Geometry R.stepC7Scopes
  stepC8a := stepC8a_layoutRIds exactIds idSets
    (r_stepC8aGeometry_closed exactIds idSets)
    (stepC8aAncestry_layoutRIds exactIds idSets
      (r_stepC8aMergedAnchors_closed exactIds idSets)
      (r_stepC8aGroupIsolated_closed exactIds idSets))
  stepC8b := stepC8b_layoutRIds exactIds idSets R.stepC8bGeometry

end PipelineImpl
end Layered
end Elegant

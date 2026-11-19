import Elegant.Layered.FramedParentsSub
import Elegant.Layered.RecursiveC6
import Elegant.Layered.RecursiveC7
import Elegant.Layered.RecursiveC78
import Elegant.Layered.FrameClearanceSeam
import Elegant.Layered.OrthogonalityFacts
import Elegant.Layered.FamilyC5
import Elegant.Layered.FlatC2
import Elegant.Layered.OutputParentContained
import Elegant.Layered.LabelsC7
import Elegant.Layered.LabelsC8b
import Elegant.Layered.PartSeparation
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.FamilyC5Measured
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.ExpandChildC6StepFacts
import Elegant.Layered.BracketInsidePremisesProof
import Elegant.Layered.FlatGroupEndpointsProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.RunLocalLabelClearanceProof
import Elegant.Layered.GroupTailPortProof
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.GroupAnchorFactsProof
import Elegant.Layered.TitleCopySpanProof
import Elegant.Layered.DummyNestedMarkerProof
import Elegant.Layered.ForeignBorderAnchorsProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.ExpandChildLabelFactsProof
import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint
import Elegant.Layered.MergedRouteIdsProof
import Elegant.Layered.RouteLabelsPlacedProof
import Elegant.Layered.BottomSyntheticRankProof
import Elegant.Layered.DummyChainRankProof
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.ExclusiveKeyOutsideCgPathsProof
import Elegant.Layered.CaptionsSeamProof
import Elegant.Layered.CaptionCrossPartProof
import Elegant.Layered.FlatC6ClosedProof
import Elegant.Layered.FrameLabelsProof
import ElegantGeometry.Validator
set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The per-expansion step fact of clause `Step`, quantified over the
`expandChild` calls `layoutRecursive` performs, with the measurements the
recursion ran the call with. -/
abbrev RecursiveStepFacts
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    Step P inp o group titleHeight parent child res

/-- Every fact the layered family validity theorem still takes as a premise.
Remaining fields: `partFrameWitness`, `loopRectTopReal`, `loopRectFixedReal`,
`loopRectTitleReal`, `loopRectBottomReal`, `loopRectRangeDegReal`,
`loopFootprintTopSeparation`, `loopFootprintBeyondProper`,
`runLocalLoopFootprint`, `titleExclusiveSamePart`, `foreignClusterRankSpans`,
`foreignBorderChainXAligned`, `bracketMarkersAtRank`,
`executedPartFrameCores`, `fallbackOwnerFrameClear`, `stepC6Geometry`,
`stepC6Anchors`, `stepC7Geometry`, `stepC8aGeometry`, `stepC8bGeometry`,
`stepC8aAncestry`.  Each field is a named
OPEN statement about the executed pipeline; a field leaves this structure when
its discharge theorem lands.  The refuted `GroupAttach`, `GroupAnchors`, and
universal nonempty-id statements were replaced by the four group endpoint
fields and a premise on the input.  The sub-input well-formedness seams are
discharged (`SubInputWellFormedFacts.lean`), as are the group-rank,
route-label, dummy-row, title-copy, border-layer-order, side-marker,
label-owner, and label-scope seams (`DummyChainRankProof.lean`,
`BottomSyntheticRankProof.lean`, `RouteLabelsPlacedProof.lean`,
`DummyNestedMarkerProof.lean`, `TitleCopySpanProof.lean`,
`ForeignBorderAnchorsProof.lean`, `SideMarkerPathsProof.lean`,
`ExpandChildLabelFactsProof.lean`, `MergedRouteIdsProof.lean`), the
forward/reversed run-local separations and the loop separation modulo its
footprint (`RunLocalSeparationsProof.lean`), the exclusive-box run bridge
(`ExclusiveKeyOutsideCgPathsProof.lean`), and the cross-part title clearance,
which the `captions` field now takes narrowed to `titleExclusiveSamePart`
via `sceneCaptionBoxContainment_of_fit` (`CaptionsSeamProof.lean`,
`CaptionCrossPartProof.lean`).  The old `flatC6` field is narrowed to its
eight residuals, closed by `flatC6_closed` (`FlatC6ClosedProof.lean`), and
the old `frameLabels` field is narrowed to `executedPartFrameCores` and
`fallbackOwnerFrameClear`, closed by `frameLabels_executed`
(`FrameLabelsProof.lean`).  `stepC6Anchors` and `stepC8aAncestry` are kept:
`stepC6Anchors_holds` and `stepC8aAncestry_holds`
(`ExpandChildAncestryProof.lean`) have exactly these field types, but that
file imports `FamilyAssembly` for `RecursiveStepFacts`, so using them here
would be an import cycle. -/
structure LayeredSeams : Prop where
  partFrameWitness : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    PartFrameWitness inp o res
  loopRectTopReal : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    LoopRectTopReal inp o res
  loopRectFixedReal : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    LoopRectFixedReal inp o res
  loopRectTitleReal : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    LoopRectTitleReal inp o res
  loopRectBottomReal : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    LoopRectBottomReal inp o res
  loopRectRangeDegReal : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    LoopRectRangeDegReal inp o res
  loopFootprintTopSeparation : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    LoopFootprintTopSeparation inp o res
  loopFootprintBeyondProper : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    LoopFootprintBeyondProper inp o res
  runLocalLoopFootprint : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    RunLocalLoopFootprint inp o res
  titleExclusiveSamePart : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    TitleExclusiveSamePart inp o res
  foreignClusterRankSpans : ForeignClusterRankSpans
  foreignBorderChainXAligned : ForeignBorderChainXAligned
  bracketMarkersAtRank : BracketMarkersAtRank
  executedPartFrameCores : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ (execution : SceneExecution inp o res), ExecutedPartFrameCores execution
  fallbackOwnerFrameClear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ (execution : SceneExecution inp o res),
      Elegant.Layered.FallbackOwnerFrameClear execution
  stepC6Geometry : RecursiveStepFacts ExpandChildC6Geometry
  stepC6Anchors : RecursiveStepFacts
    (fun _ _ _ group _ parent child res => ExpandChildC6Anchors group parent child res)
  stepC7Geometry : RecursiveStepFacts ExpandChildC7Geometry
  stepC8aGeometry : RecursiveStepFacts ExpandChildC8aGeometry
  stepC8bGeometry : RecursiveStepFacts ExpandChildC8bGeometry
  stepC8aAncestry : RecursiveStepFacts
    (fun _ _ _ group _ parent child res => ExpandChildC8aAncestry group parent child res)

/-- Layered family validity for an input with nonempty box ids, fixed-size room
for labeled boxes, and disjoint box route ids, modulo exactly the fields of
`LayeredSeams`.  `hids` is a premise on the input: `modelWellFormed` accepts an
empty box id, and the C2 merge of the recursion needs nonempty ids.  `layoutFamily`
runs the recursion on the same input, so `hfix` and `hdisj` carry over directly. -/
theorem layoutFamily_valid_of_seams (S : LayeredSeams) {inp : Input} {o : Options}
    {res : FamilyResult} (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (hfix : InputFixedFit inp o) (hdisj : BoxRouteIdsDisjoint inp)
    (h : layoutFamily inp o = .ok res) :
    HardConstraints res.scene.layoutDump := by
  obtain ⟨hwf, hrec⟩ := layoutFamily_success h
  have hfp := layoutFamily_framed_parents h
  have hflat2 : FlatC2 := fun inp o res hwf h => layout_c2 h hwf
  have hflat3 : FlatC3' := fun inp o res hwf hfp h => layout_c3 h hwf hfp
  have hflat7 : FlatC7 := fun inp o res hwf hfp hsep s1 s2 h =>
    layout_c7 hwf hfp hsep s1 s2 h
  have hframeLabels : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
      ∀ (execution : SceneExecution inp o res),
        LabelFramePackedClear execution.params inp o execution.lines execution.packedAcc ∧
          FallbackCaptionClear execution :=
    fun inp o res hwf hfp hfit execution =>
      frameLabels_executed execution hwf hfp hfit
        (S.executedPartFrameCores inp o res hwf hfp execution)
        (S.fallbackOwnerFrameClear inp o res hwf hfp execution)
  have hflat6 : FlatC6 :=
    flatC6_closed S.partFrameWitness S.loopRectTopReal S.loopRectFixedReal
      S.loopRectTitleReal S.loopRectBottomReal S.loopRectRangeDegReal
      S.loopFootprintTopSeparation S.loopFootprintBeyondProper
  have hflat8b : FlatC8b := fun inp o res hwf hfp hfit h =>
    layout_c8b h hwf (hframeLabels inp o res hwf hfp hfit)
  have hlabelRuns : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LabelRunsClearExclusiveBoxes inp o res := fun inp o res hwf hfp =>
    ⟨runLocalLabelClearance_holds hwf hfp
        (runLocalLoopSeparation inp o res (S.runLocalLoopFootprint inp o res))
        (runLocalForwardSeparation inp o res) (runLocalReversedSeparation inp o res),
      routeLabelDumpBridges hwf (labelBelongsToRun hwf routeLabelsPlaced)
        (exclusiveBoxInLabelRun' hwf hfp)⟩
  have hcaptions : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
      SceneCaptionBoxContainment inp o res := fun inp o res hwf hfp hfit =>
    sceneCaptionBoxContainment_of_fit hwf hfp hfit
      (S.titleExclusiveSamePart inp o res hwf hfp)
      (titleExclusiveCrossPart (inp := inp) (o := o) (res := res))
      (hframeLabels inp o res hwf hfp hfit)
  have hbracket : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      BracketInsidePremises inp o res := fun inp o res hwfInp hframedInp =>
    bracketInsidePremises
      (fun execution => dummyInsideProxyRowClear_executed' execution hwfInp hframedInp)
      (fun execution => titleCopySpanClearStrict_executed hwfInp hframedInp execution)
  have hstepC6 : RecursiveStepFacts ExpandChildC6Step :=
    expandChild_c6_step_of_geometry S.stepC6Geometry S.stepC6Anchors
  have hstepC7 : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true → BoxRouteIdsDisjoint inp →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7Step P inp o group titleHeight parent child res :=
    by
    intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hdisjoint hctx hparams
    intro frame tl dx dy hframe hdx hdy hwrap
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
      expandChild_c7_structure fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx
        (expandChild_label_owners fuel P inp o group titleLines titleHeight parent child res
          hexpand hframed hctx hparams)
        (expandChild_c7_label_scopes_of_disjoint hexpand hframed hctx hparams hdisjoint
          (S.stepC8aAncestry fuel P inp o group titleLines titleHeight parent child res
            hexpand hframed hctx hparams))
        frame tl dx dy hframe hdx hdy hwrap
    obtain ⟨g1, g2, g3, g4⟩ :=
      S.stepC7Geometry fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
    exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, g1, g2, g3, g4⟩
  have hstepC8a : RecursiveStepFacts ExpandChildC8aStep :=
    expandChild_c8a_step_of_geometry S.stepC8aGeometry
      (fun fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx
          hparams =>
        expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
          hexpand hframed hctx
          (S.stepC8aAncestry fuel P inp o group titleLines titleHeight parent child res
            hexpand hframed hctx hparams))
  have hstepC8b : RecursiveStepFacts ExpandChildC8bStep :=
    expandChild_c8b_step_of_geometry S.stepC8bGeometry
      (fun fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx
          hparams =>
        expandChild_c8b_structure fuel P inp o group titleLines titleHeight parent child res
          hexpand hframed hctx
          (expandChild_label_owners fuel P inp o group titleLines titleHeight parent child
            res hexpand hframed hctx hparams))
  have hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      FrameClearanceSeam inp o res := fun inp o res hwfInp hframedInp =>
    frameClearanceSeam_holds (hbracket inp o res hwfInp hframedInp)
  have hgeo2 := hgeo_of_recursion subInputWellFormedC2
  exact ⟨
    (layoutRecursive_c1_c3 subInputWellFormedC2 hflat3 (inp.boxes.length + 1) inp o res
      hwf hfp hrec).1,
    layoutRecursive_c2_of_flat hflat2 subInputWellFormedC2 hgeo2
      (inp.boxes.length + 1) inp o res hwf hids hrec,
    (layoutRecursive_c1_c3 subInputWellFormedC2 hflat3 (inp.boxes.length + 1) inp o res
      hwf hfp hrec).2,
    layoutFamily_c4 h,
    layoutFamily_c5_measured
      (flatGroupEndpoints groupTopSubtreeRankProper'
        (groupBottomBoundaryFacts_of_dummy bottomDummyRankLe) groupTailPortOnYs
        groupAnchorSelection)
      subInputWellFormed h,
    layoutRecursive_c6_of_flat hflat6 hclear subInputWellFormed hstepC6
      (inp.boxes.length + 1) inp o res hwf hfp hrec,
    layoutRecursive_c7_of_flat hflat7 (fun _ _ _ => labelsC7_partsSeparated) hlabelRuns
      hcaptions subInputWellFormed hstepC7
      (inp.boxes.length + 1) inp o res hwf hfp hfix hdisj hrec,
    layoutRecursive_c8a_of_flat
      (flatC8a_of_span_seams
        (foreignBorderSpansSeparated S.foreignClusterRankSpans foreignBorderLayerOrder'
          S.foreignBorderChainXAligned)
        (foreignNonGroupSpansClear S.bracketMarkersAtRank plainClearOfSideMarker'
          (sideMarkerSpanAligned' S.foreignBorderChainXAligned))
        hbracket)
      subInputsWellFormed hstepC8a
      (inp.boxes.length + 1) inp o res hwf hfp hrec,
    layoutRecursive_c8b_of_flat hflat8b subInputsWellFormed hstepC8b
      (inp.boxes.length + 1) inp o res hwf hfp hfix hrec⟩

end Elegant.Layered.PipelineImpl

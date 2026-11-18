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
Each field is a named OPEN statement about the executed pipeline; a field
leaves this structure when its discharge theorem lands.  No field is known to
be false: the refuted `GroupAttach`, `GroupAnchors`, and universal nonempty-id
statements were replaced by the four group endpoint fields and a premise on the input.  The
sub-input well-formedness seams are discharged (`SubInputWellFormedFacts.lean`). -/
structure LayeredSeams : Prop where
  groupTopRank : GroupTopSubtreeRankProper
  groupBottomBoundary : GroupBottomBoundaryFacts
  flatC6 : FlatC6
  dummyRowClear : ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecution inp o res),
    dummyInsideProxyRowClear execution.params execution.graph
  titleCopySpan : ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecution inp o res),
    titleCopySpanClearStrict execution.params execution.graph
  runLocalLoopSeparation : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    RunLocalLoopSeparation inp o res
  runLocalForwardSeparation : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    RunLocalForwardSeparation inp o res
  runLocalReversedSeparation : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    RunLocalReversedSeparation inp o res
  exclusiveBoxInLabelRun : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    ExclusiveBoxInLabelRun inp o res
  captions : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    SceneCaptionBoxContainment inp o res
  foreignClusterRankSpans : ForeignClusterRankSpans
  foreignBorderLayerOrder : ForeignBorderLayerOrder
  foreignBorderChainXAligned : ForeignBorderChainXAligned
  bracketMarkersAtRank : BracketMarkersAtRank
  plainClearOfSideMarker : PlainClearOfSideMarker
  sideMarkerSpanAligned : SideMarkerSpanAligned
  frameLabels : ∀ (inp : Input) (o : Options) (res : FamilyResult),
    ∀ (execution : SceneExecution inp o res),
      LabelFramePackedClear execution.params inp o execution.lines execution.packedAcc ∧
        FallbackCaptionClear execution
  stepC6Geometry : RecursiveStepFacts ExpandChildC6Geometry
  stepC6Anchors : RecursiveStepFacts
    (fun _ _ _ group _ parent child res => ExpandChildC6Anchors group parent child res)
  stepC7Geometry : RecursiveStepFacts ExpandChildC7Geometry
  stepC8aGeometry : RecursiveStepFacts ExpandChildC8aGeometry
  stepC8bGeometry : RecursiveStepFacts ExpandChildC8bGeometry
  stepC8aAncestry : RecursiveStepFacts
    (fun _ _ _ group _ parent child res => ExpandChildC8aAncestry group parent child res)
  stepLabelOwners : RecursiveStepFacts
    (fun _ inp _ _ _ parent child _ => ExpandChildLabelOwners inp parent child)
  stepC7LabelScopes : RecursiveStepFacts
    (fun P _ _ group _ parent child res => ExpandChildC7LabelScopes P group parent child res)

/-- Layered family validity for an input with nonempty box ids, modulo exactly
the fields of `LayeredSeams`.  `hids` is a premise on the input:
`modelWellFormed` accepts an empty box id, and the C2 merge of the recursion
needs nonempty ids. -/
theorem layoutFamily_valid_of_seams (S : LayeredSeams) {inp : Input} {o : Options}
    {res : FamilyResult} (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (h : layoutFamily inp o = .ok res) :
    HardConstraints res.scene.layoutDump := by
  obtain ⟨hwf, hrec⟩ := layoutFamily_success h
  have hfp := layoutFamily_framed_parents h
  have hflat2 : FlatC2 := fun inp o res hwf h => layout_c2 h hwf
  have hflat3 : FlatC3' := fun inp o res hwf hfp h => layout_c3 h hwf hfp
  have hflat7 : FlatC7 := fun inp o res hwf hfp hsep s1 s2 h =>
    layout_c7 hwf hfp hsep s1 s2 h
  have hflat8b : FlatC8b := fun inp o res hwf _ h =>
    layout_c8b h hwf (S.frameLabels inp o res)
  have hlabelRuns : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LabelRunsClearExclusiveBoxes inp o res := fun inp o res hwf hfp =>
    ⟨runLocalLabelClearance_holds hwf hfp (S.runLocalLoopSeparation inp o res)
        (S.runLocalForwardSeparation inp o res) (S.runLocalReversedSeparation inp o res),
      routeLabelDumpBridges hwf (labelBelongsToRun hwf) (S.exclusiveBoxInLabelRun inp o res)⟩
  have hbracket : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      BracketInsidePremises inp o res := fun inp o res =>
    bracketInsidePremises (S.dummyRowClear inp o res) (S.titleCopySpan inp o res)
  have hstepC6 : RecursiveStepFacts ExpandChildC6Step :=
    expandChild_c6_step_of_geometry S.stepC6Geometry S.stepC6Anchors
  have hstepC7 : RecursiveStepFacts ExpandChildC7Step :=
    expandChild_c7_step_of_geometry S.stepC7Geometry
      (fun fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx
          hparams =>
        expandChild_c7_structure fuel P inp o group titleLines titleHeight parent child res
          hexpand hframed hctx
          (S.stepLabelOwners fuel P inp o group titleLines titleHeight parent child res
            hexpand hframed hctx hparams)
          (S.stepC7LabelScopes fuel P inp o group titleLines titleHeight parent child res
            hexpand hframed hctx hparams))
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
          (S.stepLabelOwners fuel P inp o group titleLines titleHeight parent child res
            hexpand hframed hctx hparams))
  have hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      FrameClearanceSeam inp o res := fun inp o res =>
    frameClearanceSeam_holds (hbracket inp o res)
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
      (flatGroupEndpoints S.groupTopRank S.groupBottomBoundary groupTailPortOnYs
        groupAnchorSelection)
      subInputWellFormed h,
    layoutRecursive_c6_of_flat S.flatC6 hclear subInputWellFormed hstepC6
      (inp.boxes.length + 1) inp o res hwf hfp hrec,
    layoutRecursive_c7_of_flat hflat7 (fun _ _ _ => labelsC7_partsSeparated) hlabelRuns
      S.captions subInputWellFormed hstepC7
      (inp.boxes.length + 1) inp o res hwf hfp hrec,
    layoutRecursive_c8a_of_flat
      (flatC8a_of_span_seams
        (foreignBorderSpansSeparated S.foreignClusterRankSpans S.foreignBorderLayerOrder
          S.foreignBorderChainXAligned)
        (foreignNonGroupSpansClear S.bracketMarkersAtRank S.plainClearOfSideMarker
          S.sideMarkerSpanAligned)
        hbracket)
      subInputsWellFormed hstepC8a
      (inp.boxes.length + 1) inp o res hwf hfp hrec,
    layoutRecursive_c8b_of_flat hflat8b subInputsWellFormed hstepC8b
      (inp.boxes.length + 1) inp o res hwf hfp hrec⟩

end Elegant.Layered.PipelineImpl

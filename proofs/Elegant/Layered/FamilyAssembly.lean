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
import Elegant.Layered.ForeignMemberRankBoundsProof
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
import Elegant.Layered.RecursiveStepFacts
import Elegant.Layered.ExpandChildAncestryProof
import Elegant.Layered.RunLocalLoopFootprintProof
import Elegant.Layered.FlatC8aExecutedProof
import Elegant.Layered.FallbackOwnerFrameProof
import Elegant.Layered.FallbackOwnerStrictStepProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.ExpandChildC8aGeometryExecuted
import Elegant.Layered.LoopRectRealClosed
import Elegant.Layered.LoopRectRealQProof
import Elegant.Layered.TitleExclusiveSamePartProof
import Elegant.Layered.ForeignBorderChainXAlignedClosed
import Elegant.Layered.ForeignBorderEdgesNoncrossingProof
import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.ExpandChildFrameLiftResiduals
import Elegant.Layered.ExpandChildFrameLiftProof
import Elegant.Layered.ExpandChildParentRouteClearProof
import Elegant.Layered.ExpandChildParentFixedMissProof
import Elegant.Layered.ExpandChildCanvasFitProof
import Elegant.Layered.ExpandChildChildSceneProof
import Elegant.Layered.ExpandChildC7GeometryProof
import Elegant.Layered.ExpandChildTitleBandProof
import Elegant.Layered.ExpandChildC8GeometryProof
import Elegant.Layered.SelectFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RecursiveFit
import Elegant.Layered.RecursiveC1C3
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.PolylineBoxMiss
import Elegant.Layered.SceneBounds
import Elegant.Layered.Assembly
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.LoopRectResidualsProof
import Elegant.Layered.ExecutedPartFrameCoresClosed
import Elegant.Layered.ExpandChildParentFrameStrictProof
import Elegant.Layered.LoopRectTitleCopySepProof
import Elegant.Layered.SeamClosureGlue
import Elegant.Layered.LoopResGroupHullRightAncestorRanksProof
import Elegant.Layered.LoopResNeighborGapDisjCasesProof
import Elegant.Layered.LoopFootprintTopSeparationCondProof
import Elegant.Layered.LoopResGroupHullRightProof
import Elegant.Layered.LoopResNeighborGapGroupProof
import Elegant.Layered.LoopResNeighborGapProof
import Elegant.Layered.LoopResNeighborDisjointProof
import Elegant.Layered.ExpandChildParentFixedForeignProof
import Elegant.Layered.FamilyStepFacts
set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl
 /-- Every fact the layered family validity theorem still takes as a premise.
 Remaining fields: `foreignBorderDivergeStable`,
 `parentRouteAttachedClear`, `parentFrameStrict`.  Each field is a named
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
 `CaptionCrossPartProof.lean`).  The old `partFrameWitness` field is deleted:
 `flatC6_closed_nowit` (`SeamClosureGlue.lean`) replays `flatC6_closed`
 (`FlatC6ClosedProof.lean`) with `partPositiveContent_holds`
 (`PartPositiveContentProof.lean`); `routePartShelfPositive_holds` feeds the
 shelf bridge.  The old `loopFootprintTopSeparation` field is deleted:
 `loopFootprintTopSeparation_closed`
 (`LoopFootprintTopSeparationCondProof.lean`) derives it from
 `foreignBorderChainXAligned'` of `foreignBorderDivergeStable` and the closed
 `beyondProper_closed` (`SeamClosureGlue.lean`, from
 `loopFootprintBeyondProper_closed` over `topSliverMarkerReady_of_span` of the
 proved `topSliverSpanCovered_holds`).  The old `loopFootprintBeyondProper`
 field is deleted with it.  The old `flatC6` field is narrowed to its
 eight residuals, closed by `flatC6_closed_nowit`, and
 the old `frameLabels` field is closed outright by
 `executedPartFrameCores_closed` (`ExecutedPartFrameCoresClosed.lean`) via
 `frameLabels_executed` (`FrameLabelsProof.lean`) over the closed loop covers:
 `loopHullRightCover_closed` (`LoopResGroupHullRightProof.lean`) from
 `loopResGroupHullRightWitness_closed'`
 (`LoopResGroupHullRightAncestorRanksProof.lean`), and
 `loopHullRightNeighborCover_Disj_holds`
 (`LoopResNeighborDisjointProof.lean`) fed by
 `neighborCover_of_disjoint_closed` (`SeamClosureGlue.lean`), whose
 `loopResNeighborGapDisj_closed` routes the grouped off-rank case through
 `loopResNeighborGapDisj_groupedOffRank_closed`
 (`LoopResOffRankParentChainProof.lean`) with no chain premise, together with
 the proved `loopResNeighborGapGroupTopDisj_holds`
 (`LoopResNeighborGapDisjCasesProof.lean`, over `foreignBorderChainXAligned'`
 of `foreignBorderDivergeStable` and the closed `foreignBorderLayerOrder'`)
 and the proved `neighborGapBottomOwnerDisj_holds` (`SeamClosureGlue.lean`).
 The `loopNeighborOffRankChain` seam field is deleted: the parent-chain
 residual `LoopResOffRankParentChain` is no longer needed.  The loop covers feed
 `fallbackOwnerFrameClear_executed` (`FallbackOwnerFrameProof.lean`), itself over
 `flatC8a_executed` (`FlatC8aExecutedProof.lean`) and
 `fallbackOwnerStrictStep_executed` (`FallbackOwnerStrictStepProof.lean`).  The
 `bracketMarkersAtRank` field is proved outright by `bracketMarkersAtRank'`
 (`SideMarkerTopInCandidateProof.lean`).  The `foreignClusterRankSpans` field is proved
 outright by `foreignClusterRankSpans'`, composing `foreignRankPairAnchors'`
 and `foreignMemberRankBounds` (`ForeignMemberRankBoundsProof.lean`).  The
 `stepC8aGeometry` field is proved outright by `stepC8aGeometry_holds`
 (`ExpandChildC8aGeometryExecuted.lean`).  The `stepC6Anchors` and `stepC8aAncestry` fields
 are discharged by `stepC6Anchors_holds` and `stepC8aAncestry_holds`
(`RecursiveStepFacts.lean`).  The `runLocalLoopFootprint` fact is derived
by `runLocalLoopFootprint_executed` (`RunLocalLoopFootprintProof.lean`) from
the closed `loopFootprintTopSeparation_closed` and the closed
`beyondProper_closed`.  The `loopRectTopForeign` field is discharged by `loopRectTopReal_closed` (`LoopRectResidualsProof.lean`).  The old title-copy field is closed by `loopRectTitleCopy_closed` (`LoopRectTitleCopySepProof.lean`).  The old `parentFixedDisjointGroup` field is deleted: its false universal form is replaced by `parentFixedForeign_narrow_holds` (`ExpandChildParentFixedForeignProof.lean`), applied only to fixed `g` with a parent frame via `parentFixedDisjointGroup_of_parentC8a` (`ExpandChildParentFixedMissProof.lean`) over the flat C8a clause and `stepC6_frame_pos`.  The old `parentStrictMissGroup` field is narrowed to `parentRouteAttachedClear`, closed with the frame half from the fuel-sliced frame lift (`sliced_frame_lift`, fed by strict miss below the call fuel) and the attached half verbatim, via `parentStrictMissGroup_of_frame_attached` closed by fuel induction (`strictMiss_restricted_closed`). -/
structure LayeredSeams : Prop where
  foreignBorderDivergeStable : ForeignBorderDivergeStable
  parentRouteAttachedClear : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → ExpandChildParentRouteAttachedClear group parent
  parentFrameStrict : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → ExpandChildParentFrameStrict group parent
 /-- Local copy of the private lemma in `ExpandChildC6GeometryClosed.lean`:
 the parent sub-input is well-formed. -/
 private theorem parentInput_wellFormed
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res) :
     WellFormed (inputModel (parentSubInput inp group P titleLines child) o) := by
   exact inputModel_wellFormed_fixed_congr _ _ _
     (selectInput_wellFormed inp o
       (fun box => !Compound.inside inp.boxes group.id box.id) "" hctx.1
       (fun c hc hkept => keepOutside_close (group := group.id)
         (inputFacts_of_wellFormed hctx.1) hc hkept) o)

 /-- Local copy of the private lemma in `ExpandChildC6GeometryClosed.lean`:
 the parent sub-input is framed. -/
 private theorem parentInput_framed
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res) :
     framedParents (parentSubInput inp group P titleLines child) = true := by
   exact framedParents_selectInput_outside_append inp o group hctx.1 hframed
     _ child.scene child.itemArea

 /-- Local copy of the private lemma in `ExpandChildC6GeometryExecuted.lean`. -/
 private theorem stepC6_frame_id_eq {group : ModelBox} {parent : FamilyResult}
     {frame : Box}
     (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
     frame.id = group.id := by
   simpa using List.find?_some hframe

 /-- Local copy of the private lemma in `ExpandChildParentFrameDirect.lean`. -/
 private theorem frame_id_eq {group : ModelBox} {parent : FamilyResult}
     {frame : Box}
     (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
     frame.id = group.id := by
   simpa using List.find?_some hframe

 /-- Local copy of the private lemma in `ExpandChildC8GeometryProof.lean`. -/
 private theorem strictInside_contained {outer inner : Rect}
     (h : outer.StrictInside inner) : outer.Contained inner := by
   simp only [Rect.StrictInside, Rect.Contained] at h ⊢
   omega

 /-- Local copy of the private lemma in `ExpandChildC8GeometryProof.lean`. -/
 private theorem strictInside_of_strictInside_contained {a b c : Rect}
     (hab : a.StrictInside b) (hbc : b.Contained c) : a.StrictInside c := by
   simp only [Rect.StrictInside, Rect.Contained] at *
   omega

 /-- Local copy of the private lemma in `ExpandChildC8GeometryProof.lean`. -/
 private theorem parent_scene_box_ids_nodup
     (fuel : Nat) (P : Params) (inp : Input) (o : Options)
     (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
     (parent child res : FamilyResult)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res) :
     (parent.scene.boxes.map (·.id)).Nodup := by
   obtain ⟨hwf, _hgroup, _hpb, _hchild, hparent, _he⟩ := hctx
   have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
   have hcov : RoutesCovered (parentSubInput inp group P titleLines child) :=
     selectInput_routesCovered inp
       (fun box => !Compound.inside inp.boxes group.id box.id) ""
   have hids := layoutRecursive_ids (fun _ _ _ h => layout_ids h) fuel
     (parentSubInput inp group P titleLines child) o parent hcov hparent
   rw [hids.1]
   show ((selectInput inp
     (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
       (·.id)).Nodup
   rw [selectInput_box_ids]
   exact hboxIds.sublist
     (List.Sublist.map (fun b : ModelBox => b.id) List.filter_sublist)

 /-- Local copy of the private theorem in `ExpandChildC6GeometryClosed.lean`:
 the C8a step of every expansion from the globally proved geometry. -/
 private theorem c8aStep_global :
     ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
     (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
     expandChild P inp o group titleHeight parent child = .ok res →
     framedParents inp = true →
     ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
     ExpandChildCallParams P inp o group titleLines titleHeight →
     ExpandChildC8aStep P inp o group titleHeight parent child res := by
   intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
   intro frame tl dx dy hframe hdx hdy hwrap
   obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
     expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
       hexpand hframed hctx
       (stepC8aAncestry_holds fuel P inp o group titleLines titleHeight parent child res
         hexpand hframed hctx hparams)
       frame tl dx dy hframe hdx hdy hwrap
   have hg := stepC8aGeometry_holds fuel P inp o group titleLines titleHeight parent child res
       hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
   exact ⟨s1, s2, s3, s4, s5, s6, hg, s7, s8⟩

 /-- Local copy of the private theorem in `ExpandChildC6GeometryClosed.lean`:
 the parent scene C8a from the flat clause. -/
 private theorem c8aParent_of_flat (hflat8a : FlatC8a) :
     ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
     (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
     expandChild P inp o group titleHeight parent child = .ok res →
     framedParents inp = true →
     ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
     ExpandChildCallParams P inp o group titleLines titleHeight →
     Validator.C8a parent.scene.layoutDump := by
   intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
   have hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent :=
     hctx.2.2.2.2.1
   exact layoutRecursive_c8a_of_flat hflat8a subInputsWellFormed c8aStep_global fuel
     (parentSubInput inp group P titleLines child) o parent
     (parentInput_wellFormed hctx) (parentInput_framed hframed hctx) hparent

/-- Local copy of the private theorem in `ExpandChildC6GeometryExecuted.lean`:
frame positivity for an executed call. -/
 private theorem stepC6_frame_pos
     (fuel : Nat) (P : Params) (inp : Input) (o : Options)
     (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
     (parent child res : FamilyResult)
     (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
     ∀ (frame : Box),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       0 < frame.rect.w ∧ 0 < frame.rect.h := by
   intro frame hframe
   have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
   have hheightEq : titleHeight = (max 1 titleLines.length : Int) * P.lineH :=
     hparams.2.1
   have hwrapCtx : ExpandChildTitleWrapped P inp o group titleLines := hparams.2.2
   have hchild : layoutRecursive fuel (childSubInput inp group)
       (childSubOptions o group) = .ok child := hctx.2.2.2.1
   have htw : 0 ≤ titleLines.foldl (fun width line => max width line.width) 0 := by
     suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
         0 ≤ ls.foldl (fun width line => max width line.width) acc by
       exact key titleLines 0 (by omega)
     intro ls acc hac
     induction ls generalizing acc with
     | nil => simpa using hac
     | cons line ls ih =>
       simp only [List.foldl_cons]
       exact ih _ (Int.le_trans hac (Int.le_max_left _ _))
   have hth : 0 ≤ titleHeight := by
     rw [hheightEq]
     exact Int.mul_nonneg (by omega)
       (Int.le_of_lt (callParams_lineH_pos hP))
   have hpad : 0 < P.clusterPad := callParams_clusterPad_pos hP
   have hcm := layoutRecursive_canvas_margins fuel hchild
   have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
     rw [checkedParams_canvasMargin hP]
     exact hcm.1
   have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
     rw [checkedParams_canvasMargin hP]
     exact hcm.2
   have hposS : 0 < (childFrameSize group.direction P.clusterPad
       (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
       ⟨child.scene.canvas.w - 2 * P.canvasMargin,
         child.scene.canvas.h - 2 * P.canvasMargin⟩).w ∧
       0 < (childFrameSize group.direction P.clusterPad
       (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
       ⟨child.scene.canvas.w - 2 * P.canvasMargin,
         child.scene.canvas.h - 2 * P.canvasMargin⟩).h := by
     unfold childFrameSize
     split <;> refine ⟨?_, ?_⟩ <;> dsimp only <;> omega
   obtain ⟨hw, hh⟩ := expandChild_frame_size_bounds fuel P inp o group titleLines
     titleHeight parent child res hexpand hframed hctx hparams frame titleLines
     hframe hwrapCtx
   omega

/-- The wide fixed-disjoint wrapper from the narrow foreign-chain residual:
the parent C8a clause comes from the flat clause, positivity from the executed
call, via `parentFixedDisjointGroup_of_parentC8a`. -/
private theorem fixedDisjoint_of_foreign
    (hflat8a : FlatC8a)
    (hforeign : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
      (g : ModelBox),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      (∃ _entry : String × Size,
        inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry) →
      g.id ∉ parent.scene.layoutDump.ancestors group.id) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
    (g : ModelBox) (gFrame frame : Box),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    (∃ entry : String × Size,
      inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry) →
    parent.scene.boxes.find? (fun box => box.id == g.id) = some gFrame →
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ExpandChildParentFixedDisjointGroup frame gFrame := by
  intro fuel P inp o group titleLines titleHeight parent child res g gFrame frame
    hexpand hframed hctx hparams hg hgFrame hframe
  exact parentFixedDisjointGroup_of_parentC8a fuel P inp o group titleLines titleHeight
    parent child res g gFrame frame hexpand hframed hctx hparams hg hgFrame hframe
    (c8aParent_of_flat hflat8a fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams)
    (stepC6_frame_pos fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams frame hframe)
    (hforeign fuel P inp o group titleLines titleHeight parent child res g
      hexpand hframed hctx hparams hg)

/-- Fuel-sliced copy of `layoutRecursive_frame_clear`
(`ExpandChildFrameLiftProof.lean`): the cross facts are only ever consumed
below the application fuel (the `hstep` sits at the predecessor), so the copy
takes them sliced to `m < F_top` and concludes below-or-at `F_top`. The
zero case is the flat clause; no cross facts are needed there. -/
private theorem sliced_frame_lift
    (F_top : Nat)
    (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      FrameClearanceSeam inp o res)
    (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ExclusiveRunNodeDecl inp o res)
    (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RunRouteEndpointIdsScoped inp o res)
    (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RoutePartShelfPositive inp o res)
    (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate execution.graph comp candidate) run
        execution.measured v)
    (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b)
    (hsub : SubInputWellFormed)
    (hchildCross : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildChildRouteParentFrame fuel P inp o group titleLines titleHeight
        parent child res)
    (hparentCross : ∀ (m : Nat), m < F_top → ∀ (P : Params) (inp : Input) (o : Options)
      (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentRouteChildFrame m P inp o group titleLines titleHeight parent child res) :
    ∀ (fuel : Nat), fuel ≤ F_top → ∀ (inp : Input) (o : Options) (g : ModelBox)
      (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      (∃ entry : String × Size,
        inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry) →
      layoutRecursive fuel inp o = .ok res →
      ∀ (frame : Box),
      res.scene.boxes.find? (fun box => box.id == g.id) = some frame →
      ∀ r ∈ res.scene.routes, r.fromId ≠ g.id → r.toId ≠ g.id →
        g.id ∉ LayoutDump.routeScope res.scene.layoutDump r →
        ¬ Polyline.hitsRect r.points frame.rect := by
  intro fuel
  induction fuel with
  | zero =>
      intro hle inp o g res hwf hframed hfixed h
      intro frame hfind r hr hfrom hto hscope
      exact frame_clear_of_flat hclear hnodeDecl hscoped hpos hloopRes hloopSep
        hwf hframed hfixed h hfind hr hfrom hto hscope
  | succ n ih =>
      intro hle inp o g res hwf hframed hfixed h
      have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
      rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
        ⟨group, P, metric, child, titleLines, parent, hg, hP, hm,
          hchild, hwrap, hparentAt, hexpandAt⟩
      · intro frame hfind r hr hfrom hto hscope
        exact frame_clear_of_flat hclear hnodeDecl hscoped hpos hloopRes hloopSep
          hwf hframed hfixed hlayout hfind hr hfrom hto hscope
      · obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
          hsub n inp o group P metric titleLines child parent
            hwf hframed hP hm hwrap hchild hparentAt
        have hctx : ExpandChildCallContext n P inp o group titleLines _
            parent child res :=
          ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
        have hparams : ExpandChildCallParams P inp o group titleLines _ :=
          ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
        obtain ⟨entry, hentry⟩ := hfixed
        have hfixedChild : ∃ entry : String × Size,
            (childSubInput inp group).fixedSizes.find?
              (fun fixed => fixed.1 == g.id) = some entry :=
          ⟨entry, hentry⟩
        have hfixedParent : ∃ entry : String × Size,
            (parentSubInput inp group P titleLines child).fixedSizes.find?
              (fun fixed => fixed.1 == g.id) = some entry := by
          refine ⟨entry, ?_⟩
          have hfix : (parentSubInput inp group P titleLines child).fixedSizes =
              inp.fixedSizes ++
                [(group.id, childFrameSize group.direction P.clusterPad
                  (titleLines.foldl (fun width line => max width line.width) 0)
                  ((max 1 titleLines.length : Int) * P.lineH)
                  ⟨child.scene.canvas.w - 2 * P.canvasMargin,
                    child.scene.canvas.h - 2 * P.canvasMargin⟩)] := rfl
          rw [hfix, List.find?_append, hentry]
          rfl
        have hChildIH := ih (by omega : n ≤ F_top) (childSubInput inp group)
          (childSubOptions o group) g child
          hwfChild hframedChild hfixedChild hchild
        have hParentIH := ih (by omega : n ≤ F_top)
          (parentSubInput inp group P titleLines child) o g parent
          hwfParent hframedParent hfixedParent hparentAt
        have hstep : ExpandChildFrameStep inp parent child res :=
          expandChild_frame_step hexpandAt hframed hctx hparams
            (hchildCross n P inp o group titleLines _
              parent child res hexpandAt hframed hctx hparams)
            (hparentCross n (by omega : n < F_top) P inp o group titleLines _
              parent child res hexpandAt hframed hctx hparams)
        intro frame hfind r hr hfrom hto hscope
        exact hstep g ⟨entry, hentry⟩
          frame hfind hChildIH hParentIH r hr hfrom hto hscope

/-- Fuel-sliced single-call frame clearance: mirrors
`expandChild_parentRouteFrameClear` (`ExpandChildFrameLiftProof.lean`) but
feeds the sliced lift, so the strict-miss premise is only needed below the
call fuel. The child-cross side comes from the narrow foreign field (no fuel
constraint). The current-call merge step of the original is dead code there
(the lift conclusion already covers the routes) and is omitted. -/
private theorem sliced_routeFrame_of_lift
    (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      FrameClearanceSeam inp o res)
    (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ExclusiveRunNodeDecl inp o res)
    (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RunRouteEndpointIdsScoped inp o res)
    (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RoutePartShelfPositive inp o res)
    (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate execution.graph comp candidate) run
        execution.measured v)
    (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b)
    (hflat8a : FlatC8a)
    (hforeign : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
      (g : ModelBox),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      (∃ _entry : String × Size,
        inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry) →
      g.id ∉ parent.scene.layoutDump.ancestors group.id)
    {F_top : Nat}
    (hstrictBelow : ∀ (m : Nat), m < F_top → ∀ (P : Params) (inp : Input) (o : Options)
      (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentStrictMissGroup group parent)
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext F_top P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildParentRouteFrameClear group parent := by
  have hcC : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildChildRouteParentFrame fuel P inp o group titleLines titleHeight
        parent child res := by
    intro fuel P inp o group titleLines titleHeight parent child res _hexpand _hframed
      _hctx _hparams
    intro hexpand hframed hctx hparams g hgEx gFrame hfindG frame _metric
      _titleLines₀ _dx _dy hframe _hmetric _htitle hdx hdy hwrap cr hcr hfrom hto
      hscope
    exact expandChildChildRouteParentFrame_of_disjoint hexpand hframed hctx hparams
      hgEx hfindG hframe hdx hdy hwrap
      (fixedDisjoint_of_foreign hflat8a hforeign fuel P inp o group titleLines
        titleHeight parent child res g gFrame frame hexpand hframed hctx hparams
        hgEx hfindG hframe)
      hcr hfrom hto hscope
  have hpC : ∀ (m : Nat), m < F_top → ∀ (P : Params) (inp : Input) (o : Options)
      (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentRouteChildFrame m P inp o group titleLines titleHeight
        parent child res := by
    intro m hm P inp o group titleLines titleHeight parent child res _hexpand _hframed
      _hctx _hparams
    intro hexpand hframed hctx hparams _g hgEx _gFrame hfindR _cb hcb _frame _metric
      _titleLines₀ _dx _dy hframe _hmetric _htitle hdx hdy hwrap hgEmb pr hpr hfrom
      hto hscope
    exact expandChildParentRouteChildFrame_of_strictMiss hexpand hframed hctx hparams
      hgEx hfindR hcb hframe hdx hdy hwrap
      (hstrictBelow m hm P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams)
      hgEmb hpr hfrom hto hscope
  have hrec : ExpandChildFrameRecursion F_top P inp o group titleLines titleHeight
      parent child res := by
    intro frame hfind pr hpr hfrom hto hscopeP
    obtain ⟨hwfC, hgC, _hpboxesC, hchildC, hparentC, _hexpandC⟩ := hctx
    obtain ⟨hP, hheight, hwrap⟩ := hparams
    have _hheight := hheight
    obtain ⟨metric, hm, hwrapEq⟩ := hwrap
    obtain ⟨_, _, hwfParent, hframedParent⟩ :=
      subInputWellFormed F_top inp o group P metric titleLines child parent
        hwfC hframed hP hm hwrapEq hchildC hparentC
    have hfixedParent : ∃ entry : String × Size,
        (parentSubInput inp group P titleLines child).fixedSizes.find?
          (fun fixed => fixed.1 == group.id) = some entry := by
      have hpred := List.find?_some hgC
      simp only [Bool.and_eq_true] at hpred
      obtain ⟨_, hnotfixed⟩ := hpred
      have hany : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
        simpa using hnotfixed
      have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
        List.find?_eq_none.mpr (List.any_eq_false.mp hany)
      have hfix : (parentSubInput inp group P titleLines child).fixedSizes =
          inp.fixedSizes ++
            [(group.id, childFrameSize group.direction P.clusterPad
              (titleLines.foldl (fun width line => max width line.width) 0)
              ((max 1 titleLines.length : Int) * P.lineH)
              ⟨child.scene.canvas.w - 2 * P.canvasMargin,
                child.scene.canvas.h - 2 * P.canvasMargin⟩)] := rfl
      refine ⟨(group.id, childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩), ?_⟩
      rw [hfix, List.find?_append, hnone]
      simp
    exact sliced_frame_lift F_top hclear hnodeDecl hscoped hpos hloopRes hloopSep
      subInputWellFormed hcC hpC F_top (by omega : F_top ≤ F_top)
      (parentSubInput inp group P titleLines child) o group parent
      hwfParent hframedParent hfixedParent hparentC frame hfind pr hpr hfrom hto
      hscopeP
  have hscope : ExpandChildFrameScopeOutside F_top P inp o group titleLines titleHeight
      parent child res :=
    expandChild_frame_scope_outside
      (expandChildParentIsolated hexpand hframed hctx hparams)
      hexpand hframed hctx hparams
  exact expandChild_parentRouteFrame_of_recursion hrec hscope

/-- Strict miss at one fuel from strict miss below it: the out-of-scope half
comes from the sliced frame lift, the attached half from the field. -/
private theorem strictMiss_of_below
    (hatt : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentRouteAttachedClear group parent)
    (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      FrameClearanceSeam inp o res)
    (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ExclusiveRunNodeDecl inp o res)
    (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RunRouteEndpointIdsScoped inp o res)
    (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RoutePartShelfPositive inp o res)
    (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate execution.graph comp candidate) run
        execution.measured v)
    (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b)
    (hflat8a : FlatC8a)
    (hforeign : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
      (g : ModelBox),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      (∃ _entry : String × Size,
        inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry) →
      g.id ∉ parent.scene.layoutDump.ancestors group.id)
    {F_top : Nat}
    (hbelow : ∀ (m : Nat), m < F_top → ∀ (P : Params) (inp : Input) (o : Options)
      (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentStrictMissGroup group parent) :
    ∀ (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContext F_top P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildParentStrictMissGroup group parent := by
  intro P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
  exact parentStrictMissGroup_of_frame_attached F_top P inp o group titleLines
    titleHeight parent child res hexpand hframed hctx hparams
    (sliced_routeFrame_of_lift hclear hnodeDecl hscoped hpos hloopRes hloopSep
      hflat8a hforeign hbelow hexpand hframed hctx hparams)
    (hatt F_top P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams)

/-- All-fuels strict miss from the attached field, closing the fuel induction:
each level's frame half comes from the sliced lift fed by the levels below. -/
private theorem strictMiss_restricted_closed
    (hatt : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentRouteAttachedClear group parent)
    (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      FrameClearanceSeam inp o res)
    (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ExclusiveRunNodeDecl inp o res)
    (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RunRouteEndpointIdsScoped inp o res)
    (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RoutePartShelfPositive inp o res)
    (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate execution.graph comp candidate) run
        execution.measured v)
    (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b)
    (hflat8a : FlatC8a)
    (hforeign : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
      (g : ModelBox),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      (∃ _entry : String × Size,
        inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry) →
      g.id ∉ parent.scene.layoutDump.ancestors group.id) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildParentStrictMissGroup group parent := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F ih =>
    intro P inp o group titleLines titleHeight parent child res hexpand hframed hctx
      hparams
    exact strictMiss_of_below hatt hclear hnodeDecl hscoped hpos hloopRes hloopSep
      hflat8a hforeign
      (fun m hm P' inp' o' g' tls' th' par' chi' res' hx hf hc hp =>
        ih m hm P' inp' o' g' tls' th' par' chi' res' hx hf hc hp)
      P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams

 /-- Local copy of the private theorem in `ExpandChildC6GeometryClosed.lean`:
 route clearance from the two parts. -/
 private theorem routeClear_closed
     (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       FrameClearanceSeam inp o res)
     (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ExclusiveRunNodeDecl inp o res)
     (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RunRouteEndpointIdsScoped inp o res)
     (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RoutePartShelfPositive inp o res)
     (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
       comp ∈ components execution.graph →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopReservation (componentCandidate execution.graph comp candidate) run
         execution.measured v)
     (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
       comp ∈ components execution.graph →
       ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
         execution.measured v b)
    (hflat8a : FlatC8a)
    (hforeign : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
      (g : ModelBox),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      (∃ _entry : String × Size,
        inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry) →
      g.id ∉ parent.scene.layoutDump.ancestors group.id)
    (hatt : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentRouteAttachedClear group parent)
    (hstrictAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentStrictMissGroup group parent) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildParentRouteClear group parent := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
  exact expandChild_parentRouteClear_of_parts
    (sliced_routeFrame_of_lift hclear hnodeDecl hscoped hpos hloopRes hloopSep
      hflat8a hforeign
      (fun m hm P' inp' o' g' tls' th' par' chi' res' hx hf hc hp =>
        hstrictAll m P' inp' o' g' tls' th' par' chi' res' hx hf hc hp)
      hexpand hframed hctx hparams)
    (hatt fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams)

 /-- Local copy of the theorem in `ExpandChildC6GeometryExecuted.lean`: pure
 rectangle glue over the six premises. -/
 private theorem expandChild_c6_geometry_inset
     (_fuel : Nat) (P : Params) (inp : Input) (o : Options)
     (group : ModelBox) (_titleLines : List Measure.Line) (titleHeight : Int)
     (parent child res : FamilyResult)
     (hFit : ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       dx = frame.rect.x + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
         P.canvasMargin →
       dy = frame.rect.y + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
         P.canvasMargin →
       ExpandChildTitleWrapped P inp o group titleLines' →
       ∀ (r : Rect),
       (insetRect child.scene.canvas P.canvasMargin).Contained r →
       frame.rect.StrictInside (shiftRect dx dy r))
     (hBox : ∀ cb ∈ child.scene.boxes,
       (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
     (hRt : ∀ cr ∈ child.scene.routes, ∀ p ∈ cr.points,
       PointIn (insetRect child.scene.canvas P.canvasMargin) p)
     (hDisj : ∀ (frame : Box),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
         pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
         Disjoint frame.rect pb.rect)
     (hMiss : ∀ (frame : Box),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
         ¬ Polyline.hitsRect pr.points r)
     (hPos : ∀ (frame : Box),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       0 < frame.rect.w ∧ 0 < frame.rect.h) :
     ExpandChildC6Geometry P inp o group titleHeight parent child res := by
   intro frame tl dx dy hframe hdx hdy hwrap
   have hfitS : ∀ (r : Rect), (insetRect child.scene.canvas P.canvasMargin).Contained r →
       frame.rect.StrictInside (shiftRect dx dy r) :=
     hFit frame tl dx dy hframe hdx hdy hwrap
   obtain ⟨hfw, hfh⟩ := hPos frame hframe
   have ha : ∀ cr ∈ child.scene.routes, ∀ pb ∈ parent.scene.boxes,
       pb.exclusive = true →
       pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
       ¬ Polyline.hitsRect (cr.points.map (shiftPoint dx dy)) pb.rect := by
     intro cr hcr pb hpb hex hscope
     have hconf : ∀ p ∈ cr.points.map (shiftPoint dx dy), PointIn frame.rect p := by
       intro p hp
       obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
       have hqI := hRt cr hcr q hq
       have hqs : PointIn (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin))
           (shiftPoint dx dy q) :=
         pointIn_shift hqI
       have hSI := hfitS _ (Rect.Contained.refl _)
       have hC : frame.rect.Contained
           (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
         simp only [Rect.StrictInside, Rect.Contained] at hSI ⊢
         omega
       have hdeg := pointIn_contained.mp hqs
       exact pointIn_contained.mpr (Rect.Contained.trans hC hdeg)
     have hdisj := hDisj frame hframe pb hpb hex hscope
     exact polyline_in_box_misses_disjoint hfw hfh hconf hdisj
   have hb : ∀ pr ∈ parent.scene.routes, ∀ cb ∈ child.scene.boxes,
       cb.exclusive = true →
       ¬ Polyline.hitsRect pr.points (shiftRect dx dy cb.rect) := by
     intro pr hpr cb hcb hex
     have hcbI := hBox cb hcb
     have hinner : frame.rect.StrictInside (shiftRect dx dy cb.rect) :=
       hfitS _ hcbI
     exact hMiss frame hframe pr hpr (shiftRect dx dy cb.rect) hinner
   exact ⟨ha, hb⟩

 /-- Local copy of the theorem in `ExpandChildC6GeometryExecuted.lean`: the
 per-expansion C6 geometry from parent C8a and parent route clearance. -/
 private theorem stepC6Geometry_holds
     (hC8aParent : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight
         parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       Validator.C8a parent.scene.layoutDump)
     (hRouteClear : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight
         parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildParentRouteClear group parent) :
     RecursiveStepFacts ExpandChildC6Geometry := by
   intro fuel P inp o group titleLines titleHeight parent child res
     hexpand hframed hctx hparams
   have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
   have hFit : ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       dx = frame.rect.x + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
         P.canvasMargin →
       dy = frame.rect.y + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
         P.canvasMargin →
       ExpandChildTitleWrapped P inp o group titleLines' →
       ∀ (r : Rect),
       (insetRect child.scene.canvas P.canvasMargin).Contained r →
       frame.rect.StrictInside (shiftRect dx dy r) := by
     intro frame tl' dx dy hframe hdx hdy hwrap' r hr
     exact expandChild_content_fit_strict fuel P inp o group titleLines titleHeight
       parent child res hexpand hframed hctx hparams frame tl' dx dy hframe hdx hdy
       hwrap' r hr
   have hBox : ∀ cb ∈ child.scene.boxes,
       (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect := by
     intro cb hcb
     exact expandChild_child_boxes_inset fuel P inp o group titleLines titleHeight
       parent child res hexpand hframed hctx hP cb hcb
   have hRt : ∀ cr ∈ child.scene.routes, ∀ p ∈ cr.points,
       PointIn (insetRect child.scene.canvas P.canvasMargin) p := by
     intro cr hcr p hp
     exact expandChild_child_routes_inset fuel P inp o group titleLines titleHeight
       parent child res hexpand hframed hctx hP cr hcr p hp
   have hPos := stepC6_frame_pos fuel P inp o group titleLines titleHeight
     parent child res hexpand hframed hctx hparams
   have hC8a := hC8aParent fuel P inp o group titleLines titleHeight parent child res
     hexpand hframed hctx hparams
   have hanc := stepC8aAncestry_holds fuel P inp o group titleLines titleHeight
     parent child res hexpand hframed hctx hparams
   have hDisj : ∀ (frame : Box),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
         pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
         Disjoint frame.rect pb.rect := by
     intro frame hframe pb hpb hex hscope
     obtain ⟨_, _, _, _, hrole, _, _, hiso⟩ :=
       expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
         hexpand hframed hctx hanc frame titleLines _ _ hframe rfl rfl hparams.2.2
     have hfid := stepC6_frame_id_eq hframe
     have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
       List.mem_of_find?_eq_some hframe
     have hpbMem : pb ∈ parent.scene.layoutDump.boxes := hpb
     have hne' : pb.id ≠ group.id := by
       intro h
       apply hscope
       rw [h]
       exact List.mem_cons.mpr (Or.inl rfl)
     have hne : pb.id ≠ frame.id := by
       rw [hfid]
       exact hne'
     have h1 : frame.id ∉ parent.scene.layoutDump.ancestors pb.id := by
       rw [hfid]
       exact hiso pb hpb hne'
     have h2 : pb.id ∉ parent.scene.layoutDump.ancestors frame.id := by
       rw [hfid]
       exact fun hm => hscope (List.mem_cons.mpr (Or.inr hm))
     exact hC8a frame hframeMem hrole pb hpbMem hne h1 h2
   have hrc := hRouteClear fuel P inp o group titleLines titleHeight parent child res
     hexpand hframed hctx hparams
   have hMiss : ∀ (frame : Box),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
         ¬ Polyline.hitsRect pr.points r := by
     intro frame hframe pr hpr r hSI
     exact expandChild_parentFrame_routes hrc hexpand hframed hctx frame titleLines _ _
       hframe rfl rfl hparams.2.2 pr hpr r hSI
   exact expandChild_c6_geometry_inset fuel P inp o group titleLines titleHeight parent child res
     hFit hBox hRt hDisj hMiss hPos

/-- Local copy of the theorem in `ExpandChildC6GeometryClosed.lean`: closed
C6 geometry from the flat clause, the flat-stage seams, the narrow foreign
residual, the attached field, and the fuel-closed strict miss. -/
 private theorem stepC6Geometry_closed
     (hflat8a : FlatC8a)
     (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       FrameClearanceSeam inp o res)
     (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ExclusiveRunNodeDecl inp o res)
     (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RunRouteEndpointIdsScoped inp o res)
     (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RoutePartShelfPositive inp o res)
     (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
       comp ∈ components execution.graph →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopReservation (componentCandidate execution.graph comp candidate) run
         execution.measured v)
     (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
       comp ∈ components execution.graph →
       ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
         execution.measured v b)
    (hforeign : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
      (g : ModelBox),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      (∃ _entry : String × Size,
        inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some _entry) →
      g.id ∉ parent.scene.layoutDump.ancestors group.id)
    (hatt : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentRouteAttachedClear group parent)
    (hstrictAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentStrictMissGroup group parent) :
    RecursiveStepFacts ExpandChildC6Geometry := by
  exact stepC6Geometry_holds (c8aParent_of_flat hflat8a)
    (routeClear_closed hclear hnodeDecl hscoped hpos hloopRes hloopSep hflat8a hforeign
      hatt hstrictAll)

/-- Local copy of the private theorem in `ExpandChildParentFrameDirect.lean`:
the C8a step of one expansion from the below-fuel geometry. -/
private theorem c8aStep_of_below {F n : Nat} (hlt : n < F)
     (below8a : ∀ (m : Nat), m < F → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildC8aGeometry P inp o group titleHeight parent child res)
     {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext n P inp o group titleLines titleHeight parent child res)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
     ExpandChildC8aStep P inp o group titleHeight parent child res := by
   intro frame tl dx dy hframe hdx hdy hwrap
   obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
     expandChild_c8a_structure n P inp o group titleLines titleHeight parent child res
       hexpand hframed hctx
       (stepC8aAncestry_holds n P inp o group titleLines titleHeight parent child res
         hexpand hframed hctx hparams)
       frame tl dx dy hframe hdx hdy hwrap
   have hg := below8a n hlt P inp o group titleLines titleHeight parent child res
     hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
   exact ⟨s1, s2, s3, s4, s5, s6, hg, s7, s8⟩

 /-- Local copy of the private theorem in `ExpandChildParentFrameDirect.lean`:
 `layoutRecursive` preserves C8a from the flat clause and the below-fuel geometry. -/
 private theorem layoutRecursive_c8a_of_below (hflat8a : FlatC8a) {F : Nat}
     (below8a : ∀ (m : Nat), m < F → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildC8aGeometry P inp o group titleHeight parent child res) :
     ∀ (n : Nat), n ≤ F → ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       layoutRecursive n inp o = .ok res → Validator.C8a res.scene.layoutDump := by
   intro n
   induction n with
   | zero =>
     intro _ inp o res hwf hframed h
     exact hflat8a inp o res hwf hframed h
   | succ n ih =>
     intro hle inp o res hwf hframed h
     have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
     have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
     rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
       ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
     · exact hflat8a inp o res hwf hframed hlayout
     · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
         hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
         layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
       obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
         subInputsWellFormed n inp o group P metric titleLines child parent hwf hframed hP hm hwrap
           hchild hparentAt
       have hchildC8a := ih (by omega : n ≤ F) _ _ _ hwfChild hframedChild hchild
       have hparentC8a := ih (by omega : n ≤ F) _ _ _ hwfParent hframedParent hparentAt
       have hstep := c8aStep_of_below (by omega : n < F) below8a hexpandAt hframed
         ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
         ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
       exact expandChild_c8a hchildC8a hparentC8a hstep hexpandAt

 /-- Local copy of the private theorem in `ExpandChildParentFrameDirect.lean`:
 the parent scene satisfies C8a from the flat clause and the below-fuel geometry. -/
 private theorem parentScene_c8a_below {F : Nat} (hflat8a : FlatC8a)
     (below8a : ∀ (m : Nat), m < F → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildC8aGeometry P inp o group titleHeight parent child res)
     {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext F P inp o group titleLines titleHeight parent child res) :
     Validator.C8a parent.scene.layoutDump := by
   have hparent : layoutRecursive F (parentSubInput inp group P titleLines child) o = .ok parent :=
     hctx.2.2.2.2.1
   exact layoutRecursive_c8a_of_below hflat8a below8a F (Nat.le_refl _)
     (parentSubInput inp group P titleLines child) o parent
     (parentInput_wellFormed hctx) (parentInput_framed hframed hctx) hparent

 /-- Local copy of the private theorem in `ExpandChildParentFrameDirect.lean`:
 the C8b step of one expansion from the below-fuel geometry. -/
 private theorem c8bStep_of_below {F n : Nat} (hlt : n < F)
     (below8b : ∀ (m : Nat), m < F → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       InputFixedFit inp o →
       ExpandChildC8bGeometry P inp o group titleHeight parent child res)
     {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext n P inp o group titleLines titleHeight parent child res)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
     (hfix : InputFixedFit inp o) :
     ExpandChildC8bStep P inp o group titleHeight parent child res := by
   intro frame tl dx dy hframe hdx hdy hwrap
   have howners := expandChild_label_owners n P inp o group titleLines titleHeight parent child res
     hexpand hframed hctx hparams
   have hc := expandChild_c8b_structure n P inp o group titleLines titleHeight
     parent child res hexpand hframed hctx howners
     frame tl dx dy hframe hdx hdy hwrap
   obtain ⟨g1, g2, g3, g4⟩ := below8b n hlt P inp o group titleLines titleHeight parent child res
     hexpand hframed hctx hparams hfix frame tl dx dy hframe hdx hdy hwrap
   exact ⟨hc, g1, g2, g3, g4⟩

 /-- Local copy of the private theorem in `ExpandChildParentFrameDirect.lean`:
 `layoutRecursive` preserves C8b from the flat clause and the below-fuel geometry. -/
 private theorem layoutRecursive_c8b_of_below (hflat8b : FlatC8b) {F : Nat}
     (below8b : ∀ (m : Nat), m < F → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       InputFixedFit inp o →
       ExpandChildC8bGeometry P inp o group titleHeight parent child res) :
     ∀ (n : Nat), n ≤ F → ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       InputFixedFit inp o →
       layoutRecursive n inp o = .ok res → Validator.C8b res.scene.layoutDump := by
   intro n
   induction n with
   | zero =>
     intro _ inp o res hwf hframed hfit h
     exact hflat8b inp o res hwf hframed hfit h
   | succ n ih =>
     intro hle inp o res hwf hframed hfit h
     have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
     have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
     rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
       ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
     · exact hflat8b inp o res hwf hframed hfit hlayout
     · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
         hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
         layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
       obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
         subInputsWellFormed n inp o group P metric titleLines child parent hwf hframed hP hm hwrap
           hchild hparentAt
       have hfitChild : InputFixedFit
           (Elegant.Layered.PipelineImpl.childSubInput inp group)
           (Elegant.Layered.PipelineImpl.childSubOptions o group) :=
         hfit.childSubInput group
       have hcm := layoutRecursive_canvas_margins n hchild
       have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
         rw [checkedParams_canvasMargin hP]
         exact hcm.1
       have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
         rw [checkedParams_canvasMargin hP]
         exact hcm.2
       have hfitParent : InputFixedFit
           (parentSubInput inp group P titleLines child) o :=
         InputFixedFit.parentSubInput hwf hfit hP hm hwrap hcw hch
       have hchildC8b := ih (by omega : n ≤ F) _ _ _ hwfChild hframedChild hfitChild hchild
       have hparentC8b := ih (by omega : n ≤ F) _ _ _ hwfParent hframedParent hfitParent hparentAt
       have hstep := c8bStep_of_below (by omega : n < F) below8b hexpandAt hframed
        ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
        ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩ hfit
       exact expandChild_c8b hchildC8b hparentC8b hstep hexpandAt

 /-- Local copy of the private theorem in `ExpandChildParentFrameDirect.lean`:
 the parent scene satisfies C8b from the flat clause and the below-fuel geometry. -/
 private theorem parentScene_c8b_below {F : Nat} (hflat8b : FlatC8b)
     (below8b : ∀ (m : Nat), m < F → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       InputFixedFit inp o →
       ExpandChildC8bGeometry P inp o group titleHeight parent child res)
     {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hfit : InputFixedFit (parentSubInput inp group P titleLines child) o)
     (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext F P inp o group titleLines titleHeight parent child res) :
     Validator.C8b parent.scene.layoutDump := by
   have hparent : layoutRecursive F (parentSubInput inp group P titleLines child) o = .ok parent :=
     hctx.2.2.2.2.1
   exact layoutRecursive_c8b_of_below hflat8b below8b F (Nat.le_refl _)
     (parentSubInput inp group P titleLines child) o parent
     (parentInput_wellFormed hctx) (parentInput_framed hframed hctx) hfit hparent

 /-- Local copy of the private theorem in `ExpandChildParentFrameDirect.lean`:
 the frame has group role and the ancestor chain is isolated. -/
 private theorem parentFrame_role_isolation
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines titleLines' : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult} {frame : Box} {dx dy : Int}
     (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res)
     (hanc : ExpandChildC8aAncestry group parent child res)
     (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
     (hdx : dx = frame.rect.x + (childInset group.direction P.clusterPad
         (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
       P.canvasMargin)
     (hdy : dy = frame.rect.y + (childInset group.direction P.clusterPad
         (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
       P.canvasMargin)
     (hwrap : ExpandChildTitleWrapped P inp o group titleLines') :
     frame.role = "group" ∧
       (∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
         group.id ∉ parent.scene.layoutDump.ancestors pb.id) := by
   obtain ⟨_, _, _, _, hrole, _, _, hiso⟩ :=
     expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
       hexpand hframed hctx hanc
       frame titleLines' dx dy hframe hdx hdy hwrap
   exact ⟨hrole, hiso⟩

 /-- Local copy of the theorem in `ExpandChildParentFrameDirect.lean`: the
 located frame satisfies the full parent-frame fact for every executed call. -/
 private theorem expandChild_parentFrame_direct
     (hflat8a : FlatC8a)
     (hflat8b : FlatC8b)
     {fuel : Nat}
     (below8a : ∀ (m : Nat), m < fuel → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildC8aGeometry P inp o group titleHeight parent child res)
     (below8b : ∀ (m : Nat), m < fuel → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       InputFixedFit inp o →
       ExpandChildC8bGeometry P inp o group titleHeight parent child res)
     {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
     (hframeStrict : ExpandChildParentFrameStrict group parent)
     (hstepStrict : ExpandChildParentStrictStep parent)
     (hfit : InputFixedFit (parentSubInput inp group P titleLines child) o) :
     ExpandChildParentFrame P inp o group titleHeight parent child := by
   have hanc : ExpandChildC8aAncestry group parent child res :=
     stepC8aAncestry_holds fuel P inp o group titleLines titleHeight parent child res
       hexpand hframed hctx hparams
   intro frame titleLines' dx dy hframe hdx hdy hwrap
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro pb hpbMem _hex hforeign
     have hfid := frame_id_eq hframe
     have hC8a := parentScene_c8a_below hflat8a below8a hexpand hframed hctx
     obtain ⟨hrole, hiso⟩ := parentFrame_role_isolation hexpand hframed hctx hanc
       hframe hdx hdy hwrap
     have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
       List.mem_of_find?_eq_some hframe
     have hpbMemD : pb ∈ parent.scene.layoutDump.boxes := hpbMem
     have hne' : pb.id ≠ group.id := by
       intro h
       apply hforeign
       rw [h]
       exact List.mem_cons.mpr (Or.inl rfl)
     have hne : pb.id ≠ frame.id := by
       rw [hfid]
       exact hne'
     have h1 : frame.id ∉ parent.scene.layoutDump.ancestors pb.id := by
       rw [hfid]
       exact hiso pb hpbMem hne'
     have h2 : pb.id ∉ parent.scene.layoutDump.ancestors frame.id := by
       rw [hfid]
       exact fun hm => hforeign (List.mem_cons.mpr (Or.inr hm))
     exact hC8a frame hframeMem hrole pb hpbMemD hne h1 h2
   · intro pl hplMem hown
     have hC8b := parentScene_c8b_below hflat8b below8b hfit hexpand hframed hctx
     obtain ⟨hrole, _⟩ := parentFrame_role_isolation hexpand hframed hctx hanc
       hframe hdx hdy hwrap
     have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
       List.mem_of_find?_eq_some hframe
     have hplD : pl.toLabel ∈ parent.scene.layoutDump.labels :=
       List.mem_map.mpr ⟨pl, hplMem, rfl⟩
     rcases hC8b frame hframeMem hrole pl.toLabel hplD with hdisj | hstrict
     · exact hdisj
     · have hstrict' : frame.rect.StrictInside pl.rect := hstrict
       exact absurd hstrict' (hframeStrict frame hframe pl hplMem hown)
   · exact expandChild_parentFrame_ancestor hstepStrict hexpand hframed hctx
       frame titleLines' dx dy hframe hdx hdy hwrap
   · intro g hg hgRole hgNe hgNotAnc1 hgNotAnc2
     have _hdx := hdx
     have _hdy := hdy
     have _hwrap := hwrap
     have _hdxv : dx = dx := rfl
     have _hdyv : dy = dy := rfl
     have _htlv : titleLines' = titleLines' := rfl
     have hfid := frame_id_eq hframe
     have hC8a := parentScene_c8a_below hflat8a below8a hexpand hframed hctx
     have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
       List.mem_of_find?_eq_some hframe
     have hgMemD : g ∈ parent.scene.layoutDump.boxes := hg
     have hne : frame.id ≠ g.id := by
       rw [hfid]
       exact fun h => hgNe h.symm
     have h1 : g.id ∉ parent.scene.layoutDump.ancestors frame.id := by
       rw [hfid]
       exact hgNotAnc1
     have h2 : frame.id ∉ parent.scene.layoutDump.ancestors g.id := by
       rw [hfid]
       exact hgNotAnc2
     exact hC8a g hgMemD hgRole frame hframeMem hne h1 h2

 /-- Local copy of the theorem in `ExpandChildParentFrameDirect.lean`: fuel
 induction closes the loop for any step. -/
 private theorem recursiveStepFacts_of_below
     (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
       FamilyResult → Prop)
     (hclose : ∀ (fuel : Nat),
       (∀ (fuel' : Nat), fuel' < fuel → ∀ (P : Params) (inp : Input) (o : Options)
         (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
         (parent child res : FamilyResult),
         expandChild P inp o group titleHeight parent child = .ok res →
         framedParents inp = true →
         ExpandChildCallContext fuel' P inp o group titleLines titleHeight parent child res →
         ExpandChildCallParams P inp o group titleLines titleHeight →
         Step P inp o group titleHeight parent child res) →
       ∀ (P : Params) (inp : Input) (o : Options) (group : ModelBox)
         (titleLines : List Measure.Line) (titleHeight : Int)
         (parent child res : FamilyResult),
         expandChild P inp o group titleHeight parent child = .ok res →
         framedParents inp = true →
         ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
         ExpandChildCallParams P inp o group titleLines titleHeight →
         Step P inp o group titleHeight parent child res) :
     RecursiveStepFacts Step := by
   intro fuel
   induction fuel using Nat.strongRecOn with
   | _ fuel ih =>
     intro P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
     exact hclose fuel (fun f hlt P' inp' o' g' tls' th' par' chi' res' hx hf hc hp =>
       ih f hlt P' inp' o' g' tls' th' par' chi' res' hx hf hc hp)
       P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams

/-- Single-call C7 geometry: the body of `stepC7Geometry_holds` with the
per-call fit, parent fit, and parent-side residuals as single-call hypotheses.
The family theorem feeds the threaded fit here through the fit-threaded lift
copy; the all-inputs wrapper below feeds the seam field. -/
private theorem stepC7Geometry_single
    {fuel : Nat}
    (hflat8a : FlatC8a)
    (hflat8b : FlatC8b)
    (hbelow8b : ∀ (m : Nat), m < fuel → ∀ (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      InputFixedFit inp o →
      ExpandChildC8bGeometry P inp o group titleHeight parent child res)
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hframeStrict : ExpandChildParentFrameStrict group parent)
    (hstepStrict : ExpandChildParentStrictStep parent)
    (hfit : InputFixedFit inp o) :
    ExpandChildC7Geometry P inp o group titleHeight parent child res := by
  have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
  have below8a : ∀ (f : Nat), f < fuel → ∀ (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext f P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aGeometry P inp o group titleHeight parent child res :=
    fun f _ => stepC8aGeometry_holds f
  have below8b : ∀ (m : Nat), m < fuel → ∀ (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      InputFixedFit inp o →
      ExpandChildC8bGeometry P inp o group titleHeight parent child res := hbelow8b
  have hfitParent : InputFixedFit (parentSubInput inp group P titleLines child) o := by
    obtain ⟨hwf, _hgroup, _hpb, hchild, _hparent, _hexpand'⟩ := hctx
    obtain ⟨_metric, hm, hwrap⟩ := hparams.2.2
    have hcm := layoutRecursive_canvas_margins fuel hchild
    have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
      rw [checkedParams_canvasMargin hP]
      exact hcm.1
    have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
      rw [checkedParams_canvasMargin hP]
      exact hcm.2
    exact InputFixedFit.parentSubInput hwf hfit hP hm hwrap hcw hch
  have hpf : ExpandChildParentFrame P inp o group titleHeight parent child :=
    expandChild_parentFrame_direct hflat8a hflat8b below8a below8b
      hexpand hframed hctx hparams hframeStrict hstepStrict hfitParent
  have hchildBoxes : ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect := by
    intro cb hcb
    exact expandChild_child_boxes_inset fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hP cb hcb
  have hchildLabels : ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect := by
    intro cl hcl
    exact expandChild_child_labels_inset fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hfit hctx hP cl hcl
  have hparentBoxes : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
        Disjoint frame.rect pb.rect := by
    intro frame hframe pb hpb hex hforeign
    have hq := hpf frame titleLines _ _ hframe rfl rfl hparams.2.2
    exact hq.1 pb hpb hex hforeign
  have hparentLabels : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
        Disjoint frame.rect pl.rect := by
    intro frame hframe pl hpl hown
    have hq := hpf frame titleLines _ _ hframe rfl rfl hparams.2.2
    exact hq.2.1 pl hpl hown
  have howners : ExpandChildLabelOwners inp parent child :=
    expandChild_label_owners fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams
  exact expandChild_c7_geometry_executed fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams
    hchildBoxes hchildLabels hparentBoxes hparentLabels howners

 /-- Local copy of the theorem in `ExpandChildC7GeometryExecuted.lean`: the
 per-expansion C7 geometry holds for every executed call. -/
 private theorem stepC7Geometry_holds
     (hflat8a : FlatC8a)
     (hflat8b : FlatC8b)
     (hbelow8b : ∀ (fuel : Nat), ∀ (fuel' : Nat), fuel' < fuel → ∀ (P : Params) (inp : Input)
       (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel' P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       InputFixedFit inp o →
       ExpandChildC8bGeometry P inp o group titleHeight parent child res)
     (hframeStrict : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildParentFrameStrict group parent)
     (hstepStrict : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildParentStrictStep parent)
     :
     RecursiveStepFacts (fun P inp o group titleHeight parent child res =>
       InputFixedFit inp o → ExpandChildC7Geometry P inp o group titleHeight
         parent child res) := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams hfix
  exact stepC7Geometry_single hflat8a hflat8b (hbelow8b fuel)
    hexpand hframed hctx hparams
    (hframeStrict fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams)
    (hstepStrict fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams)
    hfix

 /-- Local copy of the private theorem in `ExpandChildC8bGeometryExecuted.lean`:
 pure geometry behind the strict caption containment. -/
 private theorem titleRect_strictInside_aux {direction : String}
     {pad tw th conw conh fx fy fw fh : Int}
     (hpad : 0 < pad)
     (hconw : 0 ≤ conw) (hconh : 0 ≤ conh)
     (hfw : (childFrameSize direction pad tw th ⟨conw, conh⟩).w ≤ fw)
     (hfh : (childFrameSize direction pad tw th ⟨conw, conh⟩).h ≤ fh) :
     (⟨fx, fy, fw, fh⟩ : Rect).StrictInside
       (childTitleRect direction pad tw th ⟨fx, fy, fw, fh⟩) := by
   have hW : tw + 2 * pad ≤ fw := by
     unfold childFrameSize at hfw
     split at hfw <;> dsimp only at hfw <;> omega
   have hH : th + 2 * pad ≤ fh := by
     unfold childFrameSize at hfh
     split at hfh <;> dsimp only at hfh <;> omega
   unfold childTitleRect
   split <;> unfold Rect.StrictInside <;> dsimp only <;>
     simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] <;> omega

 /-- Local copy of the theorem in `ExpandChildC8bGeometryExecuted.lean`: the
 caption rect of an executed `expandChild` lies strictly inside the located
 group frame. The margin cover comes from `SceneBounds.layoutRecursive_canvas_margins`. -/
 private theorem frame_strictInside_caption
     (fuel : Nat) (P : Params) (inp : Input) (o : Options)
     (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
     (parent child res : FamilyResult)
     (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (_hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
     ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
     parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
     dx = frame.rect.x + (childInset group.direction P.clusterPad
         (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
       P.canvasMargin →
     dy = frame.rect.y + (childInset group.direction P.clusterPad
         (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
       P.canvasMargin →
     ExpandChildTitleWrapped P inp o group titleLines' →
     frame.rect.StrictInside
       (groupTitleRectC8 group P titleLines' titleHeight frame) := by
   intro frame titleLines' _dx _dy hframe _hdx _hdy hwrap'
   obtain ⟨hw, hh⟩ := expandChild_frame_size_bounds fuel P inp o group titleLines
     titleHeight parent child res _hexpand _hframed hctx hparams frame titleLines'
     hframe hwrap'
   obtain ⟨hP, _hheightEq, _hwrapCtx⟩ := hparams
   have hpad : 0 < P.clusterPad := callParams_clusterPad_pos hP
   obtain ⟨_hwf, _hgroup, _hpb, hchild, _hparent, _hexpand'⟩ := hctx
   have hQchild : checkedParams (childSubOptions o group).profile
       (childSubInput inp group).kind = .ok P := hP
   have hcm := layoutRecursive_canvas_margins fuel hchild
   have hQm : P.canvasMargin
       = canvasMarginOf (childSubOptions o group).profile (childSubInput inp group).kind := by
     rw [checkedParams_canvasMargin hQchild]
   have hconw : 0 ≤ child.scene.canvas.w - 2 * P.canvasMargin := by omega
   have hconh : 0 ≤ child.scene.canvas.h - 2 * P.canvasMargin := by omega
   exact titleRect_strictInside_aux hpad hconw hconh hw hh

 /-- Local copy of the theorem in `ExpandChildC8bGeometryExecuted.lean`: the
 corrected inset C8b geometry of one `expandChild` call. -/
 private theorem expandChild_c8b_geometry_inset
     (fuel : Nat) (P : Params) (inp : Input) (o : Options)
     (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
     (parent child res : FamilyResult)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res)
     (hAnc : ExpandChildC8aAncestry group parent child res)
     (hFitStrict : ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       dx = frame.rect.x + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
         P.canvasMargin →
       dy = frame.rect.y + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
         P.canvasMargin →
       ExpandChildTitleWrapped P inp o group titleLines' →
       frame.rect.StrictInside
         (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)))
     (hChildBoxes : ∀ cb ∈ child.scene.boxes,
       (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
     (hChildLabels : ∀ cl ∈ child.scene.labels,
       (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect)
     (hCapStrict : ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       dx = frame.rect.x + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
         P.canvasMargin →
       dy = frame.rect.y + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
         P.canvasMargin →
       ExpandChildTitleWrapped P inp o group titleLines' →
       frame.rect.StrictInside (groupTitleRectC8 group P titleLines' titleHeight frame))
     (hCapDisj : ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       dx = frame.rect.x + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
         P.canvasMargin →
       dy = frame.rect.y + (childInset group.direction P.clusterPad
           (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
         P.canvasMargin →
       ExpandChildTitleWrapped P inp o group titleLines' →
       Disjoint (groupTitleRectC8 group P titleLines' titleHeight frame)
         (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)))
     (hParentFrame : ExpandChildParentFrame P inp o group titleHeight parent child) :
     ExpandChildC8bGeometry P inp o group titleHeight parent child res := by
   intro frame tl dx dy hframe hdx hdy hwrap
   have hfitS := hFitStrict frame tl dx dy hframe hdx hdy hwrap
   have hfit : frame.rect.Contained
       (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) :=
     strictInside_contained hfitS
   have hbandT := hCapStrict frame tl dx dy hframe hdx hdy hwrap
   have hbandD := hCapDisj frame tl dx dy hframe hdx hdy hwrap
   obtain ⟨_hparentBox, hparentLabel, hancStrict, hforeignDisj⟩ :=
     hParentFrame frame tl dx dy hframe hdx hdy hwrap
   have hSCcg : ∀ cg ∈ child.scene.boxes,
       (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)).Contained
         (shiftRect dx dy cg.rect) := by
     intro cg hcg
     exact (contained_shiftRect dx dy).mpr (hChildBoxes cg hcg)
   have hSCcl : ∀ cl ∈ child.scene.labels,
       (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)).Contained
         (shiftRect dx dy cl.rect) := by
     intro cl hcl
     exact (contained_shiftRect dx dy).mpr (hChildLabels cl hcl)
   have hFcg : ∀ cg ∈ child.scene.boxes,
       frame.rect.Contained (shiftRect dx dy cg.rect) := by
     intro cg hcg
     exact Rect.Contained.trans hfit (hSCcg cg hcg)
   have hFcl : ∀ cl ∈ child.scene.labels,
       frame.rect.Contained (shiftRect dx dy cl.rect) := by
     intro cl hcl
     exact Rect.Contained.trans hfit (hSCcl cl hcl)
   have hnodup := parent_scene_box_ids_nodup fuel P inp o group titleLines
     titleHeight parent child res hctx
   have frame_eq : ∀ g ∈ parent.scene.boxes, g.id = group.id → g = frame := by
     intro g hg hid
     have hgf : parent.scene.boxes.find? (fun a => a.id == g.id) = some g :=
       Assembly.keyed_lookup_eq (·.id) _ hnodup g hg
     simp only [hid] at hgf
     exact Option.some.inj (hgf.symm.trans hframe)
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro g hg hgRole cl hcl
     by_cases hgId : g.id = group.id
     · have hge : g = frame := frame_eq g hg hgId
       subst hge
       exact Or.inr (strictInside_of_strictInside_contained hfitS (hSCcl cl hcl))
     · by_cases hgAnc : g.id ∈ parent.scene.layoutDump.ancestors group.id
       · have hgStrict := hancStrict g hg hgRole hgAnc
         exact Or.inr (strictInside_of_strictInside_contained hgStrict
           (hFcl cl hcl))
       · have hgNotDesc : group.id ∉ parent.scene.layoutDump.ancestors g.id :=
           hAnc.2 g hg hgId
         have hdisj := hforeignDisj g hg hgRole hgId hgAnc hgNotDesc
         exact Or.inl ((Rect.disjoint_comm _ _).mp
           (disjoint_contained_left (hFcl cl hcl) ((Rect.disjoint_comm _ _).mp hdisj)))
   · intro cg hcg cgRole pl hpl hown
     have hdisjF := hparentLabel pl hpl hown
     exact Or.inl (disjoint_contained_left (hFcg cg hcg) hdisjF)
   · intro cg hcg cgRole
     exact Or.inl (disjoint_contained_left (hSCcg cg hcg)
       ((Rect.disjoint_comm _ _).mp hbandD))
   · intro g hg hgRole
     by_cases hgId : g.id = group.id
     · have hge : g = frame := frame_eq g hg hgId
       subst hge
       exact Or.inr hbandT
     · by_cases hgAnc : g.id ∈ parent.scene.layoutDump.ancestors group.id
       · have hgStrict := hancStrict g hg hgRole hgAnc
         exact Or.inr (strictInside_of_strictInside_contained hgStrict
           (strictInside_contained hbandT))
       · have hgNotDesc : group.id ∉ parent.scene.layoutDump.ancestors g.id :=
           hAnc.2 g hg hgId
         have hdisj := hforeignDisj g hg hgRole hgId hgAnc hgNotDesc
         exact Or.inl ((Rect.disjoint_comm _ _).mp
           (disjoint_contained_left (strictInside_contained hbandT)
             ((Rect.disjoint_comm _ _).mp hdisj)))

 /-- Local copy of the theorem in `ExpandChildC8bGeometryExecuted.lean`: the
 C8b geometry at one fuel, from the step facts below it. -/
 private theorem stepC8bGeometry_of_below
     (fuel : Nat)
     (below8a : ∀ (m : Nat), m < fuel → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildC8aGeometry P inp o group titleHeight parent child res)
     (below8b : ∀ (m : Nat), m < fuel → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext m P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       InputFixedFit inp o →
       ExpandChildC8bGeometry P inp o group titleHeight parent child res)
     (hflat8a : FlatC8a) (hflat8b : FlatC8b)
     {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
     (hframeStrict : ExpandChildParentFrameStrict group parent)
     (hstepStrict : ExpandChildParentStrictStep parent)
     (hfix : InputFixedFit inp o) :
     ExpandChildC8bGeometry P inp o group titleHeight parent child res := by
   have hP := hparams.1
   have hwrapCtx := hparams.2.2
   obtain ⟨metric, hm, hwrap⟩ := hwrapCtx
   have hChildBoxes := expandChild_child_boxes_inset fuel P inp o group titleLines
     titleHeight parent child res hexpand hframed hctx hP
   have hChildLabels := expandChild_child_labels_inset fuel P inp o group titleLines
     titleHeight parent child res hexpand hframed hfix hctx hP
   have hFitStrict : ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       dx = frame.rect.x + (childInset group.direction P.clusterPad
           (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
         P.canvasMargin →
       dy = frame.rect.y + (childInset group.direction P.clusterPad
           (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
         P.canvasMargin →
       ExpandChildTitleWrapped P inp o group tl →
       frame.rect.StrictInside
         (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
     intro frame tl dx dy hframe hdx hdy hwrap
     exact expandChild_content_fit_strict fuel P inp o group titleLines titleHeight
       parent child res hexpand hframed hctx hparams frame tl dx dy hframe hdx
       hdy hwrap _ (by simp only [insetRect, Rect.Contained]; omega)
   have hCapStrict : ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       dx = frame.rect.x + (childInset group.direction P.clusterPad
           (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
         P.canvasMargin →
       dy = frame.rect.y + (childInset group.direction P.clusterPad
           (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
         P.canvasMargin →
       ExpandChildTitleWrapped P inp o group tl →
       frame.rect.StrictInside
         (groupTitleRectC8 group P tl titleHeight frame) := by
     intro frame tl dx dy hframe hdx hdy hwrap
     exact frame_strictInside_caption fuel P inp o group titleLines titleHeight
       parent child res hexpand hframed hctx hparams frame tl dx dy hframe hdx
       hdy hwrap
   have hCapDisj : ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
       parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
       dx = frame.rect.x + (childInset group.direction P.clusterPad
           (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
         P.canvasMargin →
       dy = frame.rect.y + (childInset group.direction P.clusterPad
           (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
         P.canvasMargin →
       ExpandChildTitleWrapped P inp o group tl →
       Disjoint (groupTitleRectC8 group P tl titleHeight frame)
         (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
     intro frame tl dx dy hframe hdx hdy hwrap
     exact (expandChild_title_band fuel P inp o group titleLines titleHeight parent
       child res hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy
       hwrap).2
   have hAnc := stepC8aAncestry_holds fuel P inp o group titleLines titleHeight
     parent child res hexpand hframed hctx hparams
   have hfitParent : InputFixedFit (parentSubInput inp group P titleLines child) o := by
     obtain ⟨hwf, _hgroup, _hpb, hchild, _hparent, _hexpand'⟩ := hctx
     have hcm := layoutRecursive_canvas_margins fuel hchild
     have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
       rw [checkedParams_canvasMargin hP]
       exact hcm.1
     have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
       rw [checkedParams_canvasMargin hP]
       exact hcm.2
     exact InputFixedFit.parentSubInput hwf hfix hP hm hwrap hcw hch
   have hParentFrame := expandChild_parentFrame_direct hflat8a hflat8b below8a
     below8b hexpand hframed hctx hparams hframeStrict hstepStrict hfitParent
   exact expandChild_c8b_geometry_inset fuel P inp o group titleLines titleHeight
     parent child res hctx hAnc hFitStrict hChildBoxes hChildLabels hCapStrict
     hCapDisj hParentFrame

 /-- Local copy of the theorem in `ExpandChildC8bGeometryExecuted.lean`:
 executed-call C8b geometry from the flat clauses, the two parent-side
 residuals, and the caller fit in per-call form. -/
 private theorem stepC8bGeometry_holds
     (hflat8a : FlatC8a) (hflat8b : FlatC8b)
     (hframeStrict : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildParentFrameStrict group parent)
     (hstepStrict : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildParentStrictStep parent)
     :
     RecursiveStepFacts (fun P inp o group titleHeight parent child res =>
       InputFixedFit inp o → ExpandChildC8bGeometry P inp o group titleHeight
         parent child res) := by
   apply recursiveStepFacts_of_below
   intro fuel below8b P inp o group titleLines titleHeight parent child res
     hexpand hframed hctx hparams hfix
   exact stepC8bGeometry_of_below fuel
     (fun f _ P' inp' o' g' tls' th' par' chi' res' hx hf hc hp =>
       stepC8aGeometry_holds f P' inp' o' g' tls' th' par' chi' res' hx hf hc hp)
     below8b hflat8a hflat8b hexpand hframed hctx hparams
     (hframeStrict fuel P inp o group titleLines titleHeight parent child res
       hexpand hframed hctx hparams)
     (hstepStrict fuel P inp o group titleLines titleHeight parent child res
       hexpand hframed hctx hparams)
     hfix

/-- The old `stepC6Geometry` fact derived from the narrow seams: the flat C8a
clause from the border-span seams, the flat-stage premises from the closed
scope/loop reductions, the narrow foreign residual, the attached field, and
the fuel-closed strict miss. -/
 theorem c6Geometry_of_seams (S : LayeredSeams) :
     RecursiveStepFacts ExpandChildC6Geometry := by
   have hflat8a : FlatC8a := flatC8a_of_span_seams
     (foreignBorderSpansSeparated foreignClusterRankSpans'
       foreignBorderLayerOrder' (foreignBorderChainXAligned' S.foreignBorderDivergeStable))
     (foreignNonGroupSpansClear bracketMarkersAtRank'
       plainClearOfSideMarker' (sideMarkerSpanAligned' (foreignBorderChainXAligned' S.foreignBorderDivergeStable)))
     (fun inp o res hwf hfp =>
       bracketInsidePremises
         (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
         (fun execution => titleCopySpanClearStrict_executed hwf hfp execution))
   have hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       FrameClearanceSeam inp o res := fun inp o res hwfInp hframedInp =>
     frameClearanceSeam_holds (bracketInsidePremises
       (fun execution => dummyInsideProxyRowClear_executed' execution hwfInp hframedInp)
       (fun execution => titleCopySpanClearStrict_executed hwfInp hframedInp execution))
   have hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ExclusiveRunNodeDecl inp o res := fun inp o res _hwf _hfp =>
     exclusiveRunNodeDecl_of_preserved (inp := inp) (o := o) (res := res) properDeclPreserved
   have hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RunRouteEndpointIdsScoped inp o res := fun inp o res hwf hfp =>
     runRouteEndpointIdsScoped_of_keys (inp := inp) (o := o) (res := res) properDeclPreserved
       (properChainEndpointKeys' inp o res hwf hfp)
   have hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RoutePartShelfPositive inp o res := fun inp o res hwf hfp =>
     routePartShelfPositive_holds (inp := inp) (o := o) (res := res) hwf hfp
   have hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
       comp ∈ components execution.graph →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopReservation (componentCandidate execution.graph comp candidate) run
         execution.measured v :=
     fun inp o res execution hwf hfp comp candidate run v hcomp hrun =>
       loopReservation_executed execution comp candidate run v hcomp hrun
   have hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
       comp ∈ components execution.graph →
       ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
         execution.measured v b :=
    fun inp o res execution hwf hfp comp candidate run v b hcomp hbord hrun =>
      loopFootprintSeparation_executed execution comp candidate run v b hcomp hbord hrun
        (loopFootprintSeparationResidual (loopFootprintTopSeparation_closed inp o res hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp)) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp))
   have hstrictAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentStrictMissGroup group parent :=
    strictMiss_restricted_closed S.parentRouteAttachedClear hclear hnodeDecl hscoped
      hpos hloopRes hloopSep hflat8a parentFixedForeign_narrow_holds
   exact stepC6Geometry_closed hflat8a hclear hnodeDecl hscoped hpos hloopRes hloopSep
     parentFixedForeign_narrow_holds S.parentRouteAttachedClear hstrictAll

 /-- The old `stepC8bGeometry` fact derived from the narrow seams: the flat
 clauses from the border-span and label seams, the two parent-side residuals
 and the per-call fit from the fields. -/
theorem c8bGeometry_of_seams (S : LayeredSeams) :
    RecursiveStepFacts (fun P inp o group titleHeight parent child res =>
      InputFixedFit inp o → ExpandChildC8bGeometry P inp o group titleHeight
        parent child res) := by
   have hflat8a : FlatC8a := flatC8a_of_span_seams
     (foreignBorderSpansSeparated foreignClusterRankSpans'
       foreignBorderLayerOrder' (foreignBorderChainXAligned' S.foreignBorderDivergeStable))
     (foreignNonGroupSpansClear bracketMarkersAtRank'
       plainClearOfSideMarker' (sideMarkerSpanAligned' (foreignBorderChainXAligned' S.foreignBorderDivergeStable)))
     (fun inp o res hwf hfp =>
       bracketInsidePremises
         (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
         (fun execution => titleCopySpanClearStrict_executed hwf hfp execution))
   have hflat8b : FlatC8b := fun inp o res hwf hfp hfit h =>
     layout_c8b h hwf (fun execution => frameLabels_executed execution hwf hfp hfit
       (executedPartFrameCores_closed execution hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) (loopFootprintTopSeparation_closed inp o res hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp)) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp) (fun comp hcomp candidate run orderOptions hrun => hullCover_of_witness hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) execution hcomp hrun (loopResGroupHullRightWitness_closed' hwf hfp execution hcomp hrun)) (fun comp hcomp candidate run orderOptions hrun => neighborCover_of_disjoint_closed hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) execution hcomp hrun (loopResNeighborGapGroupTopDisj_holds hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) foreignBorderLayerOrder' execution hcomp hrun) (neighborGapBottomOwnerDisj_holds execution hcomp hrun)))
       (Elegant.Layered.fallbackOwnerFrameClear_executed execution hwf hfp
         (flatC8a_executed execution hwf hfp
           (foreignBorderSpansSeparated foreignClusterRankSpans'
             foreignBorderLayerOrder' (foreignBorderChainXAligned' S.foreignBorderDivergeStable))
           (foreignNonGroupSpansClear bracketMarkersAtRank'
             plainClearOfSideMarker' (sideMarkerSpanAligned' (foreignBorderChainXAligned' S.foreignBorderDivergeStable)))
           (fun inp o res hwf hfp =>
             bracketInsidePremises
               (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
               (fun execution => titleCopySpanClearStrict_executed hwf hfp execution)))
         (Elegant.Layered.fallbackOwnerStrictStep_executed execution hwf hfp)))
   exact stepC8bGeometry_holds hflat8a hflat8b S.parentFrameStrict parentStrictStep_of_recursion

 /-- The below-fuel C8b geometry from the seams, for the C7 derivation. -/
 theorem below8b_of_seams (S : LayeredSeams) (fuel : Nat) :
     ∀ (fuel' : Nat), fuel' < fuel → ∀ (P : Params) (inp : Input) (o : Options)
       (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
       (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel' P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       InputFixedFit inp o →
       ExpandChildC8bGeometry P inp o group titleHeight parent child res :=
   fun fuel' _ P inp o group tls th par chi res hx hf hc hp hfix =>
     c8bGeometry_of_seams S fuel' P inp o group tls th par chi res hx hf hc hp hfix

 /-- The old `stepC7Geometry` fact derived from the narrow seams: the flat
 clauses and below-fuel geometry as above, the two parent-side residuals and
 both fits from the fields. -/
theorem c7Geometry_of_seams (S : LayeredSeams) :
    RecursiveStepFacts (fun P inp o group titleHeight parent child res =>
      InputFixedFit inp o → ExpandChildC7Geometry P inp o group titleHeight
        parent child res) := by
   have hflat8a : FlatC8a := flatC8a_of_span_seams
     (foreignBorderSpansSeparated foreignClusterRankSpans'
       foreignBorderLayerOrder' (foreignBorderChainXAligned' S.foreignBorderDivergeStable))
     (foreignNonGroupSpansClear bracketMarkersAtRank'
       plainClearOfSideMarker' (sideMarkerSpanAligned' (foreignBorderChainXAligned' S.foreignBorderDivergeStable)))
     (fun inp o res hwf hfp =>
       bracketInsidePremises
         (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
         (fun execution => titleCopySpanClearStrict_executed hwf hfp execution))
   have hflat8b : FlatC8b := fun inp o res hwf hfp hfit h =>
     layout_c8b h hwf (fun execution => frameLabels_executed execution hwf hfp hfit
       (executedPartFrameCores_closed execution hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) (loopFootprintTopSeparation_closed inp o res hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp)) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp) (fun comp hcomp candidate run orderOptions hrun => hullCover_of_witness hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) execution hcomp hrun (loopResGroupHullRightWitness_closed' hwf hfp execution hcomp hrun)) (fun comp hcomp candidate run orderOptions hrun => neighborCover_of_disjoint_closed hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) execution hcomp hrun (loopResNeighborGapGroupTopDisj_holds hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) foreignBorderLayerOrder' execution hcomp hrun) (neighborGapBottomOwnerDisj_holds execution hcomp hrun)))
       (Elegant.Layered.fallbackOwnerFrameClear_executed execution hwf hfp
         (flatC8a_executed execution hwf hfp
           (foreignBorderSpansSeparated foreignClusterRankSpans'
             foreignBorderLayerOrder' (foreignBorderChainXAligned' S.foreignBorderDivergeStable))
           (foreignNonGroupSpansClear bracketMarkersAtRank'
             plainClearOfSideMarker' (sideMarkerSpanAligned' (foreignBorderChainXAligned' S.foreignBorderDivergeStable)))
           (fun inp o res hwf hfp =>
             bracketInsidePremises
               (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
               (fun execution => titleCopySpanClearStrict_executed hwf hfp execution)))
         (Elegant.Layered.fallbackOwnerStrictStep_executed execution hwf hfp)))
   exact stepC7Geometry_holds hflat8a hflat8b (below8b_of_seams S) S.parentFrameStrict
     parentStrictStep_of_recursion

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
  have hbracket : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      BracketInsidePremises inp o res := fun inp o res hwfInp hframedInp =>
    bracketInsidePremises
      (fun execution => dummyInsideProxyRowClear_executed' execution hwfInp hframedInp)
      (fun execution => titleCopySpanClearStrict_executed hwfInp hframedInp execution)
  have hframeLabels : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
      ∀ (execution : SceneExecution inp o res),
        LabelFramePackedClear execution.params inp o execution.lines execution.packedAcc ∧
          FallbackCaptionClear execution :=
     fun inp o res hwf hfp hfit execution =>
       frameLabels_executed execution hwf hfp hfit
         (executedPartFrameCores_closed execution hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) (loopFootprintTopSeparation_closed inp o res hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp)) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp) (fun comp hcomp candidate run orderOptions hrun => hullCover_of_witness hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) execution hcomp hrun (loopResGroupHullRightWitness_closed' hwf hfp execution hcomp hrun)) (fun comp hcomp candidate run orderOptions hrun => neighborCover_of_disjoint_closed hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) execution hcomp hrun (loopResNeighborGapGroupTopDisj_holds hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) foreignBorderLayerOrder' execution hcomp hrun) (neighborGapBottomOwnerDisj_holds execution hcomp hrun)))
         (Elegant.Layered.fallbackOwnerFrameClear_executed execution hwf hfp
           (flatC8a_executed execution hwf hfp
            (foreignBorderSpansSeparated foreignClusterRankSpans' foreignBorderLayerOrder' (foreignBorderChainXAligned' S.foreignBorderDivergeStable))
            (foreignNonGroupSpansClear bracketMarkersAtRank' plainClearOfSideMarker' (sideMarkerSpanAligned' (foreignBorderChainXAligned' S.foreignBorderDivergeStable)))
             hbracket)
           (Elegant.Layered.fallbackOwnerStrictStep_executed execution hwf hfp))
  have hflat6 : FlatC6 := flatC6_closed_nowit (fun inp o res hwf hfp => loopRectTopReal_closed hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable)) (fun inp o res hwf hfp => loopRectFixedReal_holds hwf hfp) (fun inp o res hwf hfp => loopRectTitleReal_holds hwf hfp (loopRectTitleCopy_closed inp o res hwf hfp)) (fun inp o res hwf hfp => loopRectBottomReal_holds hwf hfp) (fun inp o res hwf hfp => loopRectRangeDegReal_holds hwf hfp) (fun inp o res hwf hfp => loopFootprintTopSeparation_closed inp o res hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp)) (beyondProper_closed S.foreignBorderDivergeStable)
  have hflat8b : FlatC8b := fun inp o res hwf hfp hfit h =>
    layout_c8b h hwf (hframeLabels inp o res hwf hfp hfit)
  have hlabelRuns : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LabelRunsClearExclusiveBoxes inp o res := fun inp o res hwf hfp =>
    ⟨runLocalLabelClearance_holds hwf hfp
        (runLocalLoopSeparation inp o res (runLocalLoopFootprint_executed hwf hfp
          (loopFootprintTopSeparation_closed inp o res hwf hfp (foreignBorderChainXAligned' S.foreignBorderDivergeStable) (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp))
          (beyondProper_closed S.foreignBorderDivergeStable inp o res hwf hfp)))
        (runLocalForwardSeparation inp o res) (runLocalReversedSeparation inp o res),
      routeLabelDumpBridges hwf (labelBelongsToRun hwf routeLabelsPlaced)
        (exclusiveBoxInLabelRun' hwf hfp)⟩
  have hcaptions : ∀ (inp : Input) (o : Options) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o → SceneCaptionBoxContainment inp o res := fun inp o res hwf hfp hfit => sceneCaptionBoxContainment_of_fit hwf hfp hfit (titleExclusiveSamePart_holds (foreignBorderChainXAligned' S.foreignBorderDivergeStable) inp o res hwf hfp) (titleExclusiveCrossPart (inp := inp) (o := o) (res := res)) (hframeLabels inp o res hwf hfp hfit)
  have hstepC6 : RecursiveStepFacts ExpandChildC6Step :=
    expandChild_c6_step_of_geometry (c6Geometry_of_seams S) stepC6Anchors_holds
  have hstepC7 : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true → BoxRouteIdsDisjoint inp → InputFixedFit inp o →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7Step P inp o group titleHeight parent child res :=
    by
    intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hdisjoint hfix hctx hparams
    intro frame tl dx dy hframe hdx hdy hwrap
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
      expandChild_c7_structure fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx
        (expandChild_label_owners fuel P inp o group titleLines titleHeight parent child res
          hexpand hframed hctx hparams)
        (expandChild_c7_label_scopes_of_disjoint hexpand hframed hctx hparams hdisjoint
          (stepC8aAncestry_holds fuel P inp o group titleLines titleHeight parent child res
            hexpand hframed hctx hparams))
        frame tl dx dy hframe hdx hdy hwrap
    obtain ⟨g1, g2, g3, g4⟩ :=
      (c7Geometry_of_seams S) fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams hfix frame tl dx dy hframe hdx hdy hwrap
    exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, g1, g2, g3, g4⟩
  have hstepC8a : RecursiveStepFacts ExpandChildC8aStep :=
    expandChild_c8a_step_of_geometry stepC8aGeometry_holds
      (fun fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx
          hparams =>
        expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
          hexpand hframed hctx
          (stepC8aAncestry_holds fuel P inp o group titleLines titleHeight parent child res
            hexpand hframed hctx hparams))
  have hstepC8b : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true → InputFixedFit inp o →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStep P inp o group titleHeight parent child res := by
    intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hfix hctx hparams
    intro frame tl dx dy hframe hdx hdy hwrap
    obtain ⟨g1, g2, g3, g4⟩ :=
      (c8bGeometry_of_seams S) fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams hfix frame tl dx dy hframe hdx hdy hwrap
    exact ⟨expandChild_c8b_structure fuel P inp o group titleLines titleHeight parent child
        res hexpand hframed hctx
        (expandChild_label_owners fuel P inp o group titleLines titleHeight parent child
          res hexpand hframed hctx hparams) frame tl dx dy hframe hdx hdy hwrap,
      g1, g2, g3, g4⟩
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
    layoutRecursive_c7_of_flat_fit hflat7 (fun _ _ _ => labelsC7_partsSeparated) hlabelRuns
      hcaptions subInputWellFormed hstepC7
      (inp.boxes.length + 1) inp o res hwf hfp hfix hdisj hrec,
    layoutRecursive_c8a_of_flat (flatC8a_of_span_seams (foreignBorderSpansSeparated foreignClusterRankSpans' foreignBorderLayerOrder' (foreignBorderChainXAligned' S.foreignBorderDivergeStable)) (foreignNonGroupSpansClear bracketMarkersAtRank' plainClearOfSideMarker' (sideMarkerSpanAligned' (foreignBorderChainXAligned' S.foreignBorderDivergeStable))) hbracket)
      subInputsWellFormed hstepC8a
      (inp.boxes.length + 1) inp o res hwf hfp hrec,
    layoutRecursive_c8b_of_flat_fit hflat8b subInputsWellFormed hstepC8b
      (inp.boxes.length + 1) inp o res hwf hfp hfix hrec⟩

end Elegant.Layered.PipelineImpl

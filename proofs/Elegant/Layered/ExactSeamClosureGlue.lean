import Elegant.Layered.ExactCaptionScopeFitWProof
import Elegant.Layered.ExactFlatC6ShelfBorderProof
import Elegant.Layered.ExactCaptionFitFactsProof
import Elegant.Layered.ExactFlatC8aCore
import Elegant.Layered.ExactCaptionRunClearWProof
import Elegant.Layered.ExactCaptionSelfNarrowProof
import Elegant.Layered.ExactCaptionSelfBottomProof
import Elegant.Layered.ExactCaptionCapBandProof
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExactPartFrameCoresWProof
import Elegant.Layered.ExactForwardClearWProof
import Elegant.Layered.ExactForwardClearFactsProof
import Elegant.Layered.ExactForwardDummyFactsProof
import Elegant.Layered.ExactRouteNonforwardClearProof
import Elegant.Layered.ExactLoopEnvelopeMissProof
import Elegant.Layered.ExactLoopEnvelopeFootBelowProof
import Elegant.Layered.ExactLoopEnvelopeSidesProof
import Elegant.Layered.ExactLoopEnvelopeGroupMissProof
import Elegant.Layered.ExactLoopEnvelopeRightProof
import Elegant.Layered.ExactLoopEnvelopeReserveProof
import Elegant.Layered.ExactLoopEnvelopeLeftNonPlainProof
import Elegant.Layered.ExactStepLeafFactsProof
 import Elegant.Layered.ExactStepGeometryProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact seam closure glue: named step-geometry residuals.

The three `stepC*Geometry_layoutX` assemblers
(`ExactStepGeometryProof.lean`) take their open per-call premises as anonymous
`∀`-types. `Kinds/UsecaseValidExact.lean` needs strictly narrower PUBLIC named
defs for those premises, so they are named here, copied verbatim from the
theorem binders (each carries the local `framedParents` premise and the local
`WellFormed` fact inside `ExpandChildCallContextB`). Premises already proved in
`ExactStepGeometryProof.lean` (`XG_child_boxes_insetB`, `XG_frame_posB`,
`XG_child_routes_insetB`, `XG_content_fit_strict`) or closed elsewhere
(`stepC6Anchors_layoutX`, `stepC8aAncestry_layoutX`, both
`ExactStepShortFacts.lean`) are discharged at the use site, not renamed here;
the `XG_C8bCoreB` inset core is already a named def and is reused directly.
-/

/-- Open C6 residual: the located group frame misses every foreign exclusive
parent box. Verbatim copy of `hDisjB` in `stepC6Geometry_layoutX`. -/
def XG_StepC6DisjB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
      pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
      Disjoint frame.rect pb.rect

/-- Open C6 residual: no parent route hits any rect strictly inside the
located group frame. Verbatim copy of `hMissB` in `stepC6Geometry_layoutX`. -/
def XG_StepC6MissB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
      ¬ Polyline.hitsRect pr.points r

/-- Open C7 residual: shifted child boxes and labels lie in the located group
frame. Verbatim copy of `hchildB` in `stepC7Geometry_layoutX`. -/
def XG_StepC7ChildB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7ChildInside P inp o group titleHeight parent child

/-- Open C7 residual: the located group frame is clear of foreign parent boxes
and parent labels. Verbatim copy of `hparentB` in `stepC7Geometry_layoutX`. -/
def XG_StepC7ParentB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7ParentClear P inp o group titleHeight parent

/-- Open C7 residual: group-owned result labels fit the title band clear of
exclusive child boxes. Verbatim copy of `hcaptionB` in
`stepC7Geometry_layoutX`. -/
def XG_StepC7CaptionB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7CaptionFit P inp o group titleHeight parent child res

/-- Open C8b residual: child labels lie in the margin inset of the child
canvas. Verbatim copy of `hChildLabelsB` in `stepC8bGeometry_layoutX` (the
companion box fact is the proved `XG_child_boxes_insetB`). -/
def XG_StepC8bChildLabelsB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect

/-- Open C8b residual: the C8 title rect misses the shifted child margin
inset. Verbatim copy of `hCapDisjB` in `stepC8bGeometry_layoutX`. -/
def XG_StepC8bCapDisjB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    Disjoint (groupTitleRectC8 group P titleLines' titleHeight frame)
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin))
/-- Open C8b residual: the located group frame strictly contains the shifted
C8 title rect. Verbatim copy of `hCapStrictB` in `stepC8bGeometry_layoutX`. -/
def XG_StepC8bCapStrictB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    frame.rect.StrictInside (groupTitleRectC8 group P titleLines' titleHeight frame)

/-- Open C8b residual: the exact call preserves the parent frame placement.
Verbatim copy of `hParentFrameB` in `stepC8bGeometry_layoutX`. -/
def XG_StepC8bParentFrameB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildParentFrame P inp o group titleHeight parent child

/-- Discharged C8b premise: the child margin inset lands strictly inside the
located group frame. Specialization of the proved `XG_content_fit_strict` to
the inset rect itself (via `Contained.refl`), matching `hFitStrictB` in
`stepC8bGeometry_layoutX` so the use site needs no extra field. -/
theorem XG_fitStrictB_of_content (exactIds : List String) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
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
        (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams frame titleLines' dx dy hframe hdx hdy hwrap
  have hr : (⟨P.canvasMargin, P.canvasMargin,
      child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained
      (insetRect child.scene.canvas P.canvasMargin) := by
    unfold insetRect
    exact Rect.Contained.refl _
  exact XG_content_fit_strict exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams frame titleLines' dx dy
    hframe hdx hdy hwrap _ hr

def X6_PartPosW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hfix : FixedSizesPositive inp)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? =
      some edge),
    0 < q.1.2.width ∧ 0 < q.1.2.height

/-- Shelf positivity from part-size positivity: replay of
`X6_shelfPositiveW_of_partPos_holds` over the part-size residual. -/
theorem X6_shelfPositiveW_of_partPosW (exactIds : List String)
    (hpart : X6_PartPosW exactIds) :
    X6_ShelfPositiveW exactIds := by
  intro inp o res execution hfix hwf hfp packed hpacked c q hsel candidate i edge hedge
  obtain ⟨hW, hH⟩ := hpart execution hfix hwf hfp packed hpacked hsel hedge
  exact X6_shelfPositiveW_of_partPos_holds exactIds execution hwf hfp packed hpacked hsel hedge hW hH

/-- Assembled W caption scope clearance: replay of
`X_captionScopeClearanceFitW_holds` over the four W leaves; the
node-border premise is the closed `x_ownerResNodeBorderZeroX_holds`. -/
theorem glue_captionScopeFitW (exactIds : List String)
    (hdesc : X_CaptionDescendantSamePartClearW exactIds)
    (hcontainW : X_OwnerCaptionContainFallbackFitW exactIds)
    (hownersW : X_OwnerScopeSamePartClearW exactIds)
    (htitle : X_CaptionTitleBranchClearW exactIds) :
    X_CaptionScopeClearanceFitW exactIds :=
  X_captionScopeClearanceFitW_holds exactIds hdesc hcontainW hownersW htitle
    (x_ownerResNodeBorderZeroX_holds exactIds)

/-- Assembled W caption run clearance: replay of
`XF_captionRunClearXW_of_linkW` over the nine open leaves; the seven proved
premises are discharged by the closed narrow holds. The group-link premise
is the W form `XCA_GroupLinkXW`, closed premise-free by
`XCA_groupLinkXW_closed`. -/
theorem glue_captionRunClearXW (exactIds : List String)
    (hlinkW : XCA_GroupLinkXW exactIds)
    (hbelow : XCA_MarkerBelowX exactIds)
    (himpossible : XCA_PlainAncestorImpossibleX exactIds)
    (hspans : XB_ForeignClusterRankSpans exactIds)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (halignB : XB_ForeignBorderChainXAligned exactIds)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplainXN : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds) :
    XF_CaptionRunClearXW exactIds :=
  XF_captionRunClearXW_of_linkW exactIds
    (XC_selfSidesLeftNarrowX_holds exactIds)
    (XC_selfSidesRightNarrowX_holds exactIds)
    (XC_selfBottomHeightNarrowX_holds exactIds)
    (XC_capBandX_holds exactIds)
    hlinkW hbelow himpossible hspans horder halignB
    (XB_orderedIntervals_holds exactIds)
    (XB_topNonneg_holds exactIds)
    (XB_memberNonempty_holds exactIds)
    hbracket hplainXN halignN

/-- Assembled W seams-imply-foreign: replay of
`XFR_seamsImplyForeignXW_holds` over the six open span leaves. -/
theorem glue_seamsImplyForeignXW (exactIds : List String)
    (hspans : XB_ForeignClusterRankSpans exactIds)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (halignB : XB_ForeignBorderChainXAligned exactIds)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplain : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds) :
    XFR_SeamsImplyForeignXW exactIds :=
  XFR_seamsImplyForeignXW_holds exactIds hspans horder halignB hbracket hplain
    halignN

/-- Assembled W route-label foreign clearance: replay of
`XFR_routeLabelForeignClearXW_holds` over the four open leaves. -/
theorem glue_routeLabelForeignClearXW (exactIds : List String)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplain : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds)
    (hchain : X_ForeignBorderChainXAligned exactIds) :
    XFR_RouteLabelForeignClearXW exactIds :=
  XFR_routeLabelForeignClearXW_holds exactIds hbracket hplain halignN hchain

/-- Assembled nonforward route-label clearance: replay of
`XF_routeNonforwardClearX_holds` over the two open leaves. -/
theorem glue_nonforward (exactIds : List String)
    (hmiss : XNonfwd_ExtMiss exactIds)
    (hhull : XNonfwd_GroupHullExt exactIds) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate)
        execution.measured orderOptions = .ok run →
      RouteNonforwardLabelClear execution.params
        (componentCandidate execution.graph comp candidate) run
        execution.measured :=
  XF_routeNonforwardClearX_holds exactIds hmiss hhull

/-- Assembled W leftover-pair clearance: replay of
`XFR_routeLabelLeftoverPairXW_holds` over the open leaves; the dummy-label
premise is the closed `XFR_dummyExLabeledX_holds`. -/
theorem glue_routeLeftoverPairXW (exactIds : List String)
    (hstrict : XFR_StrictDummyLinkedX exactIds)
    (hforeign : XFR_RouteLabelForeignClearXW exactIds)
    (hnonfwd : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate)
        execution.measured orderOptions = .ok run →
      RouteNonforwardLabelClear execution.params
        (componentCandidate execution.graph comp candidate) run
        execution.measured)
    (himp : XFR_SeamsImplyForeignXW exactIds)
    (hxalign : ForeignBorderChainXAligned)
    (hscopeFree : XFR_ForwardScopeFreeX exactIds) :
    XFR_RouteLabelLeftoverPairXW exactIds :=
  XFR_routeLabelLeftoverPairXW_holds exactIds hstrict hforeign hnonfwd
    (XFR_dummyExLabeledX_holds exactIds) himp hxalign hscopeFree

/-- Assembled W forward route clearance: replay of
`XF_routeForwardClearX_holds` over the open leaves; the dummy/in-dummy
premises are the closed `XFR_dummyExLabeledX_holds` and
`XFR_routeLabelInDummyX_holds`. -/
theorem glue_routeForwardClearXW (exactIds : List String)
    (hstrict : XFR_StrictDummyLinkedX exactIds)
    (hreal : XFR_RouteLabelRealClearX exactIds)
    (hforeign : XFR_RouteLabelForeignClearXW exactIds)
    (hleftover : XFR_RouteLabelLeftoverPairXW exactIds)
    (himp : XFR_SeamsImplyForeignXW exactIds)
    (hxalign : ForeignBorderChainXAligned) :
    XF_RouteForwardClearXW exactIds :=
  XF_routeForwardClearXW_holds exactIds hstrict
    (XFR_routeLabelInDummyX_holds exactIds) hreal hforeign hleftover
    (XFR_dummyExLabeledX_holds exactIds) hxalign himp

/-- Assembled W route run clearance: replay of `XF_routeRunClearX_holds`
over the assembled forward clearance and the nonforward case. -/
theorem glue_routeRunClearXW (exactIds : List String)
    (hfwd : XF_RouteForwardClearXW exactIds)
    (hnonfwd : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate)
        execution.measured orderOptions = .ok run →
      RouteNonforwardLabelClear execution.params
        (componentCandidate execution.graph comp candidate) run
        execution.measured) :
    XF_RouteRunClearXW exactIds :=
  XF_routeRunClearXW_holds exactIds hfwd hnonfwd

/-- Assembled loop-envelope miss: replay of `X_loopEnvelopeMiss_closed`
over the six open leaves; the other-rank miss is closed by
`XLEM_otherRankMiss_closed`, the left miss by `XLEM_leftMiss_holds`, and
the group-owner miss by `XLEM_groupOwnerMiss_holds`. -/
theorem glue_loopEnvelopeMiss (exactIds : List String)
    (hres : XLEM_PlainReserve exactIds)
    (hgrp : XLEM_GroupOwnerOtherRank exactIds)
    (hleftNP : XLEM_LeftNonPlain exactIds)
    (hright : XLEM_PlainRightMiss exactIds)
    (hgrpOrd : XLEG_GroupMarkerOrderX exactIds)
    (howner : X_loopEnvOtherOwner exactIds) :
    X_LoopEnvelopeMiss exactIds :=
  X_loopEnvelopeMiss_closed exactIds
    (XLEM_otherRankMiss_closed exactIds hres hgrp)
    hright
    (XLEM_leftMiss_holds exactIds hleftNP)
    (XLEM_groupOwnerMiss_holds exactIds hgrpOrd)
    howner

/-- Assembled W executed part-frame cores: replay of
`X_executedPartFrameCores_holds` over the assembled caption and route run
residuals. The plain alignment is fed by the caller from the kept
`foreignBorderDivergeStable` field; the loop miss is the assembled
`glue_loopEnvelopeMiss`. The group-link premise is the W form. -/
theorem glue_partFrameCoresW (exactIds : List String)
    (hlinkW : XCA_GroupLinkXW exactIds)
    (hbelow : XCA_MarkerBelowX exactIds)
    (himpossible : XCA_PlainAncestorImpossibleX exactIds)
    (hspans : XB_ForeignClusterRankSpans exactIds)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (halignB : XB_ForeignBorderChainXAligned exactIds)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplainXN : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds)
    (hchainX : X_ForeignBorderChainXAligned exactIds)
    (hstrict : XFR_StrictDummyLinkedX exactIds)
    (hscopeFree : XFR_ForwardScopeFreeX exactIds)
    (hmissN : XNonfwd_ExtMiss exactIds)
    (hhullN : XNonfwd_GroupHullExt exactIds)
    (hxalign : ForeignBorderChainXAligned)
    (hmiss : X_LoopEnvelopeMiss exactIds) :
    X_ExecutedPartFrameCoresB8W exactIds :=
  X_executedPartFrameCoresW_holds exactIds
    (glue_captionRunClearXW exactIds hlinkW hbelow himpossible hspans horder
      halignB hbracket hplainXN halignN)
    (glue_routeRunClearXW exactIds
      (glue_routeForwardClearXW exactIds hstrict
        (XFR_routeLabelRealClearX_holds exactIds hmiss)
        (glue_routeLabelForeignClearXW exactIds hbracket hplainXN halignN
          hchainX)
        (glue_routeLeftoverPairXW exactIds hstrict
          (glue_routeLabelForeignClearXW exactIds hbracket hplainXN halignN
            hchainX)
          (glue_nonforward exactIds hmissN hhullN)
          (glue_seamsImplyForeignXW exactIds hspans horder halignB hbracket
            hplainXN halignN)
          hxalign hscopeFree)
        (glue_seamsImplyForeignXW exactIds hspans horder halignB hbracket
          hplainXN halignN)
        hxalign)
      (glue_nonforward exactIds hmissN hhullN))

/-- Closed C8b caption-disjointness residual: replay of `XSGL_stepC8bCapDisj`
with the executed-run binders reintroduced. Discharges the `stepC8bCapDisj`
field of `ExactSeams`. -/
theorem glue_stepC8bCapDisjB (exactIds : List String) :
    XG_StepC8bCapDisjB exactIds := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  exact XSGL_stepC8bCapDisj exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams

/-- Closed C8b caption-strictness residual: replay of `XSGL_stepC8bCapStrict`
with the executed-run binders reintroduced. Discharges the `stepC8bCapStrict`
field of `ExactSeams`. -/
theorem glue_stepC8bCapStrictB (exactIds : List String) :
    XG_StepC8bCapStrictB exactIds := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  exact XSGL_stepC8bCapStrict exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams

/-- Assembled C8b inset core: replay of `XSGL_c8bCore` with the executed-run
binders reintroduced. The inner premises are exactly the core binders, so no
`ExactSeams` field is needed. Discharges the `stepC8bCore` field. -/
theorem glue_stepC8bCoreB (exactIds : List String) :
    XG_C8bCoreB exactIds := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams hChildBoxes hChildLabels hFitStrict
    hCapStrict hCapDisj hAnc hParentFrame
  exact XSGL_c8bCore exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams hChildBoxes hChildLabels
    hFitStrict hCapStrict hCapDisj hAnc hParentFrame


/-- Assembled other-owner miss from the four intermediate misses: the
other-rank miss (plain reserve closed, group rank from the kept overlap
residual), the right miss (kept right-nonplain residual), the left miss
(left non-plain closed), and the group miss (kept marker order).
Discharges the `loopOwner` field of `ExactSeams`. -/
theorem glue_loopEnvOtherOwner (exactIds : List String)
    (hgrp : XLEM_GroupOverlapMiss exactIds)
    (hRightNP : XLEM_PlainRightNonPlain exactIds)
    (hgrpOrd : XLEG_GroupMarkerOrderX exactIds) :
    X_loopEnvOtherOwner exactIds :=
  X_loopEnvOtherOwner_of_parts exactIds
    (XLEM_otherRankMiss_closed exactIds (XLEM_plainReserve_holds exactIds)
      (XLEM_groupOtherRank_holds exactIds hgrp))
    (XLEM_plainRightMiss_holds exactIds hRightNP)
    (XLEM_leftMiss_holds exactIds (XLEM_leftNonPlain_holds exactIds))
    (XLEM_groupOwnerMiss_holds exactIds hgrpOrd)
end PipelineImpl
end Layered
end Elegant

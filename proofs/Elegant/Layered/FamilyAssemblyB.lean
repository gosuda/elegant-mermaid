import Elegant.Layered.FamilyAssembly
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.FamilyC5B
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.InsetFit
import Elegant.Layered.ExecutedPortsFacts
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
import Elegant.Layered.SceneBounds
import ElegantGeometry.Validator
import Elegant.Layered.FlatC8aExecutedProof
import Elegant.Layered.FallbackOwnerFrameProof
import Elegant.Layered.FallbackOwnerStrictStepProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.ExpandChildC8aGeometryExecuted

set_option autoImplicit false
namespace Elegant.Layered.PipelineImpl

/-- Every hypothesis the base-parametric family validity theorem takes: one
field per hypothesis the `layoutRecursiveB` lifts consume.  The flat facts
(`flatInset`, `flatC3`, `flatC2`, `flatC4`, `flatC5`, `flatC6`, `flatC7`,
`flatC8a`, `flatC8b`) are the `Flat*B base` copies; the four seam fields
(`frameClear`, `partsSep`, `labelRuns`, `captions`) discharge the side
premises the flat facts and lifts take (`FrameClearanceSeam`,
`PartsSeparated`, `LabelRunsClearExclusiveBoxes`,
`SceneCaptionBoxContainment`), with `captions` and the `FlatC8bB` copy also
taking the fixed-size premise `InputFixedFit inp o` the C7/C8b lifts thread.
`canvasMargins` is the per-fuel canvas-margin bound the C7/C8b lifts need for
the fresh fixed size.  The sub-input facts are kept in both forms
the lifts take: `subInputC2` is the plain `SubInputWellFormedC2` the inset,
C1/C3, and C2 lifts (`layoutRecursiveB_inset`, `layoutRecursiveB_c1_c3`,
`layoutRecursiveB_c2`) consume, while `subInputB` is the base-parametric
`SubInputWellFormedB base` the C6, C7, C8a, C8b, and C5 lifts consume.
`fitClosed` is the per-call fit/closure fact the inset and C1/C3 lifts need,
and the five `step` fields are the per-call step facts in the shape the
lifts take (`ExpandChildCallContextB base ... → ExpandChildCallParams ...
→ Step`), with `stepC7` also taking the route-id disjointness premise
`BoxRouteIdsDisjoint inp`. -/
structure BaseSeams (base : Input → Options → Except LayoutError FamilyResult) : Prop where
  flatInset : FlatInsetB base
  flatC3 : FlatC3B base
  flatC2 : FlatC2B base
  flatC4 : FlatC4B base
  flatC5 : FlatC5B base
  flatC6 : FlatC6B base
  flatC7 : FlatC7B base
  flatC8a : FlatC8aB base
  flatC8b : FlatC8bB base
  canvasMargins : CanvasMarginsB base
  frameClear :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      FrameClearanceSeam inp o res
  partsSep :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      Elegant.Layered.PartsSeparated inp o res
  labelRuns :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LabelRunsClearExclusiveBoxes inp o res
  captions :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
      SceneCaptionBoxContainment inp o res
  subInputC2 : SubInputWellFormedC2
  subInputB : SubInputWellFormedB base
  fitClosed : ExpandChildFitClosedB base
  stepC2 :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      (∀ m ∈ inp.boxes, m.id ≠ "") →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC2Step P inp o group titleHeight parent child res
  stepC6 :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Step P inp o group titleHeight parent child res
  stepC7 :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true → BoxRouteIdsDisjoint inp →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7Step P inp o group titleHeight parent child res
  stepC8a :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStep P inp o group titleHeight parent child res
  stepC8b :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStep P inp o group titleHeight parent child res

/-- Base-parametric recursion validity at any fuel, modulo `BaseSeams`: the
conjunction the lifts give.  The C5 slot carries the recursive group-endpoint
invariant; the full C5 clause comes through the family theorem. -/
theorem layoutRecursiveB_valid_of_seams {base : Input → Options → Except LayoutError FamilyResult}
    (S : BaseSeams base) (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (hfix : InputFixedFit inp o) (hdisj : BoxRouteIdsDisjoint inp)
    (h : layoutRecursiveB base fuel inp o = .ok res) :
    Validator.C1 res.scene.layoutDump ∧ Validator.C2 res.scene.layoutDump ∧
      Validator.C3 res.scene.layoutDump ∧ Validator.C4 res.scene.layoutDump ∧
      GroupEndpointInvariantMeasured inp res.scene ∧
      Validator.C6 res.scene.layoutDump ∧ Validator.C7 res.scene.layoutDump ∧
      Validator.C8a res.scene.layoutDump ∧ Validator.C8b res.scene.layoutDump := by
  obtain ⟨hc1, hc3⟩ :=
    layoutRecursiveB_c1_c3 base S.flatInset S.flatC3 S.subInputC2 S.fitClosed
      fuel inp o res hwf hfp h
  exact ⟨hc1,
    layoutRecursiveB_c2 base S.flatC2 S.subInputC2 S.stepC2
      fuel inp o res hwf hfp hids h,
    hc3,
    layoutRecursiveB_c4 base S.flatC4 fuel inp o res hwf hfp h,
    (layoutRecursiveB_c5_facts S.flatC5 S.subInputB fuel hwf hfp h).2.2,
    layoutRecursiveB_c6 base S.flatC6 S.frameClear S.subInputB S.stepC6
      fuel inp o res hwf hfp h,
    layoutRecursiveB_c7 base S.flatC7 S.canvasMargins S.partsSep S.labelRuns S.captions
      S.subInputB S.stepC7 fuel inp o res hwf hfp hfix hdisj h,
    layoutRecursiveB_c8a base S.flatC8a S.subInputB S.stepC8a
      fuel inp o res hwf hfp h,
    layoutRecursiveB_c8b base S.flatC8b S.canvasMargins S.subInputB S.stepC8b
      fuel inp o res hwf hfp hfix h⟩

/-- Base-parametric family validity, mirroring `layoutFamily_valid_of_seams`:
the family guards supply `WellFormed` (`layoutFamilyB_success`) and
`framedParents` (`layoutFamilyB_framed_parents`). -/
theorem layoutFamilyB_valid_of_seams
    {base : Input → Options → Except LayoutError FamilyResult}
    (S : BaseSeams base) {inp : Input} {o : Options} {res : FamilyResult}
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (hfix : InputFixedFit inp o) (hdisj : BoxRouteIdsDisjoint inp)
    (h : layoutFamilyB base inp o = .ok res) :
    HardConstraints res.scene.layoutDump := by
  obtain ⟨hwf, hrec⟩ := layoutFamilyB_success h
  have hfp := layoutFamilyB_framed_parents h
  exact ⟨
    (layoutRecursiveB_c1_c3 base S.flatInset S.flatC3 S.subInputC2 S.fitClosed
      (inp.boxes.length + 1) inp o res hwf hfp hrec).1,
    layoutRecursiveB_c2 base S.flatC2 S.subInputC2 S.stepC2
      (inp.boxes.length + 1) inp o res hwf hfp hids hrec,
    (layoutRecursiveB_c1_c3 base S.flatInset S.flatC3 S.subInputC2 S.fitClosed
      (inp.boxes.length + 1) inp o res hwf hfp hrec).2,
    layoutRecursiveB_c4 base S.flatC4 (inp.boxes.length + 1) inp o res hwf hfp hrec,
    layoutFamilyB_c5 S.flatC5 S.subInputB h,
    layoutRecursiveB_c6 base S.flatC6 S.frameClear S.subInputB S.stepC6
      (inp.boxes.length + 1) inp o res hwf hfp hrec,
    layoutRecursiveB_c7 base S.flatC7 S.canvasMargins S.partsSep S.labelRuns S.captions
      S.subInputB S.stepC7 (inp.boxes.length + 1) inp o res hwf hfp hfix hdisj hrec,
    layoutRecursiveB_c8a base S.flatC8a S.subInputB S.stepC8a
      (inp.boxes.length + 1) inp o res hwf hfp hrec,
    layoutRecursiveB_c8b base S.flatC8b S.canvasMargins S.subInputB S.stepC8b
      (inp.boxes.length + 1) inp o res hwf hfp hfix hrec⟩

/-- Every `BaseSeams layout` field follows from `LayeredSeams` by the same
discharges `layoutFamily_valid_of_seams` uses: the `flat*B_of_flat`
sanities, `flatC5B_of_endpoints`, `expandChildCallContext_iff`, the proved
step and sub-input facts (`subInputWellFormedC2`, `subInputWellFormed`,
`hgeo_of_recursion`), the executed bracket discharges
(`dummyInsideProxyRowClear_executed'`, `titleCopySpanClearStrict_executed`),
the closed span seams (`foreignBorderLayerOrder'`, `plainClearOfSideMarker'`,
`sideMarkerSpanAligned'`), the proved label-owner step
(`expandChild_label_owners`), the per-call label scopes
(`expandChild_c7_label_scopes_of_disjoint`), the closed route-label fact
(`routeLabelsPlaced`), the closed group endpoint ranks
(`groupTopSubtreeRankProper'`, `groupBottomBoundaryFacts_of_dummy`), the
canvas-margin bound (`layoutRecursive_canvas_margins` through
`layoutRecursive_eq_B` and `checkedParams_canvasMargin`), and
`ExpandChildFitClosedB layout` from the plain fit
lemmas (`layoutRecursive_childInset_fits_frame`,
`layoutRecursive_parent_closed_wellFormed`) through `layoutRecursive_eq_B`. -/
theorem baseSeams_of_layered (S : LayeredSeams) : BaseSeams layout where
  flatInset := flatInsetB_of_flat (fun inp o res h => layout_inset h)
  flatC3 := flatC3B_of_flat (fun inp o res hwf hfp h => layout_c3 h hwf hfp)
  flatC2 := flatC2B_of_flat (fun inp o res hwf h => layout_c2 h hwf)
  flatC4 := flatC4B_of_flat (fun inp o res h route hroute =>
    (Classical.choice (layout_sceneExecution h)).routes_orthogonal route hroute)
  flatC5 := flatC5B_of_endpoints
    (flatGroupEndpoints groupTopSubtreeRankProper'
      (groupBottomBoundaryFacts_of_dummy bottomDummyRankLe)
      groupTailPortOnYs groupAnchorSelection)
  flatC6 := flatC6_closed S.partFrameWitness S.loopRectTopReal S.loopRectFixedReal
    S.loopRectTitleReal S.loopRectBottomReal S.loopRectRangeDegReal
    S.loopFootprintTopSeparation S.loopFootprintBeyondProper
  flatC7 := fun inp o res hwf hfp hsep hseam1 hseam2 hb =>
    layout_c7 hwf hfp hsep hseam1 hseam2 hb
  flatC8a := flatC8a_of_span_seams
    (foreignBorderSpansSeparated foreignClusterRankSpans'
      foreignBorderLayerOrder' S.foreignBorderChainXAligned)
    (foreignNonGroupSpansClear bracketMarkersAtRank'
      plainClearOfSideMarker' (sideMarkerSpanAligned' S.foreignBorderChainXAligned))
    (fun inp o res hwf hfp =>
      bracketInsidePremises
        (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
        (fun execution => titleCopySpanClearStrict_executed hwf hfp execution))
  frameClear := fun inp o res hwf hfp =>
    frameClearanceSeam_holds
      (bracketInsidePremises
        (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
        (fun execution => titleCopySpanClearStrict_executed hwf hfp execution))
  flatC8b := fun inp o res hwf hfp hfit hb =>
    layout_c8b hb hwf (fun execution => frameLabels_executed execution hwf hfp hfit
      (S.executedPartFrameCores inp o res hwf hfp execution)
      (Elegant.Layered.fallbackOwnerFrameClear_executed execution hwf hfp
        (flatC8a_executed execution hwf hfp
          (foreignBorderSpansSeparated foreignClusterRankSpans'
            foreignBorderLayerOrder' S.foreignBorderChainXAligned)
          (foreignNonGroupSpansClear bracketMarkersAtRank'
            plainClearOfSideMarker' (sideMarkerSpanAligned' S.foreignBorderChainXAligned))
          (fun inp o res hwf hfp =>
            bracketInsidePremises
              (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
              (fun execution => titleCopySpanClearStrict_executed hwf hfp execution)))
        (Elegant.Layered.fallbackOwnerStrictStep_executed execution hwf hfp)))
  canvasMargins := fun fuel inp o res h P hP => by
    have hm := layoutRecursive_canvas_margins fuel (by rw [layoutRecursive_eq_B]; exact h)
    rw [checkedParams_canvasMargin hP]
    exact hm
  labelRuns := fun inp o res hwf hfp =>
    ⟨runLocalLabelClearance_holds hwf hfp
        (runLocalLoopSeparation inp o res (runLocalLoopFootprint_executed hwf hfp
          (S.loopFootprintTopSeparation inp o res hwf hfp)
          (S.loopFootprintBeyondProper inp o res hwf hfp)))
        (runLocalForwardSeparation inp o res) (runLocalReversedSeparation inp o res),
      routeLabelDumpBridges hwf (labelBelongsToRun hwf routeLabelsPlaced)
        (exclusiveBoxInLabelRun' hwf hfp)⟩
  partsSep := fun _ _ _ => labelsC7_partsSeparated
  captions := fun inp o res hwf hfp hfit =>
    sceneCaptionBoxContainment_of_fit hwf hfp hfit
      (S.titleExclusiveSamePart inp o res hwf hfp)
      (titleExclusiveCrossPart (inp := inp) (o := o) (res := res))
      (fun execution => frameLabels_executed execution hwf hfp hfit
        (S.executedPartFrameCores inp o res hwf hfp execution)
        (Elegant.Layered.fallbackOwnerFrameClear_executed execution hwf hfp
          (flatC8a_executed execution hwf hfp
            (foreignBorderSpansSeparated foreignClusterRankSpans'
              foreignBorderLayerOrder' S.foreignBorderChainXAligned)
            (foreignNonGroupSpansClear bracketMarkersAtRank'
              plainClearOfSideMarker' (sideMarkerSpanAligned' S.foreignBorderChainXAligned))
            (fun inp o res hwf hfp =>
              bracketInsidePremises
                (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
                (fun execution => titleCopySpanClearStrict_executed hwf hfp execution)))
          (Elegant.Layered.fallbackOwnerStrictStep_executed execution hwf hfp)))
  subInputC2 := subInputWellFormedC2
  subInputB := by
    intro fuel inp o group P metric titleLines child parent hwf hfp hP hm hwrap
      hchildB hparentB
    have hchild :
        layoutRecursive fuel (childSubInput inp group)
          (childSubOptions o group) = .ok child := by
      rw [layoutRecursive_eq_B]; exact hchildB
    have hparent :
        layoutRecursive fuel (parentSubInput inp group P titleLines child) o =
          .ok parent := by
      rw [layoutRecursive_eq_B]; exact hparentB
    exact subInputWellFormed fuel inp o group P metric titleLines child parent
      hwf hfp hP hm hwrap hchild hparent
  fitClosed := by
    intro fuel P inp o group titleLines titleHeight parent child res hexpand
      hctxB hparams
    obtain ⟨hP, htitleH, hwrap⟩ := hparams
    subst htitleH
    have hctx :
        ExpandChildCallContext fuel P inp o group titleLines
          ((max 1 titleLines.length : Int) * P.lineH) parent child res :=
      (expandChildCallContext_iff fuel P inp o group titleLines
        ((max 1 titleLines.length : Int) * P.lineH) parent child res).mpr hctxB
    obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, _hexpand⟩ := hctx
    obtain ⟨metric, hm, hwrap'⟩ := hwrap
    simp only [childSubInput, childSubOptions] at hchild
    simp only [parentSubInput] at hparent
    have hrec : layoutRecursive (fuel + 1) inp o = .ok res := by
      unfold layoutRecursive
      rw [hgroup]
      simp only [hP, hm, hchild, hwrap', hparent, hexpand, Bind.bind, Except.bind]
    obtain ⟨hwfChild, hparentWF⟩ := subInputWellFormedC2 inp o group hwf
    obtain ⟨P', metric', child', titleLines', parent', frm, _lines', dx, dy,
        hP', hm', hchild', hwrap'', hparent', _hexpand', hfrm, _hlines',
        hdxEq, hdyEq, hchildLookup', hparentLookup', _hroutes', _hitems'⟩ :=
      layoutRecursive_embedding_assembly_sources (Model.boxIds_nodup hwf)
        (inputRoutesCovered hwf) hgroup hrec
    have hPeq : P = P' := (Except.ok.inj (hP'.symm.trans hP)).symm
    have hmetriceq : metric = metric' := (Except.ok.inj (hm'.symm.trans hm)).symm
    subst hPeq
    subst hmetriceq
    have htleq : titleLines = titleLines' :=
      (Except.ok.inj (hwrap''.symm.trans hwrap')).symm
    have hchildeq : child = child' :=
      (Except.ok.inj (hchild'.symm.trans hchild)).symm
    subst htleq
    subst hchildeq
    have hparenteq : parent = parent' :=
      (Except.ok.inj (hparent'.symm.trans hparent)).symm
    subst hparenteq
    have hfit : ExpandChildFitsInset P inp o group
        ((max 1 titleLines.length : Int) * P.lineH) parent child res := by
      intro frm' tl' fdx fdy hfrmLook hfdxEq hfdyEq hwrapTl
      obtain ⟨metric'', hm'', htl''⟩ := hwrapTl
      have hmetricEq : metric'' = metric := Except.ok.inj (hm''.symm.trans hm)
      have htlEq : tl' = titleLines := by
        rw [hmetricEq] at htl''
        exact Except.ok.inj (htl''.symm.trans hwrap')
      have hfrmEq : frm' = frm := Option.some.inj (hfrmLook.symm.trans hfrm)
      have hfdxDx : fdx = dx := by
        rw [hfdxEq, hfrmEq, htlEq, ← hdxEq]
      have hfdyDy : fdy = dy := by
        rw [hfdyEq, hfrmEq, htlEq, ← hdyEq]
      refine ⟨?_, ?_, ?_⟩
      · rw [hfdxDx, hfdyDy, hfrmEq]
        exact layoutRecursive_childInset_fits_frame hwf hrec hgroup hP hm
          hchild hwrap' rfl hparent frm dx dy hfrm hdxEq hdyEq
      · intro box hbox
        rw [hfdxDx, hfdyDy]
        exact hchildLookup' box hbox
      · intro box hbox
        exact hparentLookup' box hbox
    refine ⟨hfit, ?_, ?_⟩
    · exact layoutRecursive_parent_closed_wellFormed (hparentWF _ _ _) fuel
        parent hparent
    · exact layoutRecursive_parent_closed_wellFormed hwfChild fuel child hchild
  stepC2 := fun fuel P inp o group titleLines titleHeight parent child res
      hexpand hids hctxB _hparams =>
    hgeo_of_recursion subInputWellFormedC2 fuel P inp o group titleLines
      titleHeight parent child res hexpand hids
      ((expandChildCallContext_iff fuel P inp o group titleLines titleHeight
        parent child res).mpr hctxB)
  stepC6 := fun fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams =>
    expandChild_c6_step_of_geometry S.stepC6Geometry stepC6Anchors_holds
      fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      ((expandChildCallContext_iff fuel P inp o group titleLines titleHeight
        parent child res).mpr hctxB)
      hparams
  stepC7 := by
    intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hdisjoint hctxB hparams
    have hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res :=
      (expandChildCallContext_iff fuel P inp o group titleLines titleHeight
        parent child res).mpr hctxB
    intro frame tl dx dy hframe hdx hdy hwrap
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
      expandChild_c7_structure fuel P inp o group titleLines titleHeight
        parent child res hexpand hframed hctx
        (expandChild_label_owners fuel P inp o group titleLines titleHeight parent
          child res hexpand hframed hctx hparams)
        (expandChild_c7_label_scopes_of_disjoint hexpand hframed hctx hparams hdisjoint
          (stepC8aAncestry_holds fuel P inp o group titleLines titleHeight parent
            child res hexpand hframed hctx hparams))
        frame tl dx dy hframe hdx hdy hwrap
    obtain ⟨g1, g2, g3, g4⟩ :=
      S.stepC7Geometry fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
    exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, g1, g2, g3, g4⟩
  stepC8a := fun fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams =>
    expandChild_c8a_step_of_geometry stepC8aGeometry_holds
      (fun fuel P inp o group titleLines titleHeight parent child res hexpand
        hframed hctx hparams =>
        expandChild_c8a_structure fuel P inp o group titleLines titleHeight
          parent child res hexpand hframed hctx
          (stepC8aAncestry_holds fuel P inp o group titleLines titleHeight parent
            child res hexpand hframed hctx hparams))
      fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      ((expandChildCallContext_iff fuel P inp o group titleLines titleHeight
        parent child res).mpr hctxB)
      hparams
  stepC8b := fun fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams =>
    expandChild_c8b_step_of_geometry S.stepC8bGeometry
      (fun fuel P inp o group titleLines titleHeight parent child res hexpand
        hframed hctx hparams =>
        expandChild_c8b_structure fuel P inp o group titleLines titleHeight
          parent child res hexpand hframed hctx
          (expandChild_label_owners fuel P inp o group titleLines titleHeight parent
            child res hexpand hframed hctx hparams))
      fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      ((expandChildCallContext_iff fuel P inp o group titleLines titleHeight
        parent child res).mpr hctxB)
      hparams

end Elegant.Layered.PipelineImpl

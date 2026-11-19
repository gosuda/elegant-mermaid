import Elegant.Layered.FamilyAssemblyB
import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.SubInputWellFormedFacts
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
// base-independent). `flatC3` stays open: `layoutX_c3` needs the full
// `ExactComponentPlacement`, whose second conjunct is the draft
// `exactMemberInFrame` modulo the open `ExactRunFrameNesting` residual (the
// unguarded form is false; see the witness in `ExactMemberInFrame.lean`).
Each field below names in one line the plain-pipeline theorem proving its
counterpart, for the porting slices. -/
structure ExactSeams (exactIds : List String) : Prop where
  /-- Plain counterpart: `layout_c3` via `flatC3B_of_flat`. -/
  flatC3 : Layered.PipelineImpl.FlatC3B (Layered.PipelineImpl.layoutX exactIds)
  /-- Plain counterpart: `layout_c2` via `flatC2B_of_flat`. -/
  flatC2 : Layered.PipelineImpl.FlatC2B (Layered.PipelineImpl.layoutX exactIds)
  /-- Plain counterpart: `FlatGroupEndpoints` via `flatC5B_of_endpoints`. -/
  flatC5 : Layered.PipelineImpl.FlatC5B (Layered.PipelineImpl.layoutX exactIds)
  /-- Plain counterpart: the eight narrow `LayeredSeams` residuals via `flatC6_closed`. -/
  flatC6 : Layered.PipelineImpl.FlatC6B (Layered.PipelineImpl.layoutX exactIds)
  /-- Plain counterpart: `layout_c7`. -/
  flatC7 : Layered.PipelineImpl.FlatC7B (Layered.PipelineImpl.layoutX exactIds)
  /-- Plain counterpart: `flatC8a_of_span_seams` plus foreign-span premises. -/
  flatC8a : Layered.PipelineImpl.FlatC8aB (Layered.PipelineImpl.layoutX exactIds)
  /-- Plain counterpart: `layout_c8b` plus the narrow label residuals via `frameLabels_executed`. -/
  flatC8b : Layered.PipelineImpl.FlatC8bB (Layered.PipelineImpl.layoutX exactIds)
  /-- Residual: the canvas-margin bound the C7/C8b lifts need. -/
  canvasMargins :
    Layered.PipelineImpl.CanvasMarginsB (Layered.PipelineImpl.layoutX exactIds)
  /-- Plain counterpart: `frameClearanceSeam_holds` over `S.dummyRowClear`/`S.titleCopySpan`. -/
  frameClear :
    ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
      WellFormed (Layered.inputModel inp o) →
        Layered.framedParents inp = true →
          Layered.PipelineImpl.FrameClearanceSeam inp o res
  /-- Plain counterpart: `runLocalLabelClearance_holds` plus `routeLabelDumpBridges`. -/
  labelRuns :
    ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
      WellFormed (Layered.inputModel inp o) →
        Layered.framedParents inp = true →
          Layered.LabelRunsClearExclusiveBoxes inp o res
  /-- Plain counterpart: `LayeredSeams.titleExclusiveSamePart` via `sceneCaptionBoxContainment_of_fit`. -/
  captions :
    ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
      WellFormed (Layered.inputModel inp o) →
        Layered.framedParents inp = true →
          Layered.PipelineImpl.InputFixedFit inp o →
          Layered.SceneCaptionBoxContainment inp o res
  /-- Plain counterpart: `subInputWellFormed` transported through `layoutRecursive_eq_B`. -/
  subInputB :
    Layered.PipelineImpl.SubInputWellFormedB (Layered.PipelineImpl.layoutX exactIds)
  /-- Plain counterpart: `layoutRecursive_childInset_fits_frame` plus parent closure. -/
  fitClosed :
    Layered.PipelineImpl.ExpandChildFitClosedB (Layered.PipelineImpl.layoutX exactIds)
  /-- Plain counterpart: `hgeo_of_recursion`. -/
  stepC2 :
    ∀ (fuel : Nat) (P : Layered.PipelineImpl.Params) (inp : Layered.Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : Layered.FamilyResult),
      Layered.PipelineImpl.expandChild P inp o group titleHeight parent child = .ok res →
      (∀ m ∈ inp.boxes, m.id ≠ "") →
      Layered.PipelineImpl.ExpandChildCallContextB
        (Layered.PipelineImpl.layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      Layered.PipelineImpl.ExpandChildCallParams P inp o group titleLines titleHeight →
      Layered.PipelineImpl.ExpandChildC2Step P inp o group titleHeight parent child res
  /-- Plain counterpart: `expandChild_c6_step_of_geometry`. -/
  stepC6 :
    ∀ (fuel : Nat) (P : Layered.PipelineImpl.Params) (inp : Layered.Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : Layered.FamilyResult),
      Layered.PipelineImpl.expandChild P inp o group titleHeight parent child = .ok res →
      Layered.framedParents inp = true →
      Layered.PipelineImpl.ExpandChildCallContextB
        (Layered.PipelineImpl.layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      Layered.PipelineImpl.ExpandChildCallParams P inp o group titleLines titleHeight →
      Layered.PipelineImpl.ExpandChildC6Step P inp o group titleHeight parent child res
  /-- Plain counterpart: `expandChild_c7_step_of_geometry` plus `expandChild_c7_structure`. -/
  stepC7 :
    ∀ (fuel : Nat) (P : Layered.PipelineImpl.Params) (inp : Layered.Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : Layered.FamilyResult),
      Layered.PipelineImpl.expandChild P inp o group titleHeight parent child = .ok res →
      Layered.framedParents inp = true →
        Layered.PipelineImpl.BoxRouteIdsDisjoint inp →
      Layered.PipelineImpl.ExpandChildCallContextB
        (Layered.PipelineImpl.layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      Layered.PipelineImpl.ExpandChildCallParams P inp o group titleLines titleHeight →
      Layered.PipelineImpl.ExpandChildC7Step P inp o group titleHeight parent child res
  /-- Plain counterpart: `expandChild_c8a_step_of_geometry` plus `expandChild_c8a_structure`. -/
  stepC8a :
    ∀ (fuel : Nat) (P : Layered.PipelineImpl.Params) (inp : Layered.Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : Layered.FamilyResult),
      Layered.PipelineImpl.expandChild P inp o group titleHeight parent child = .ok res →
      Layered.framedParents inp = true →
      Layered.PipelineImpl.ExpandChildCallContextB
        (Layered.PipelineImpl.layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      Layered.PipelineImpl.ExpandChildCallParams P inp o group titleLines titleHeight →
      Layered.PipelineImpl.ExpandChildC8aStep P inp o group titleHeight parent child res
  /-- Plain counterpart: `expandChild_c8b_step_of_geometry` plus `expandChild_c8b_structure`. -/
  stepC8b :
    ∀ (fuel : Nat) (P : Layered.PipelineImpl.Params) (inp : Layered.Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : Layered.FamilyResult),
      Layered.PipelineImpl.expandChild P inp o group titleHeight parent child = .ok res →
      Layered.framedParents inp = true →
      Layered.PipelineImpl.ExpandChildCallContextB
        (Layered.PipelineImpl.layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      Layered.PipelineImpl.ExpandChildCallParams P inp o group titleLines titleHeight →
      Layered.PipelineImpl.ExpandChildC8bStep P inp o group titleHeight parent child res

/-- Seams for the exact base: `flatInset` replays `layoutX_inset` on
`exactPartsBounded'` (the inset body consumes only placement conjunct 1, which
holds with no hypothesis); `flatC4` from `SceneExecutionX.routes_orthogonal`;
`subInputC2` from `subInputWellFormedC2`; `partsSep` from
`labelsC7_partsSeparated` (all base-independent). Every other field is the
matching `ExactSeams` projection. Stated as a `theorem` because the target is
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
  flatC3 := R.flatC3
  flatC2 := R.flatC2
  flatC4 := fun inp o res h route hroute => by
    obtain ⟨execution⟩ := Layered.PipelineImpl.layoutX_sceneExecution h
    exact Layered.PipelineImpl.SceneExecutionX.routes_orthogonal execution route hroute
  flatC5 := R.flatC5
  flatC6 := R.flatC6
  flatC7 := R.flatC7
  flatC8a := R.flatC8a
  flatC8b := R.flatC8b
  canvasMargins := R.canvasMargins
  frameClear := R.frameClear
  partsSep := fun _ _ _ => Layered.PipelineImpl.labelsC7_partsSeparated
  labelRuns := R.labelRuns
  captions := R.captions
  subInputC2 := Layered.PipelineImpl.subInputWellFormedC2
  subInputB := R.subInputB
  fitClosed := R.fitClosed
  stepC2 := R.stepC2
  stepC6 := R.stepC6
  stepC7 := R.stepC7
  stepC8a := R.stepC8a
  stepC8b := R.stepC8b

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

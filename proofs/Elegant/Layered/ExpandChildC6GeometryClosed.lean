import Elegant.Layered.ExpandChildC6GeometryExecuted
import Elegant.Layered.ExpandChildC8aGeometryExecuted
import Elegant.Layered.ExpandChildParentFrameDirect
import Elegant.Layered.ExpandChildFrameLiftProof
import Elegant.Layered.ExpandChildFrameLiftResiduals
import Elegant.Layered.RecursiveC78
import Elegant.Layered.ExpandChildAncestryProof
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.ExpandChildParentRouteClearProof
import Elegant.Layered.ExpandChildParentRouteRunProof
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams

set_option autoImplicit false

open Elegant.Layered.Compound

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Closed C6 geometry: discharging `stepC6Geometry_holds`

`stepC6Geometry_holds` (`ExpandChildC6GeometryExecuted`) takes two
per-call hypotheses. Both are discharged here from the flat clause and
narrow single-scene residuals; no circular seam remains:

* `hC8aParent`: the parent scene is a successful recursive layout at the
  call fuel, so `layoutRecursive_c8a_of_flat` gives `Validator.C8a` from
  `FlatC8a`, the proved sub-input seam `subInputsWellFormed`, and the
  `ExpandChildC8aStep` assembled from the proved structure
  (`expandChild_c8a_structure` with the proved `stepC8aAncestry_holds`)
  and the proved `stepC8aGeometry_holds`.
* `hRouteClear`: the out-of-scope conjunct (`ExpandChildParentRouteFrameClear`)
  is the restated frame lift `expandChild_parentRouteFrameClear'` from the
  flat-stage seams and the two narrowed wrappers `ExpandChildParentFixedDisjointGroup`
  / `ExpandChildParentStrictMissGroup`; the attached conjunct
  (`ExpandChildParentRouteAttachedClear`) is `ExpandChildParentStrictMissGroup`
  restricted to attached routes (the strict-interior miss already covers every
  parent route, attached or not).

Why the attached conjunct stays a residual: the group frame is non-exclusive
in the parent scene (`sceneOf` copies `exclusive` from the model box and
`WellFormed` forbids exclusive groups; every probed executed call shows
`exclusive = false`), so parent C6 (`routeClear`: `!b.exclusive || scope ∋ ...`)
is vacuous for the frame; and every attached route has `group.id` in its
route scope, so C6 is doubly vacuous for exactly the attached case. C5 pins
the attached endpoint on the frame boundary (probed: `BOUND-VIOL` 0), but no
proved clause bounds the stub exterior or the middle segments, so the
strict-interior miss remains assumed as `ExpandChildParentStrictMissGroup`.

Probe evidence (`proofs/wip/Probe/StepC6CloseTProbe.lean`, 5 executed calls
over `twoComp`, `groupEnd`, `sandwich`, `twoGroups`): `C8A-VIOL` 0, `BOX-VIOL` 0,
`A-VIOL` 0, `A-INNER-VIOL` 0, `B-VIOL` 0, `BOUND-VIOL` 0, `FIXED-VIOL` 0,
`SCOPE-UNEXPECTED` 0; `FIXED-COUNT` total 1 non-vacuous instance (the `G2`
call with fixed `G1`), disjoint holds.
-/

/-- The parent sub-input is well-formed (copy of the private lemma in
`ExpandChildParentFrameProof.lean`; `inputModel` ignores the fixed side tables). -/
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

/-- The parent sub-input is framed (copy of the private lemma in
`ExpandChildParentFrameProof.lean`). -/
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

/-- The C8a step of every expansion from the globally proved geometry: the
same assembly as `c8aStep_of_below` (`ExpandChildParentFrameDirect`), with the
below-fuel query replaced by the proved `stepC8aGeometry_holds`. -/
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

/-- The `hC8aParent` hypothesis of `stepC6Geometry_holds` from the flat clause:
the parent scene is the recursive result at the call fuel, so the C8a lift
applies with the proved sub-input seam and the globally proved step. -/
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

/-- The out-of-scope conjunct of `hRouteClear` from the restated frame lift:
`expandChild_parentRouteFrameClear'` with its flat-stage seams, the proved
`subInputWellFormed` seam, and the two narrowed wrappers. -/
private theorem routeFrame_of_lift
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
    (hfixedDisj : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
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
      ExpandChildParentFixedDisjointGroup frame gFrame)
    (hstrictMiss : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
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
    ExpandChildParentRouteFrameClear group parent := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
  exact expandChild_parentRouteFrameClear' hclear hnodeDecl hscoped hpos hloopRes hloopSep
    subInputWellFormed hfixedDisj hstrictMiss hframed hctx hparams

/-- The attached conjunct of `hRouteClear` from the strict-miss wrapper: the
wrapper already quantifies over every parent route, so attached routes are
covered without further router facts. -/
private theorem routeAttached_of_strictMiss
    (hstrictMiss : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
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
    ExpandChildParentRouteAttachedClear group parent := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
  intro frame hfind pr hpr _hatt r hSI
  exact hstrictMiss fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams frame hfind pr hpr r hSI
/-- The `hRouteClear` hypothesis of `stepC6Geometry_holds` from the two parts:
out-of-scope from the frame lift, attached from the strict-miss wrapper. -/
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
    (hfixedDisj : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
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
      ExpandChildParentFixedDisjointGroup frame gFrame)
    (hstrictMiss : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
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
    (routeFrame_of_lift hclear hnodeDecl hscoped hpos hloopRes hloopSep hfixedDisj hstrictMiss
      fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams)
    (routeAttached_of_strictMiss hstrictMiss
      fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams)

/-- Closed C6 geometry: both hypotheses of `stepC6Geometry_holds` are
discharged, leaving the flat clause, the flat-stage seams the frame lift
consumes, and the two narrowed single-scene wrappers. -/
theorem stepC6Geometry_closed
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
    (hfixedDisj : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
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
      ExpandChildParentFixedDisjointGroup frame gFrame)
    (hstrictMiss : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentStrictMissGroup group parent) :
    RecursiveStepFacts ExpandChildC6Geometry := by
  exact stepC6Geometry_holds (c8aParent_of_flat hflat8a)
    (routeClear_closed hclear hnodeDecl hscoped hpos hloopRes hloopSep hfixedDisj hstrictMiss)


end PipelineImpl
end Layered
end Elegant

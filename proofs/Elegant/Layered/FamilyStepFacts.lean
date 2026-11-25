import Elegant.Layered.ExpandChildFitPerCallProof
import Elegant.Layered.RecursiveStepFacts

import Elegant.Layered.RecursiveC7
import Elegant.Layered.RecursiveC78

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Reachable per-call fixed fit: cutover kit for `LayeredSeams.fitPerCall`.

`LayeredSeams.fitPerCall` (`FamilyAssembly.lean`) asks for `InputFixedFit inp o`
at every executed `expandChild` call with no hypothesis linking the call input
to the top-level input that carries the family theorem's
`hfix : InputFixedFit inp o` premise. As stated over arbitrary call inputs the
field is false: the executed witness `badFirst`
(`proofs/wip/Probe/FitPerCallProbe.lean:188`, also run in the cell profile,
with `LR` direction, and with zero and negative fixed sizes) satisfies every
call premise yet refutes the fit conclusion, so no proof of the arbitrary form
exists. The true reachable form is proved in `ExpandChildFitPerCallProof.lean`:
`fitPerCall_of_top` threads a top-level fit down the exact sub-inputs the
recursion builds, and `fitParent_of_top` mirrors `fitParent_of_seams`.

Status: the field is KEPT. The family-theorem path is being cut over to the
reachable fit in owned files; `baseSeams_of_layered` keeps the field for the
B fill (`BaseSeams.stepC7`/`stepC8b` keep their fields, pinned by
`UsecaseValidExact.exactBaseSeams`; the B lifts `layoutRecursiveB_c7`
(`RecursiveBLiftsB.lean:167`) and `layoutRecursiveB_c8b`
(`RecursiveBLiftsB.lean:327`) thread `hfit` without passing it to `hgeo`).
The family statement is unchanged, so it is not weakened.

Done in this file: `RestrictedStepFacts` (reachability-indexed step facts),
`restrictedCallFit`/`restrictedParentFit` (per-call fit supply in step-fact
call shape, via `fitPerCall_of_top`/`fitParent_of_top`), and owned copies
`layoutRecursive_c7_of_flat_fit`/`layoutRecursive_c8b_of_flat_fit` whose
`hgeo` takes the current input's fit (mirroring `BoxRouteIdsDisjoint`);
`FamilyAssembly.lean` has the single-call `stepC7Geometry_single` (fed by the
`∀` wrapper for the B fill). `fitParent_of_seams` is mirrored by
`fitParent_of_top`; the step bodies are otherwise unchanged.

Remainder (all in owned files; `RecursiveC7.lean`, `RecursiveC78.lean`,
`RecursiveBLiftsB.lean` are untouched). The `hfit`-in-`hgeo` copies above
cover the main lifts, whose use sites have the threaded `hfit` in scope.
The below-fuel fragment needs the same treatment with reachability, because
`expandChild_parentFrame_direct` applies its `below8b` premise at calls whose
fits only reachability supplies: add `tin`/`to` parameters and an
`hr : FitReached tin to inp o` premise to `hgeo` (as well as `hfit`), thread
`hr` with the `child`/`parent` constructors of `FitReached` wherever the
lifts now thread `hfit`, and duplicate the C8b-below chain with `hr`
(`c8bStep_of_below`, `layoutRecursive_c8b_of_below`, `parentScene_c8b_below`,
`expandChild_parentFrame_direct`, `stepC8bGeometry_of_below`, keeping the
plain versions for the B fill), closing the `hr`-indexed below-facts by fuel
induction (mirroring `recursiveStepFacts_of_below`) with fits from
`fitPerCall_of_top`. Then the family `hstepC7`/`hstepC8b` take `hr`, derive
fits through this file's bridges, and feed the `_fit` lifts; the B fill is
unchanged.
-/

/-- Step facts restricted to call inputs reached from a fit top-level input:
the same step statements with one extra premise threading the top-level fit
down the exact descent the recursion performs. -/
abbrev RestrictedStepFacts (tin : Input) (to : Options)
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    FitReached tin to inp o →
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    Step P inp o group titleHeight parent child res

/-- The per-call fit at a reached input, in step-fact call shape: what the
`hfit` hypothesis of `stepC7Geometry_holds` and `stepC8bGeometry_holds` becomes
once the lifts thread the current input's fit. -/
theorem restrictedCallFit {tin : Input} {to : Options} (htop : InputFixedFit tin to)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hr : FitReached tin to inp o)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    InputFixedFit inp o :=
  fitPerCall_of_top htop hr

/-- The parent sub-input fit at a reached call, in step-fact call shape: what
`fitParent_of_seams` becomes once the lifts thread the current input's fit. -/
theorem restrictedParentFit {tin : Input} {to : Options} (htop : InputFixedFit tin to)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hr : FitReached tin to inp o)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    InputFixedFit (parentSubInput inp group P titleLines child) o :=
  fitParent_of_top htop hr hctx hparams

/-- Owned copy of `layoutRecursive_c7_of_flat` (`RecursiveC7.lean`) whose step
hypothesis also takes the current input's fit, exactly as it already takes
the current input's `BoxRouteIdsDisjoint`. The threaded `hfit` is in scope at
the use site, so the copy passes it where the original passes `hdisjoint`.
(Not yet fed by the family theorem; that awaits the below-fuel `hr` chain
described in the module doc.) -/
theorem layoutRecursive_c7_of_flat_fit (hflat7 : FlatC7)
    (hsep : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      PartsSeparated inp o res)
    (hseam1 : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LabelRunsClearExclusiveBoxes inp o res)
    (hseam2 : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o →
      SceneCaptionBoxContainment inp o res)
    (hsub : SubInputWellFormed)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      BoxRouteIdsDisjoint inp →
      InputFixedFit inp o →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7Step P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o → BoxRouteIdsDisjoint inp →
      layoutRecursive fuel inp o = .ok res → Validator.C7 res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hwf hframed hfit hdisjoint h
      exact hflat7 inp o res hwf hframed (hsep inp o res) (hseam1 inp o res hwf hframed)
        (hseam2 inp o res hwf hframed hfit) h
  | succ fuel ih =>
      intro inp o res hwf hframed hfit hdisjoint h
      have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      have hcovered : RoutesCovered inp := inputRoutesCovered hwf
      rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
        ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
      · exact hflat7 inp o res hwf hframed (hsep inp o res) (hseam1 inp o res hwf hframed)
          (hseam2 inp o res hwf hframed hfit) hlayout
      · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
          hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
        obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
          hsub fuel inp o group P metric titleLines child parent hwf hframed hP hm hwrap
            hchild hparentAt
        have hfitChild := hfit.childSubInput group
        have hdisjChild := hdisjoint.childSubInput group
        have hcm := layoutRecursive_canvas_margins fuel hchild
        have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
          rw [checkedParams_canvasMargin hP]
          exact hcm.1
        have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
          rw [checkedParams_canvasMargin hP]
          exact hcm.2
        have hfitParent := InputFixedFit.parentSubInput hwf hfit hP hm hwrap hcw hch
        have hdisjParent := hdisjoint.parentSubInput group P titleLines child
        have hchildC7 := ih _ _ _ hwfChild hframedChild hfitChild hdisjChild hchild
        have hparentC7 := ih _ _ _ hwfParent hframedParent hfitParent hdisjParent hparentAt
        have hstep := hgeo fuel P inp o group titleLines _ parent child res hexpandAt hframed
          hdisjoint hfit ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
          ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
        exact expandChild_c7 hchildC7 hparentC7 hstep hexpandAt

/-- Owned copy of `layoutRecursive_c8b_of_flat` (`RecursiveC78.lean`) whose step
hypothesis also takes the current input's fit. The threaded `hfit` is in scope
at the use site, so the copy passes it. (Not yet fed by the family theorem;
that awaits the below-fuel `hr` chain described in the module doc.) -/
theorem layoutRecursive_c8b_of_flat_fit (hflat8b : FlatC8b)
    (hsub : SubInputsWellFormed)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      InputFixedFit inp o →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStep P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o →
      layoutRecursive fuel inp o = .ok res → Validator.C8b res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hwf hframed hfit h
      exact hflat8b inp o res hwf hframed hfit h
  | succ fuel ih =>
      intro inp o res hwf hframed hfit h
      have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
      rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
        ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
      · exact hflat8b inp o res hwf hframed hfit hlayout
      · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
          hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
        obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
          hsub fuel inp o group P metric titleLines child parent hwf hframed hP hm hwrap
            hchild hparentAt
        have hfitChild := hfit.childSubInput group
        have hcm := layoutRecursive_canvas_margins fuel hchild
        have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
          rw [checkedParams_canvasMargin hP]
          exact hcm.1
        have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
          rw [checkedParams_canvasMargin hP]
          exact hcm.2
        have hfitParent := InputFixedFit.parentSubInput hwf hfit hP hm hwrap hcw hch
        have hchildC8b := ih _ _ _ hwfChild hframedChild hfitChild hchild
        have hparentC8b := ih _ _ _ hwfParent hframedParent hfitParent hparentAt
        have hstep := hgeo fuel P inp o group titleLines _ parent child res hexpandAt hframed
          hfit ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
          ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
        exact expandChild_c8b hchildC8b hparentC8b hstep hexpandAt

end Elegant.Layered.PipelineImpl

import Elegant.Layered.ExpandChildC6GeometryExecuted
import Elegant.Layered.ExpandChildC7GeometryProof
import Elegant.Layered.ExpandChildC6StepFacts
import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.InsetFit
import Elegant.Layered.SceneBounds
import Elegant.Layered.RecursiveC7
import Elegant.Layered.RecursiveC78
import Elegant.Layered.RecursiveC6
import Elegant.Layered.FamilyC5B
import Elegant.Layered.FramedParentsSub
import Elegant.Layered.ExactFlatC5Closed
import Elegant.Layered.ExactFitClosure
import Elegant.Layered.InputFixedFit
import Elegant.Layered.ExactSubInputStepC2
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.ExpandChildCanvasFitProof
import Elegant.Layered.ExpandChildChildSceneProof
import Elegant.Layered.ExpandChildAncestryProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Validator

/-- Local unfolding of `RecursiveStepFactsB` (`ExactStepFacts.lean`): the
per-expansion step fact at an arbitrary base. Used because `ExactStepFacts`
currently imports the mid-repair `FamilyAssembly.lean` and has no olean;
this unfolds to the identical `∀`-type, so terms coerce by definitional
equality. Delete this abbrev and restore the import once that module builds. -/
abbrev XG_RecursiveStepFactsB
    (base : Input → Options → Except LayoutError FamilyResult)
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    Step P inp o group titleHeight parent child res


/-! # Exact step geometry: C6, C7, C8b at the exact base.

The exact recursion `layoutRecursiveB (layoutX exactIds)` calls the same
`expandChild` assembly as the plain `layoutRecursive`, so the plain
per-expansion geometry replays over `ExpandChildCallContextB`. This module
assembles the three exact step-geometry facts:

* `stepC6Geometry`: via `stepC6Geometry_holdsB`, with the inset facts proved
  here and the two parent-scene facts as named residuals;
* `stepC7Geometry`: via the context-free `expandChild_c7_geometry` assembly,
  using the caller's `InputFixedFit` for child containment;
* `stepC8bGeometry`: via the inset-core conditional, using the caller's
  `InputFixedFit` for the child-label inset.
-/

/-- The exact flat inset as a `FlatInsetB` fact: replay of the `flatInset`
lambda in `exactBaseSeams` through `exactPartsBounded'`. -/
theorem XG_flatInset (exactIds : List String) :
    FlatInsetB (layoutX exactIds) := by
  intro inp o res h
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hacc := SceneExecutionX.straightAcc_bounded execution
    (exactPartsBounded' execution)
  have hm1 := checkedParams_canvasMargin_ge_one execution.checked
  refine ⟨execution.params, execution.checked, by omega, ?_⟩
  rw [execution.scene_eq]
  exact sceneOf_boxes_inset execution.params inp o execution.lines
    execution.straightAcc execution.measured hacc (by omega)
/-- Frame reservation of an executed exact `expandChild` call: the located
group frame dominates the `childFrameSize` for the inner title lines.
`XG_` copy of the private `ESS_frame_size_bounds`
(`ExactStepShortFacts.lean`); private lemmas do not resolve across modules. -/
theorem XG_frame_size_bounds (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (frame : Box) (titleLines' : List Measure.Line)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hwrap' : ExpandChildTitleWrapped P inp o group titleLines') :
    (childFrameSize group.direction P.clusterPad
      (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w ∧
    (childFrameSize group.direction P.clusterPad
      (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := by
  obtain ⟨hP, hheightEq, hwrapCtx⟩ := hparams
  obtain ⟨metric, hmetric, hwrapEq⟩ := hwrapCtx
  obtain ⟨metric', hmetric', hwrapEq'⟩ := hwrap'
  have hmetricEq : metric' = metric := Except.ok.inj (hmetric'.symm.trans hmetric)
  subst hmetricEq
  have htlEq : titleLines' = titleLines := Except.ok.inj (hwrapEq'.symm.trans hwrapEq)
  subst titleLines'
  obtain ⟨hwf, hgroup, hpboxes, hchild, hparent, _hexpand'⟩ := hctxB
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hsub := subInputWellFormedB_layoutX exactIds fuel inp o group P metric'
    titleLines child parent hwf _hframed hP hmetric hwrapEq hchild hparent
  have hparentC5 := layoutRecursiveB_c5_facts (flatC5B_layoutX_closed exactIds)
    (subInputWellFormedB_layoutX exactIds) fuel hsub.2.2.1 hsub.2.2.2 hparent
  have hparentOutputIds : parent.scene.boxes.map (·.id) =
      (parentSubInput inp group P titleLines child).boxes.map (·.id) :=
    hparentC5.1
  have hparentIds : ((parentSubInput inp group P titleLines child).boxes.map
      (·.id)).Nodup := by
    rw [hpboxes, selectInput_box_ids]
    exact nodup_filter_map _ _ _ hboxIds
  have hparentCovered : RoutesCovered (parentSubInput inp group P titleLines child) := by
    change RoutesCovered
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id))
    exact selectInput_routesCovered inp _ ""
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hparentSourceId : group.id ∈
      (parentSubInput inp group P titleLines child).boxes.map (·.id) := by
    rw [← hparentOutputIds, ← hframeId]
    exact List.mem_map.mpr ⟨frame, List.mem_of_find?_eq_some hframe, rfl⟩
  obtain ⟨source, hsource, hsourceId⟩ := List.mem_map.mp hparentSourceId
  have hsourceBase : source ∈ (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := by
    rw [← hpboxes]
    exact hsource
  obtain ⟨original, horiginal, _, hsourceEq⟩ :=
    selectInput_box_source inp (fun box => !Compound.inside inp.boxes group.id box.id)
      "" source hsourceBase
  have hsourceOriginalId : source.id = original.id := by
    rw [hsourceEq]
    split <;> rfl
  have horiginalId : original.id = group.id := hsourceOriginalId.symm.trans hsourceId
  have horiginalLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hboxIds original horiginal
  have hgroupLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hboxIds
    group (List.mem_of_find?_eq_some hgroup)
  rw [horiginalId] at horiginalLookup
  have horiginalEq : original = group :=
    Option.some.inj (horiginalLookup.symm.trans hgroupLookup)
  have hnotfixed : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
    have hs := List.find?_some hgroup
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2
  have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hnotfixed)
  let size := childFrameSize group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩
  have hfixed : (parentSubInput inp group P titleLines child).fixedSizes.find?
      (fun fixed => fixed.1 == source.id) = some (group.id, size) := by
    change (inp.fixedSizes ++ [(group.id, size)]).find?
      (fun fixed => fixed.1 == source.id) = some (group.id, size)
    simp [List.find?_append, hsourceId, hnone]
  obtain ⟨actual, hactual, _, hw, hh⟩ :=
    (xExactFixedMin exactIds) fuel _ _ _ _ _ hparentIds hparentCovered hparent
      hsource hfixed
  rw [hsourceId] at hactual
  have hactualEq : actual = frame := Option.some.inj (hactual.symm.trans hframe)
  subst actual
  have hw' : (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w := by
    have hw'' : (childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w := hw
    rw [← hheightEq] at hw''
    exact hw''
  have hh' : (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := by
    have hh'' : (childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := hh
    rw [← hheightEq] at hh''
    exact hh''
  exact ⟨hw', hh'⟩
/-- Strict content fit of an executed exact `expandChild` call: every rect
inside the child canvas shrunk by `P.canvasMargin` lands strictly inside the
group frame. `XG_` copy of the private `ESS_content_fit_strict`. -/
theorem XG_content_fit_strict (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
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
    ∀ (r : Rect),
    (⟨P.canvasMargin, P.canvasMargin, child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained r →
    frame.rect.StrictInside (shiftRect dx dy r) := by
  intro frame titleLines' dx dy hframe hdx hdy hwrap' r hr
  obtain ⟨hw, hh⟩ := XG_frame_size_bounds exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams frame titleLines'
    hframe hwrap'
  obtain ⟨hP, hheightEq, _hwrapCtx⟩ := hparams
  have hpad : 0 < P.clusterPad := callParams_clusterPad_pos hP
  have htw : 0 ≤ titleLines'.foldl (fun width line => max width line.width) 0 := by
    suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
        0 ≤ ls.foldl (fun width line => max width line.width) acc by
      exact key titleLines' 0 (by omega)
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
  have hS : frame.rect.StrictInside
      (shiftRect dx dy ⟨P.canvasMargin, P.canvasMargin,
        child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩) := by
    rw [hdx, hdy]
    exact childInsetContent_strict hpad htw hth hw hh
  have hshift : (shiftRect dx dy ⟨P.canvasMargin, P.canvasMargin,
      child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩).Contained (shiftRect dx dy r) :=
    (contained_shiftRect dx dy).mpr hr
  unfold Rect.StrictInside at hS ⊢
  unfold Rect.Contained at hshift
  omega
/-- Child boxes of an executed exact `expandChild` lie in the margin inset
of the child canvas. `XG_` copy of the private `ESS_child_boxes_insetB`,
via `XG_flatInset` and the `layoutRecursiveB_inset` lift. -/
theorem XG_child_boxes_insetB (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect := by
  obtain ⟨hwf, _hgroup, _hpboxes, hchild, hparent, _hexpand'⟩ := hctxB
  obtain ⟨hP, _hheightEq, hwrapCtx⟩ := hparams
  obtain ⟨metric, hmetric, hwrapEq⟩ := hwrapCtx
  have hsub := subInputWellFormedB_layoutX exactIds fuel inp o group P metric
    titleLines child parent hwf hframed hP hmetric hwrapEq hchild hparent
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  have hinset := layoutRecursiveB_inset (layoutX exactIds)
    (XG_flatInset exactIds) subInputWellFormedC2 (exactFitClosed exactIds)
    fuel _ _ _ hsub.1 hsub.2.1 hchild P hQchild
  exact hinset.2
/-- Route points of a successful flat `layoutX` lie in the margin inset of
its canvas: the exact execution's packed bounds transported through
`sceneOf`, mirroring `flat_layout_routes_inset`. Needs no placement
hypothesis: `exactPartsBounded'` holds outright. -/
theorem XG_flat_routes_insetX (exactIds : List String) {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) (Q : Params)
    (hQ : checkedParams o.profile inp.kind = .ok Q) :
    ∀ cr ∈ res.scene.routes, ∀ p ∈ cr.points,
      PointIn (insetRect res.scene.canvas Q.canvasMargin) p := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hQeq : Q = execution.params :=
    Except.ok.inj (hQ.symm.trans execution.checked)
  subst hQeq
  intro cr hcr p hp
  rw [execution.scene_eq] at hcr ⊢
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcr
  have hzip : (cr, i) ∈ (sceneOf execution.params inp o execution.lines
      execution.straightAcc execution.measured).routes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hi
  have hm : 0 ≤ execution.params.canvasMargin := by
    have := checkedParams_canvasMargin_ge_one execution.checked
    omega
  have hacc := SceneExecutionX.straightAcc_bounded execution
    (exactPartsBounded' execution)
  exact sceneOf_routes_pointIn_inset execution.params inp o execution.lines
    execution.straightAcc execution.measured hacc hm (cr, i) hzip p hp
/-- The located group frame contains the shifted child margin inset: the
strict content fit weakened to containment, with the inset rect folded. -/
theorem XG_frame_fitB (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (frame : Box) (fdx fdy : Int)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hdx : fdx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin)
    (hdy : fdy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin) :
    frame.rect.Contained
      (shiftRect fdx fdy (insetRect child.scene.canvas P.canvasMargin)) := by
  have hwrap' : ExpandChildTitleWrapped P inp o group titleLines := hparams.2.2
  have hself : (⟨P.canvasMargin, P.canvasMargin,
      child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained
      ⟨P.canvasMargin, P.canvasMargin,
        child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ := by
    simp only [Rect.Contained]
    omega
  have hS := XG_content_fit_strict exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams frame titleLines
    fdx fdy hframe hdx hdy hwrap' _ hself
  have hc := strictInside_to_contained hS
  simpa [insetRect] using hc
/-- Route points of a successful `layoutRecursiveB (layoutX exactIds)` lie
in the margin inset of the canvas. Mirror of `layoutRecursive_routes_inset`:
the flat branch is `XG_flat_routes_insetX`, the merge shifts child points
into the frame (via `XG_frame_fitB`) and keeps parent points verbatim. -/
theorem XG_routes_insetB (exactIds : List String) (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ Q : Params, checkedParams o.profile inp.kind = .ok Q →
        ∀ cr ∈ res.scene.routes, ∀ p ∈ cr.points,
          PointIn (insetRect res.scene.canvas Q.canvasMargin) p := by
  induction fuel with
  | zero =>
    intro inp o res _hwf _hframed h Q hQ cr hcr p hp
    exact XG_flat_routes_insetX exactIds h Q hQ cr hcr p hp
  | succ fuel ih =>
    intro inp o res hwf hframed h Q hQ cr hcr p hp
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with ⟨_, hlayout⟩ |
      ⟨group, Pm, metric, child, titleLines, parent, hg, hPm, hm, hc, ht, hp',
        hexpand⟩
    · exact XG_flat_routes_insetX exactIds hlayout Q hQ cr hcr p hp
    · have hQm : Pm = Q := Except.ok.inj (hPm.symm.trans hQ)
      subst hQm
      obtain ⟨hwfChild, hparentWF⟩ := subInputWellFormedC2 inp o group hwf
      have hframedChild : framedParents (childSubInput inp group) = true :=
        (framedParentsSub inp o group hwf hframed).1
      have hQchild : checkedParams (childSubOptions o group).profile
          (childSubInput inp group).kind = .ok Pm := hQ
      have hQparent : checkedParams o.profile
          (parentSubInput inp group Pm titleLines child).kind = .ok Pm := hQ
      have hcIH := ih (childSubInput inp group) (childSubOptions o group) child
        hwfChild hframedChild hc Pm hQchild
      have hwfParent : WellFormed
          (inputModel (parentSubInput inp group Pm titleLines child) o) :=
        hparentWF _ _ _
      have hframedParent : framedParents
          (parentSubInput inp group Pm titleLines child) = true :=
        framedParents_selectInput_outside_append inp o group hwf hframed
          _ child.scene child.itemArea
      have hpIH := ih (parentSubInput inp group Pm titleLines child) o parent
        hwfParent hframedParent hp' Pm hQparent
      obtain ⟨frame, metricS, ftl, _linesS, fdx, fdy, hframe, hmS, htlS, _hlS,
        hdxS, hdyS, hcanvasS, _hboxesS⟩ := expandChild_sources hexpand
      have hmetricSeq : metric = metricS :=
        Except.ok.inj (hm.symm.trans hmS)
      subst hmetricSeq
      have htlSeq : titleLines = ftl :=
        Except.ok.inj (ht.symm.trans htlS)
      subst htlSeq
      have hroutesEq := expandChild_routes_eq hexpand frame metric titleLines
        fdx fdy hframe hm ht hdxS hdyS
      have hparams : ExpandChildCallParams Pm inp o group titleLines
          ((max 1 titleLines.length : Int) * Pm.lineH) :=
        ⟨hPm, rfl, ⟨metric, hm, ht⟩⟩
      have hctxB : ExpandChildCallContextB (layoutX exactIds) fuel Pm inp o group
          titleLines ((max 1 titleLines.length : Int) * Pm.lineH) parent child res :=
        ⟨hwf, hg, rfl, hc, hp', hexpand⟩
      have hfitFrame : frame.rect.Contained
          (shiftRect fdx fdy (insetRect child.scene.canvas Pm.canvasMargin)) :=
        XG_frame_fitB exactIds fuel Pm inp o group titleLines
          ((max 1 titleLines.length : Int) * Pm.lineH) parent child res
          hexpand hframed hctxB hparams frame fdx fdy hframe hdxS hdyS
      have hparentInset := layoutRecursiveB_inset (layoutX exactIds)
        (XG_flatInset exactIds) subInputWellFormedC2 (exactFitClosed exactIds)
        fuel _ _ _ hwfParent hframedParent hp' Pm hQparent
      rw [hroutesEq] at hcr
      obtain ⟨model, _hmodel, hbind⟩ := List.mem_filterMap.mp hcr
      cases hfind : (((child.scene.routes.map fun (route : Route) =>
          { route with points := route.points.map (shiftPoint fdx fdy) }) ++
        parent.scene.routes).find? (fun (route : Route) => route.id == model.id)) with
      | none => rw [hfind] at hbind; simp at hbind
      | some route =>
        rw [hfind] at hbind
        have hrEq : route = cr := Option.some.inj hbind
        have hrouteMem : route ∈ (child.scene.routes.map
            (fun r => { r with points := r.points.map (shiftPoint fdx fdy) })) ++
            parent.scene.routes := List.mem_of_find?_eq_some hfind
        rcases List.mem_append.mp hrouteMem with hcm | hpm
        · obtain ⟨cr', hcr'mem, hcr'Eq⟩ := List.mem_map.mp hcm
          rw [← hrEq, ← hcr'Eq] at hp
          change p ∈ cr'.points.map (shiftPoint fdx fdy) at hp
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          have hqIH : PointIn (insetRect child.scene.canvas
              Pm.canvasMargin) q := hcIH cr' hcr'mem q hq
          have h1 : PointIn (shiftRect fdx fdy
              (insetRect child.scene.canvas Pm.canvasMargin))
              (shiftPoint fdx fdy q) := pointIn_shift hqIH
          have h2 : (shiftRect fdx fdy
              (insetRect child.scene.canvas Pm.canvasMargin)).Contained
              ⟨(shiftPoint fdx fdy q).x, (shiftPoint fdx fdy q).y, 0, 0⟩ :=
            (pointIn_contained).mp h1
          have h3 : frame.rect.Contained ⟨(shiftPoint fdx fdy q).x,
              (shiftPoint fdx fdy q).y, 0, 0⟩ :=
            Rect.Contained.trans hfitFrame h2
          have hframeMem : frame ∈ parent.scene.boxes :=
            List.mem_of_find?_eq_some hframe
          have h4 : (insetRect parent.scene.canvas Pm.canvasMargin).Contained
              frame.rect := hparentInset.2 frame hframeMem
          have h5 : (insetRect parent.scene.canvas Pm.canvasMargin).Contained
              ⟨(shiftPoint fdx fdy q).x, (shiftPoint fdx fdy q).y, 0, 0⟩ :=
            Rect.Contained.trans h4 h3
          rw [hcanvasS]
          exact (pointIn_contained).mpr h5
        · rw [← hrEq] at hp
          rw [hcanvasS]
          exact hpIH route hpm p hp
/-- Child route points of an executed exact `expandChild` lie in the margin
inset of the child canvas. `XG_` copy of `expandChild_child_routes_inset`,
via the `XG_routes_insetB` induction. -/
theorem XG_child_routes_insetB (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ cr ∈ child.scene.routes, ∀ p ∈ cr.points,
      PointIn (insetRect child.scene.canvas P.canvasMargin) p := by
  obtain ⟨hwf, _hgroup, _hpboxes, hchild, _hparent, _hexpand'⟩ := hctxB
  obtain ⟨hP, _hheightEq, _hwrapCtx⟩ := hparams
  have hwfChild : WellFormed
      (inputModel (childSubInput inp group) (childSubOptions o group)) :=
    (subInputWellFormedC2 inp o group hwf).1
  have hframedChild : framedParents (childSubInput inp group) = true :=
    (framedParentsSub inp o group hwf hframed).1
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  exact XG_routes_insetB exactIds fuel (childSubInput inp group)
    (childSubOptions o group) child hwfChild hframedChild hchild P hQchild

/-- Frame positivity for an executed exact call: the located group frame
dominates the reserved `childFrameSize`, positive from the pad, title, and
exact canvas-margin bounds. `XG_` copy of the private `stepC6_frame_pos`. -/
theorem XG_frame_posB (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      0 < frame.rect.w ∧ 0 < frame.rect.h := by
  intro frame hframe
  have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
  have hheightEq : titleHeight = (max 1 titleLines.length : Int) * P.lineH :=
    hparams.2.1
  have hwrapCtx : ExpandChildTitleWrapped P inp o group titleLines := hparams.2.2
  have hchild : layoutRecursiveB (layoutX exactIds) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child := hctxB.2.2.2.1
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
  have hcm := (exactCanvasMargins exactIds) fuel _ _ _ hchild P hP
  have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := hcm.1
  have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := hcm.2
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
  obtain ⟨hw, hh⟩ := XG_frame_size_bounds exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams frame titleLines
    hframe hwrapCtx
  omega
/-- `XG_` copy of the private `strictInside_contained`
(`ExpandChildC8bGeometryExecuted.lean`). -/
theorem XG_strictInside_contained {outer inner : Rect}
    (h : outer.StrictInside inner) : outer.Contained inner := by
  simp only [Rect.StrictInside, Rect.Contained] at h ⊢
  omega
/-- `XG_` copy of the private `strictInside_of_strictInside_contained`. -/
theorem XG_strictInside_of_contained {a b c : Rect}
    (hab : a.StrictInside b) (hbc : b.Contained c) : a.StrictInside c := by
  simp only [Rect.StrictInside, Rect.Contained] at *
  omega
/-- Scene box ids of the exact parent result stay nodup: the parent scene
boxes map to the parent sub-input box ids (via the exact C5 lift), which
are a sublist of the well-formed input's nodup ids. `XG_` copy of the
private `parent_scene_box_ids_nodup` (`ExpandChildC8GeometryProof.lean`). -/
theorem XG_parent_box_ids_nodupB (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    (parent.scene.boxes.map (·.id)).Nodup := by
  have hwf : WellFormed (inputModel inp o) := hctxB.1
  have hchild : layoutRecursiveB (layoutX exactIds) fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child := hctxB.2.2.2.1
  have hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent :=
    hctxB.2.2.2.2.1
  have hpboxes : (parentSubInput inp group P titleLines child).boxes =
      (selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes :=
    hctxB.2.2.1
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
  have hwrapCtx : ExpandChildTitleWrapped P inp o group titleLines := hparams.2.2
  have hmetric : metricOf o.profile = .ok hwrapCtx.choose := hwrapCtx.choose_spec.1
  have hwrapEq : StyledMeasure.wrap hwrapCtx.choose
      (Measure.wrapTarget hwrapCtx.choose.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD
        ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
        group.id).toList = .ok titleLines := hwrapCtx.choose_spec.2
  have hsub := subInputWellFormedB_layoutX exactIds fuel inp o group P
    hwrapCtx.choose titleLines child parent hwf hframed hP hmetric hwrapEq
    hchild hparent
  have hparentC5 := layoutRecursiveB_c5_facts (flatC5B_layoutX_closed exactIds)
    (subInputWellFormedB_layoutX exactIds) fuel hsub.2.2.1 hsub.2.2.2 hparent
  have hparentOutputIds : parent.scene.boxes.map (·.id) =
      (parentSubInput inp group P titleLines child).boxes.map (·.id) :=
    hparentC5.1
  have hparentIds : ((parentSubInput inp group P titleLines child).boxes.map
      (·.id)).Nodup := by
    rw [hpboxes, selectInput_box_ids]
    exact nodup_filter_map _ _ _ hboxIds
  rw [hparentOutputIds]
  exact hparentIds

/-- `stepC6Geometry` at the exact base from `stepC6Geometry_holdsB`: content
fit, child boxes, child routes, and frame positivity are proved below; the
two parent-scene facts stay as named single-fact residuals. -/
theorem stepC6Geometry_layoutX (exactIds : List String)
    (hDisjB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
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
        Disjoint frame.rect pb.rect)
    (hMissB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
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
        ¬ Polyline.hitsRect pr.points r) :
    XG_RecursiveStepFactsB (layoutX exactIds) ExpandChildC6Geometry :=
  stepC6Geometry_holdsB (layoutX exactIds) (XG_content_fit_strict exactIds)
    (XG_child_boxes_insetB exactIds) (XG_child_routes_insetB exactIds)
    hDisjB hMissB (XG_frame_posB exactIds)

/-- `stepC7Geometry` at the exact base, using the caller's `InputFixedFit`
to establish child containment and parent clearance. -/
theorem stepC7Geometry_layoutX (exactIds : List String)
    (hchildB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      InputFixedFit inp o →
      ExpandChildC7ChildInside P inp o group titleHeight parent child)
    (hparentB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      InputFixedFit inp o →
      ExpandChildC7ParentClear P inp o group titleHeight parent)
    (hcaptionB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7CaptionFit P inp o group titleHeight parent child res) :
    XG_RecursiveStepFactsB (layoutX exactIds)
      (fun P inp o group titleHeight parent child res =>
        InputFixedFit inp o →
          ExpandChildC7Geometry P inp o group titleHeight parent child res) := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams hfix
  have _hexpandEq := hexpand
  have _hframedEq := hframed
  have _hctxEq := hctxB
  have hchild := hchildB fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams hfix
  have hparent := hparentB fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams hfix
  have hcaption := hcaptionB fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨hchildBox, hchildLabel⟩ := hchild frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨hparentBox, hparentLabel⟩ := hparent frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨hclass, htitleIn, htitleClear⟩ := hcaption frame tl dx dy hframe hdx hdy hwrap
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cl hcl hown pb hpb hex hforeign
    have hcont : frame.rect.Contained (shiftRect dx dy cl.rect) :=
      hchildLabel cl hcl
    have hdisj : Disjoint frame.rect pb.rect :=
      hparentBox pb hpb hex hforeign
    exact disjoint_contained_left hcont hdisj
  · intro cb hcb hex rl hrl hown
    have hrect : rl.rect = groupTitleRect group P tl titleHeight frame :=
      hclass rl hrl hown
    have hdisj : Disjoint (groupTitleRect group P tl titleHeight frame)
        (shiftRect dx dy cb.rect) :=
      htitleClear cb hcb hex
    rw [hrect]
    exact hdisj
  · intro pl hpl hown cb hcb hex
    have hcont : frame.rect.Contained (shiftRect dx dy cb.rect) :=
      hchildBox cb hcb
    have hdisjFrame : Disjoint frame.rect pl.rect :=
      hparentLabel pl hpl hown
    have hdisj : Disjoint (shiftRect dx dy cb.rect) pl.rect :=
      disjoint_contained_left hcont hdisjFrame
    exact (Disjoint.comm _ _).mp hdisj
  · intro pb hpb hex hforeign rl hrl hown
    have hrect : rl.rect = groupTitleRect group P tl titleHeight frame :=
      hclass rl hrl hown
    have hdisj : Disjoint frame.rect pb.rect :=
      hparentBox pb hpb hex hforeign
    have hinner : Disjoint (groupTitleRect group P tl titleHeight frame) pb.rect :=
      disjoint_contained_left htitleIn hdisj
    rw [hrect]
    exact hinner

/-- Named single-fact residual for `stepC8bGeometry`: the C8b inset core
conditional at the exact base.  Strictly narrower than the field: every
per-call inset/caption/ancestry/parent premise is an extra hypothesis. -/
def XG_C8bCoreB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    (∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect) →
    (∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect) →
    (∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group titleLines' →
      frame.rect.StrictInside
        (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin))) →
    (∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group titleLines' →
      frame.rect.StrictInside (groupTitleRectC8 group P titleLines' titleHeight frame)) →
    (∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group titleLines' →
      Disjoint (groupTitleRectC8 group P titleLines' titleHeight frame)
        (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin))) →
    ExpandChildC8aAncestry group parent child res →
    ExpandChildParentFrame P inp o group titleHeight parent child →
    ExpandChildC8bGeometry P inp o group titleHeight parent child res

/-- `stepC8bGeometry` at the exact base, from the inset-core residual. -/
theorem stepC8bGeometry_layoutX (exactIds : List String)
    (hCore : XG_C8bCoreB exactIds)
    (hChildBoxesB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ cb ∈ child.scene.boxes,
        (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
    (hChildLabelsB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      InputFixedFit inp o →
      ∀ cl ∈ child.scene.labels,
        (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect)
    (hFitStrictB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
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
        (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)))
    (hCapStrictB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
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
      frame.rect.StrictInside (groupTitleRectC8 group P titleLines' titleHeight frame))
    (hCapDisjB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
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
        (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)))
    (hAncB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aAncestry group parent child res)
    (hParentFrameB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentFrame P inp o group titleHeight parent child) :
    XG_RecursiveStepFactsB (layoutX exactIds)
      (fun P inp o group titleHeight parent child res =>
        InputFixedFit inp o →
          ExpandChildC8bGeometry P inp o group titleHeight parent child res) := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams hfix
  exact hCore fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
    (hChildBoxesB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hChildLabelsB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams hfix)
    (hFitStrictB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hCapStrictB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hCapDisjB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hAncB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hParentFrameB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)

end PipelineImpl
end Layered
end Elegant

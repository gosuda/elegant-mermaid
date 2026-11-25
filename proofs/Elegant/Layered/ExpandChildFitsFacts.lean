import Elegant.Layered.PipelineFacts
import Elegant.Layered.SelectFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RecursiveC6
import Elegant.Layered.RecursiveFit

set_option autoImplicit false

/-!
# `ExpandChildFitAt` discharge for `layoutRecursive` expansion steps

`ExpandChildFits` (ExpandChildContainment.lean:92) quantifies the measured
title lines freely, so it is not provable from frame-size facts alone: the
shift `dx dy` depends on the measured title width, and only the
execution-pinned form `ExpandChildFitAt` (RecursiveFit.lean:202) relates the
shift to the `childFrameSize` reservation the parent recursion stored in
`fixedSizes`. This file discharges that pinned form for the expansion
`layoutRecursive` actually performs.

The argument reuses `layoutRecursive_embedding_assembly_sources`, which
already transports both box lookups through `expandChild`, and the
CaptionWidthFacts parent-frame derivation, which bounds the frame rectangle
by the stored `childFrameSize` entry. `childCanvas_contained` then turns the
size bound plus `P.canvasMargin ≤ P.clusterPad` into the frame fit.
-/

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound

/-- Fixed-size scene-box invariant at the flat leaf: a successful `layout`
produces a scene box whose rect dominates the declared `Size`. -/
theorem layout_fixed_size_scene_dims
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {entry : String × Size} {sz : Size}
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry)
    (hsz : entry.2 = sz) :
    ∃ box : Box,
      res.scene.layoutDump.box? source.id = some box ∧
      sz.w ≤ box.rect.w ∧ sz.h ≤ box.rect.h := by
  obtain ⟨box, hbox, hw, hh⟩ :=
    (Classical.choice (layout_sceneExecution h)).fixed_source_box_minimum_dimensions
      hids hsource hfixed
  exact ⟨box, hbox, by rw [← hsz]; exact hw, by rw [← hsz]; exact hh⟩

/-- Discharge of `ExpandChildFitAt` for the expansion step of a successful
`layoutRecursive (fuel + 1)` call. `hmargin` is the named obligation that
the canvas margin does not exceed the cluster pad, which
`childCanvas_contained` needs to turn the stored `childFrameSize`
reservation into a frame fit. -/
theorem expandChild_fits_of_recursion
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {group : ModelBox} {P : Params} {metric : Measure.Metric}
    {child : FamilyResult} {titleLines : List Measure.Line}
    {parent : FamilyResult} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
    (hmargin : P.canvasMargin ≤ P.clusterPad)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res)
    (hgroup : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hP : checkedParams o.profile inp.kind = .ok P)
    (hm : metricOf o.profile o.fontFamily = .ok metric)
    (hchild : layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child)
    (hwrap : StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines)
    (htitleH : titleHeight = (max 1 titleLines.length : Int) * P.lineH)
    (hparent : layoutRecursive fuel
        { (selectInput inp fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes :=
            (selectInput inp fun box => !Compound.inside inp.boxes group.id box.id).fixedSizes ++
              [(group.id, childFrameSize group.direction P.clusterPad
                (titleLines.foldl (fun width line => max width line.width) 0)
                ((max 1 titleLines.length : Int) * P.lineH)
                ⟨child.scene.canvas.w - 2 * P.canvasMargin,
                  child.scene.canvas.h - 2 * P.canvasMargin⟩)]
          fixedChildren :=
            (selectInput inp fun box => !Compound.inside inp.boxes group.id box.id).fixedChildren ++
              [(group.id, child.scene)]
          fixedAreas :=
            (selectInput inp fun box => !Compound.inside inp.boxes group.id box.id).fixedAreas ++
              [(group.id, child.itemArea)] } o = .ok parent) :
    ExpandChildFitAt P inp o group titleHeight parent child res := by
  intro frame fmetric ftLines _flines fdx fdy hframe hfmetric hftitle _hflines hdx hdy
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hcovered : RoutesCovered inp := inputRoutesCovered hwf
  obtain ⟨P', metric', child', titleLines', parent', frame', _lines', dx', dy',
      hP', hm', hchild', hwrap', hparent', _hexpand', hframe', _hlines',
      hdx', hdy', hchildLookup', hparentLookup', _hroutes', _hitems'⟩ :=
    layoutRecursive_embedding_assembly_sources hboxIds hcovered hgroup hrecursive
  have hPeq : P' = P := Except.ok.inj (hP'.symm.trans hP)
  have hmetric'eq : metric' = metric := Except.ok.inj (hm'.symm.trans hm)
  have hfmetriceq : fmetric = metric := Except.ok.inj (hfmetric.symm.trans hm)
  have hchild'eq : child' = child := Except.ok.inj (hchild'.symm.trans hchild)
  subst P'
  subst metric'
  subst fmetric
  subst child'
  have htitleLines'eq : titleLines' = titleLines :=
    Except.ok.inj (hwrap'.symm.trans hwrap)
  subst titleLines'
  have hftlineeq : ftLines = titleLines :=
    Except.ok.inj (hftitle.symm.trans hwrap)
  subst ftLines
  have hparent'eq : parent' = parent := Except.ok.inj (hparent'.symm.trans hparent)
  subst parent'
  have hframe'eq : frame' = frame :=
    Option.some.inj (hframe'.symm.trans hframe)
  subst frame'
  have hdx'eq : dx' = fdx := by
    have h1 : dx' = frame.rect.x +
        (childInset group.direction P.clusterPad
          (titleLines.foldl (fun width line => max width line.width) 0)
          ((max 1 titleLines.length : Int) * P.lineH)).x - P.canvasMargin := hdx'
    have h2 : fdx = frame.rect.x +
        (childInset group.direction P.clusterPad
          (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin := hdx
    rw [h1, h2, htitleH]
  have hdy'eq : dy' = fdy := by
    have h1 : dy' = frame.rect.y +
        (childInset group.direction P.clusterPad
          (titleLines.foldl (fun width line => max width line.width) 0)
          ((max 1 titleLines.length : Int) * P.lineH)).y - P.canvasMargin := hdy'
    have h2 : fdy = frame.rect.y +
        (childInset group.direction P.clusterPad
          (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin := hdy
    rw [h1, h2, htitleH]
  subst dx'
  subst dy'
  refine ⟨?_, ?_, ?_⟩
  · let baseParent := selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id)
    let size := childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0)
      ((max 1 titleLines.length : Int) * P.lineH)
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩
    let parentInput : Input := { baseParent with
      fixedSizes := baseParent.fixedSizes ++ [(group.id, size)]
      fixedChildren := baseParent.fixedChildren ++ [(group.id, child.scene)]
      fixedAreas := baseParent.fixedAreas ++ [(group.id, child.itemArea)] }
    have hparentAt : layoutRecursive fuel parentInput o = .ok parent := hparent
    have hparentIds : (parentInput.boxes.map (·.id)).Nodup := by
      change (baseParent.boxes.map (·.id)).Nodup
      rw [selectInput_box_ids]
      exact List.Nodup.sublist ((List.filter_sublist).map _) hboxIds
    have hparentCovered : RoutesCovered parentInput := by
      change RoutesCovered baseParent
      exact selectInput_routesCovered inp
        (fun box => !Compound.inside inp.boxes group.id box.id) ""
    have hparentOutputIds := (layoutRecursive_ids (fun _ _ _ h => layout_ids h)
      fuel parentInput o parent hparentCovered hparentAt).1
    have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
    have hparentSourceId : group.id ∈ parentInput.boxes.map (·.id) := by
      rw [← hparentOutputIds, ← hframeId]
      exact List.mem_map.mpr ⟨frame, List.mem_of_find?_eq_some hframe, rfl⟩
    obtain ⟨source, hsource, hsourceId⟩ := List.mem_map.mp hparentSourceId
    have hsourceBase : source ∈ baseParent.boxes := hsource
    obtain ⟨original, horiginal, _, hsourceEq⟩ :=
      selectInput_box_source inp (fun box => !Compound.inside inp.boxes group.id box.id)
        "" source hsourceBase
    have hsourceOriginalId : source.id = original.id := by
      rw [hsourceEq]
      split <;> rfl
    have horiginalId : original.id = group.id := hsourceOriginalId.symm.trans hsourceId
    have horiginalLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hboxIds original horiginal
    have hgroupLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hboxIds group
      (List.mem_of_find?_eq_some hgroup)
    rw [horiginalId] at horiginalLookup
    have horiginalEq : original = group :=
      Option.some.inj (horiginalLookup.symm.trans hgroupLookup)
    have hnotfixed : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
      have hs := List.find?_some hgroup
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
      exact hs.2
    have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
      List.find?_eq_none.mpr (List.any_eq_false.mp hnotfixed)
    have hfixed : parentInput.fixedSizes.find? (fun fixed => fixed.1 == source.id) =
        some (group.id, size) := by
      change (inp.fixedSizes ++ [(group.id, size)]).find?
        (fun fixed => fixed.1 == source.id) = some (group.id, size)
      simp [List.find?_append, hsourceId, hnone]
    obtain ⟨actual, hactual, _, hw, hh⟩ :=
      layoutRecursive_fixed_source_box_minimum_dimensions_with_role fuel
        hparentIds hparentCovered hparentAt hsource hfixed
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
      rw [← htitleH] at hw''
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
      rw [← htitleH] at hh''
      exact hh''
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
      rw [htitleH]
      exact Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP)
    rw [hdx, hdy]
    exact childCanvas_contained htw hth hmargin hw' hh'
  · intro box hb
    simp only [← htitleH, ← hdx, ← hdy] at hchildLookup'
    exact hchildLookup' box hb
  · intro box hb
    exact hparentLookup' box hb

end Elegant.Layered.PipelineImpl

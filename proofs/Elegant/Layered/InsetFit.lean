import Elegant.Layered.RecursiveFit
import Elegant.Layered.RecursiveC2
import Elegant.Layered.ExpandChildFitsFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.SelectFacts
import Elegant.Layered.RecursiveC1C3

set_option autoImplicit false

/-!
# Inset containment: C1/C3 recursion lift without `canvasMargin ≤ clusterPad`

`childCanvas_contained` (RecursiveFit) discharges `ExpandChildFitAt` only under
the premise `P.canvasMargin ≤ P.clusterPad`, which is false for `usecase` on
the vector profile (`diagram_padding` 1280 > `cluster_pad` 1024). What C1 and
C3 actually need is weaker: every scene box lies in the *inset* canvas
`⟨margin, margin, canvas.w - 2*margin, canvas.h - 2*margin⟩`, and in the
recursion the shifted child inset fits inside the group frame for every
margin because the frame reserves `childFrameSize`, which dominates the inset
content plus padding on every side.

This file proves, over the executed definitions:

* `layout_inset`: the flat `layout` places every box inside the margin inset
  of its canvas (`0 ≤ P.canvasMargin` included).
* `layoutRecursive_inset`: the same invariant through `layoutRecursive`, by
  fuel induction; `expandChild` keeps the parent canvas and the shifted child
  inset lands inside the group frame.
* `layoutRecursive_childInset_fits_frame`: the frame fit for the shifted
  child inset in the actual recursion context (no margin-vs-pad premise).
* `layoutRecursive_c1_c3_of_inset`: the C1/C3 lift. C1 follows from inset ⊆
  canvas; C3 reuses the expansion argument with the inset geometry.
-/

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound

/-- The canvas with a uniform `m` inset removed on every side. -/
def insetRect (c : Size) (m : Int) : Rect := ⟨m, m, c.w - 2 * m, c.h - 2 * m⟩

/-- The full canvas rectangle contains a nonnegative inset: `Contained` has
the container as its first argument. -/
theorem insetRect_subset_canvas {c : Size} {m : Int} (hm : 0 ≤ m) :
    (Validator.canvasRect ⟨c, [], [], []⟩).Contained (insetRect c m) := by
  simp only [insetRect, Validator.canvasRect, Rect.Contained]
  omega

/-- `InsetC1`: every scene box lies in the margin inset of the canvas. This is
the flat C1 strengthened to the inset; `Validator.C1` follows because the
inset is contained in the canvas for `m ≥ 0`. -/
def InsetC1 (scene : Scene) (m : Int) : Prop :=
  ∀ b ∈ scene.boxes, (insetRect scene.canvas m).Contained b.rect

/-- Inset counterpart of `orient_shiftRect_containsCellRect`: a packed rect
inside `⟨0..W⟩ × ⟨0..H⟩` lands inside the margin inset of the oriented
expanded canvas, for every direction and every nonnegative margin. -/
theorem orient_shiftRect_inset_containsCellRect (d : Direction) (W H margin : Int) (r : Rect)
    (hr : 0 ≤ r.x ∧ r.x + r.w ≤ W ∧ 0 ≤ r.y ∧ r.y + r.h ≤ H ∧ 0 ≤ r.w ∧ 0 ≤ r.h)
    (_hm : 0 ≤ margin) :
    (insetRect (orientCanvas d (W + 2 * margin) (H + 2 * margin)) margin).Contained
      (shiftRect margin margin (orientRect d H r)) := by
  unfold insetRect shiftRect orientRect orientCanvas Rect.Contained
  cases d <;> dsimp <;> omega

/-- Inset counterpart of `sceneOf_boxes_bounded`: when the packed accumulator
satisfies packing bounds, every scene box lies in the margin inset of the
scene canvas. -/
theorem sceneOf_boxes_inset (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel)
    (hacc : AccBounded acc.canvasW acc.canvasH acc)
    (hmargin : 0 ≤ P.canvasMargin) :
    ∀ b ∈ (sceneOf P inp o lines acc measured).boxes,
      (insetRect (sceneOf P inp o lines acc measured).canvas P.canvasMargin).Contained b.rect := by
  intro b hb
  obtain ⟨hi0, hiEq⟩ := List.mem_iff_getElem?.mp hb
  have hzip : ((sceneOf P inp o lines acc measured).boxes.zipIdx)[hi0]? = some (b, hi0) := by
    rw [List.getElem?_zipIdx, hiEq]
    simp
  refine ?_
  have hq := List.mem_of_getElem? hzip
  unfold sceneOf at hq ⊢
  dsimp only at hq ⊢
  obtain ⟨_, heq⟩ := List.getElem?_eq_some_iff.mp
    (List.mem_zipIdx_iff_getElem?.mp hq)
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at heq
  rw [← heq]
  dsimp only
  have hr' : 0 ≤ (acc.rects.getD hi0 default).x ∧
      (acc.rects.getD hi0 default).x + (acc.rects.getD hi0 default).w ≤ acc.canvasW ∧
      0 ≤ (acc.rects.getD hi0 default).y ∧
      (acc.rects.getD hi0 default).y + (acc.rects.getD hi0 default).h ≤ acc.canvasH ∧
      0 ≤ (acc.rects.getD hi0 default).w ∧
      0 ≤ (acc.rects.getD hi0 default).h := by
    cases hget : acc.rects[hi0]? with
    | none =>
      have hdef : acc.rects.getD hi0 default = default := by
        simp [Array.getD_eq_getD_getElem?, hget]
      rw [hdef]
      change 0 ≤ (0 : Int) ∧ 0 ≤ acc.canvasW ∧ 0 ≤ (0 : Int) ∧
        0 ≤ acc.canvasH ∧ 0 ≤ (0 : Int) ∧ 0 ≤ (0 : Int)
      exact ⟨by omega, hacc.canvas_w_nonneg, by omega, hacc.canvas_h_nonneg,
        by omega, by omega⟩
    | some r =>
      rw [Array.getD_eq_getD_getElem?, hget]
      exact hacc.rects_bounded hi0 r hget
  exact orient_shiftRect_inset_containsCellRect o.direction acc.canvasW acc.canvasH
    P.canvasMargin _ hr' hmargin

/-- The flat `layout` keeps every box inside the margin inset of its canvas,
with the parameters the execution actually used. -/
theorem layout_inset {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) :
    ∃ P : Params, checkedParams o.profile inp.kind = .ok P ∧
      0 ≤ P.canvasMargin ∧ InsetC1 res.scene P.canvasMargin := by
  let execution := Classical.choice (layout_sceneExecution h)
  have hacc := execution.packedAcc_bounded execution.components_parts_bounded
  have hm1 := checkedParams_canvasMargin_ge_one execution.checked
  refine ⟨execution.params, execution.checked, by omega, ?_⟩
  rw [execution.scene_eq]
  exact sceneOf_boxes_inset execution.params inp o execution.lines
    execution.packedAcc execution.measured hacc (by omega)

/-- The shifted child *inset* canvas fits inside a frame whose width and
height dominate `childFrameSize`, WITHOUT any `margin ≤ pad` premise: the
frame reserves `childInset` plus content on every side, and the inset removes
exactly the margin the shift adds back. Pure arithmetic over the direction
branches; only the title width/height and the cluster pad must be
nonnegative. -/
theorem childInsetCanvas_contained {direction : String}
    {pad titleWidth titleHeight margin cw ch fw fh fx fy : Int}
    (htw : 0 ≤ titleWidth) (hth : 0 ≤ titleHeight) (hpad : 0 ≤ pad)
    (hfw : (childFrameSize direction pad titleWidth titleHeight
      ⟨cw - 2 * margin, ch - 2 * margin⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad titleWidth titleHeight
      ⟨cw - 2 * margin, ch - 2 * margin⟩).h ≤ fh) :
    (⟨fx, fy, fw, fh⟩ : Rect).Contained
      (shiftRect (fx + (childInset direction pad titleWidth titleHeight).x - margin)
        (fy + (childInset direction pad titleWidth titleHeight).y - margin)
        (insetRect ⟨cw, ch⟩ margin)) := by
  unfold childInset shiftRect insetRect Rect.Contained
  unfold childFrameSize at hfw hfh
  split <;> split at hfw <;> split at hfh <;> simp_all <;> omega

/-- The frame fit for the shifted child *inset* canvas in the actual
recursion context, WITHOUT any `canvasMargin ≤ clusterPad` premise: the
frame reserves `childFrameSize` computed from the inset content, and the
shift plus the inset cancel the margin on every side. -/
theorem layoutRecursive_childInset_fits_frame
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {group : ModelBox} {P : Params} {metric : Measure.Metric}
    {child : FamilyResult} {titleLines : List Measure.Line}
    {parent : FamilyResult} {titleHeight : Int}
    (hwf : WellFormed (inputModel inp o))
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
              [(group.id, child.itemArea)] } o = .ok parent)
    (frame : Box) (fdx fdy : Int)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hdx : fdx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin)
    (hdy : fdy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin) :
    frame.rect.Contained (shiftRect fdx fdy (insetRect child.scene.canvas P.canvasMargin)) := by
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hcovered : RoutesCovered inp := inputRoutesCovered hwf
  obtain ⟨P', metric', child', titleLines', parent', frame', _lines', dx', dy',
      hP', hm', hchild', hwrap', hparent', _hexpand', hframe', _hlines',
      _hdx', _hdy', _hchildLookup', _hparentLookup', _hroutes', _hitems'⟩ :=
    layoutRecursive_embedding_assembly_sources hboxIds hcovered hgroup hrecursive
  have hPeq : P' = P := Except.ok.inj (hP'.symm.trans hP)
  have hmetric'eq : metric' = metric := Except.ok.inj (hm'.symm.trans hm)
  have hchild'eq : child' = child := Except.ok.inj (hchild'.symm.trans hchild)
  subst P'
  subst metric'
  subst child'
  have htitleLines'eq : titleLines' = titleLines :=
    Except.ok.inj (hwrap'.symm.trans hwrap)
  subst titleLines'
  have hparent'eq : parent' = parent := Except.ok.inj (hparent'.symm.trans hparent)
  subst parent'
  have hframe'eq : frame' = frame :=
    Option.some.inj (hframe'.symm.trans hframe)
  subst frame'
  let baseParent := selectInput inp
    (fun box => !Compound.inside inp.boxes group.id box.id)
  let size := childFrameSize group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩
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
    intro ls ac hac
    induction ls generalizing ac with
    | nil => simpa using hac
    | cons line ls ih =>
      simp only [List.foldl_cons]
      exact ih _ (Int.le_trans hac (Int.le_max_left _ _))
  have hth : 0 ≤ titleHeight := by
    rw [htitleH]
    exact Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP)
  rw [hdx, hdy]
  exact childInsetCanvas_contained htw hth (checkedParams_clusterPad_nonneg hP) hw' hh'

/-- The inset invariant through `layoutRecursive`: for every fuel, a
successful recursion places every scene box inside the canvas inset by the
canvas margin of the parameters checked for THAT input's kind (the same
constant at every level, because `selectInput` keeps `kind` and
`expandChild` keeps the parent canvas). `hsub` is the sanctioned
`SubInputWellFormedC2` seam of `RecursiveC2.lean` that transports the
well-formedness premise to the two sub-inputs of every expansion. -/
theorem layoutRecursive_inset (fuel : Nat) (hsub : SubInputWellFormedC2) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) →
      layoutRecursive fuel inp o = .ok res →
      ∀ Q : Params, checkedParams o.profile inp.kind = .ok Q →
        0 ≤ Q.canvasMargin ∧ InsetC1 res.scene Q.canvasMargin := by
  induction fuel with
  | zero =>
    intro inp o res _hwf h Q hQ
    obtain ⟨P', hchecked, hm, hinset⟩ := layout_inset h
    have hQm : P' = Q := Except.ok.inj (hchecked.symm.trans hQ)
    subst hQm
    exact ⟨hm, hinset⟩
  | succ fuel ih =>
    intro inp o res hwf h Q hQ
    rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
      ⟨group, Pm, metric, child, titleLines, parent, hg, hPm, hm, hc, ht, hp, hexpand⟩
    · obtain ⟨P', hchecked, hm, hinset⟩ := layout_inset hlayout
      have hQm : P' = Q := Except.ok.inj (hchecked.symm.trans hQ)
      subst hQm
      exact ⟨hm, hinset⟩
    · have hQm : Pm = Q := Except.ok.inj (hPm.symm.trans hQ)
      subst hQm
      obtain ⟨hwfChild, hparentWF⟩ := hsub inp o group hwf
      have hQchild : checkedParams
          { o with direction := directionOf group.direction }.profile
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id)
            group.id).kind = .ok Pm := hQ
      have hcIH := ih _ _ _ hwfChild hc Pm hQchild
      have hQparent : checkedParams o.profile
          (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).kind =
          .ok Pm := hQ
      have hpIH := ih _ _ _ (hparentWF _ _ _) hp Pm hQparent
      obtain ⟨frame, fm, ftl, _fl, dx, dy, hframe, hmEq, htlEq, _hlEq,
        hdx, hdy, hcanvas, hboxes⟩ := expandChild_sources hexpand
      have hfmEq : fm = metric := Except.ok.inj (hmEq.symm.trans hm)
      subst hfmEq
      have hftlEq : ftl = titleLines := Except.ok.inj (htlEq.symm.trans ht)
      subst hftlEq
      have hFit := layoutRecursive_childInset_fits_frame hwf h hg hQ hm hc ht
        rfl hp frame dx dy hframe hdx hdy
      refine ⟨hpIH.1, ?_⟩
      unfold InsetC1
      rw [hcanvas]
      intro b hb
      have hbMem : b ∈ res.scene.boxes := hb
      rw [hboxes] at hbMem
      obtain ⟨_, -, hfind⟩ := List.mem_filterMap.mp hbMem
      have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hfind
      have hFrameInInset : (insetRect parent.scene.canvas Pm.canvasMargin).Contained
          frame.rect := hpIH.2 frame (List.mem_of_find?_eq_some hframe)
      rcases List.mem_append.mp hbItems with hbc | hbp
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hbc
        have hshift :
            (shiftRect dx dy (insetRect child.scene.canvas Pm.canvasMargin)).Contained
              (shiftRect dx dy c.rect) :=
          (contained_shiftRect dx dy).mpr (hcIH.2 c hc)
        exact Rect.Contained.trans hFrameInInset (Rect.Contained.trans hFit hshift)
      · exact hpIH.2 b hbp

/-- The geometric and lookup premises `expandChild` needs for C1 and C3 when
the child evidence is the inset invariant (every child box inside the
inset canvas) instead of the whole-child-canvas fit: for any frame, title
lines, and offsets satisfying the executed `expandChild` equations — the
title-wrap hypothesis pins `titleLines` to the actually wrapped lines — the
child inset shifted by the offsets stays inside the frame, and both lookup
transports hold at the same offsets. -/
def ExpandChildFitsInset (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    (∃ metric : Measure.Metric, metricOf o.profile o.fontFamily = .ok metric ∧
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines) →
    frame.rect.Contained
        (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) ∧
    (∀ box : Box, child.scene.layoutDump.box? box.id = some box →
      result.scene.layoutDump.box? box.id = some (embedBox group.id dx dy box)) ∧
    (∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
      result.scene.layoutDump.box? box.id = some box)

/-- `expandChild` preserves C1 and C3 with the inset child evidence: parent
boxes keep their containment in the unchanged canvas; shifted child boxes
land inside the group frame through the child inset and the frame fit;
deeper child boxes keep their shifted parent containment; rewritten child
roots are contained in the frame. -/
theorem expandChild_c1_c3_inset
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child result : FamilyResult}
    (_hmargin : 0 ≤ P.canvasMargin)
    (hparentC1 : Validator.C1 parent.scene.layoutDump)
    (hparentC3 : Validator.C3 parent.scene.layoutDump)
    (hchildInset : InsetC1 child.scene P.canvasMargin)
    (hchildC3 : Validator.C3 child.scene.layoutDump)
    (hfit : ExpandChildFitsInset P inp o group titleHeight parent child result)
    (hparentClosed : SceneParentClosed parent.scene)
    (hchildClosed : SceneParentClosed child.scene)
    (h : expandChild P inp o group titleHeight parent child = .ok result) :
    Validator.C1 result.scene.layoutDump ∧ Validator.C3 result.scene.layoutDump := by
  obtain ⟨frame, metric, ftl, _fl, dx, dy, hframe, hmEq, htlEq, _hlEq,
    hdxEq, hdyEq, hcanvas, hboxes⟩ := expandChild_sources h
  obtain ⟨hfitC, hchildLookupT, hparentLookupT⟩ :=
    hfit frame ftl dx dy hframe hdxEq hdyEq ⟨metric, hmEq, htlEq⟩
  refine ⟨?_, ?_⟩
  · intro b hb
    have hbMem : b ∈ result.scene.layoutDump.boxes := hb
    simp only [Scene.layoutDump] at hbMem
    change b ∈ result.scene.boxes at hbMem
    rw [hboxes] at hbMem
    obtain ⟨_, -, hfind⟩ := List.mem_filterMap.mp hbMem
    have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes := List.mem_of_find?_eq_some hfind
    have hcanvasRect : Validator.canvasRect result.scene.layoutDump =
        Validator.canvasRect parent.scene.layoutDump := by
      unfold Validator.canvasRect
      have : result.scene.layoutDump.canvas = parent.scene.layoutDump.canvas := hcanvas
      rw [this]
    have hframeMem : frame ∈ parent.scene.boxes := List.mem_of_find?_eq_some hframe
    have hframeC1 : (Validator.canvasRect result.scene.layoutDump).Contained frame.rect := by
      rw [hcanvasRect]
      exact hparentC1 frame hframeMem
    rcases List.mem_append.mp hbItems with hbc | hbp
    · obtain ⟨c, hc, hbEq⟩ := List.mem_map.mp hbc
      have hshift :
          (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)).Contained
            (shiftRect dx dy c.rect) := (contained_shiftRect dx dy).mpr (hchildInset c hc)
      rw [← hbEq]
      exact Rect.Contained.trans hframeC1 (Rect.Contained.trans hfitC hshift)
    · rw [hcanvasRect]
      exact hparentC1 b hbp
  · intro b hb hbne p hp
    have hbMem : b ∈ result.scene.layoutDump.boxes := hb
    simp only [Scene.layoutDump] at hbMem
    change b ∈ result.scene.boxes at hbMem
    rw [hboxes] at hbMem
    obtain ⟨_, -, hfind⟩ := List.mem_filterMap.mp hbMem
    have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes := List.mem_of_find?_eq_some hfind
    rcases List.mem_append.mp hbItems with hbc | hbp
    · obtain ⟨c, hc, hbEq⟩ := List.mem_map.mp hbc
      by_cases hcp : c.parent = ""
      · -- child root: the parent is rewritten to `group.id`, and the frame contains it
        have hbParentEq : b.parent = group.id := by
          have hproj : b.parent = (if c.parent == "" then group.id else c.parent) := by
            rw [← hbEq]; rfl
          rw [hproj]
          simp [hcp]
        have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
        have hframeSelf : parent.scene.layoutDump.box? frame.id = some frame := by
          rw [hframeId]
          exact hframe
        have hresultLookup := hparentLookupT frame hframeSelf
        rw [hframeId] at hresultLookup
        rw [hbParentEq] at hp
        rw [hresultLookup] at hp
        have hpEq : frame = p := Option.some.inj hp
        subst hpEq
        have hshift :
            (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)).Contained
              (shiftRect dx dy c.rect) := (contained_shiftRect dx dy).mpr (hchildInset c hc)
        rw [← hbEq]
        exact Rect.Contained.trans hfitC hshift
      · -- deeper child box: shift the child parent containment
        have hbParentEq : b.parent = c.parent := by
          have hproj : b.parent = (if c.parent == "" then group.id else c.parent) := by
            rw [← hbEq]; rfl
          rw [hproj]
          simp [hcp]
        rcases hchildClosed c hc with hcpEmpty | ⟨p', hp'mem, hp'id⟩
        · exact absurd hcpEmpty hcp
        · have hfindNe :
              child.scene.boxes.find? (fun candidate => candidate.id == c.parent) ≠ none := by
            intro hnone
            rw [List.find?_eq_none] at hnone
            exact absurd (hnone p' hp'mem) (by simp [hp'id])
          cases hfind2 :
              child.scene.boxes.find? (fun candidate => candidate.id == c.parent) with
          | none => exact absurd hfind2 hfindNe
          | some q =>
            have hchildLookup : child.scene.layoutDump.box? c.parent = some q := hfind2
            have hC3 := hchildC3 c hc hcp q hchildLookup
            have hqid : q.id = c.parent := by simpa using List.find?_some hfind2
            have hqSelf : child.scene.layoutDump.box? q.id = some q := by
              rw [hqid]
              exact hchildLookup
            have hqImg := hchildLookupT q hqSelf
            rw [hqid] at hqImg
            rw [hbParentEq] at hp
            rw [hqImg] at hp
            have hpEq : embedBox group.id dx dy q = p := Option.some.inj hp
            subst hpEq
            rw [← hbEq]
            exact (contained_shiftRect dx dy).mpr hC3
    · -- parent box: the parent stays put
      rcases hparentClosed b hbp with hempty | ⟨p', hp'mem, hp'id⟩
      · exact absurd hempty hbne
      · have hfindNe :
              parent.scene.boxes.find? (fun candidate => candidate.id == b.parent) ≠ none := by
          intro hnone
          rw [List.find?_eq_none] at hnone
          exact absurd (hnone p' hp'mem) (by simp [hp'id])
        cases hfind2 :
            parent.scene.boxes.find? (fun candidate => candidate.id == b.parent) with
        | none => exact absurd hfind2 hfindNe
        | some q =>
          have hparentLookup : parent.scene.layoutDump.box? b.parent = some q := hfind2
          have hC3 := hparentC3 b hbp hbne q hparentLookup
          have hqid : q.id = b.parent := by simpa using List.find?_some hfind2
          have hqSelf : parent.scene.layoutDump.box? q.id = some q := by
            rw [hqid]
            exact hparentLookup
          have hqImg := hparentLookupT q hqSelf
          rw [← hqid] at hp
          rw [hqImg] at hp
          have hpEq : q = p := Option.some.inj hp
          subst hpEq
          exact hC3

/-- The flat C3 clause, with the premise shape the flat worker states. -/
abbrev FlatC3' : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    layout inp o = .ok res → Validator.C3 res.scene.layoutDump

/-- `framedParents` survives the two `selectInput` sub-inputs of every
expansion, in the corrected form `FramedParentsSub.lean` proves: the inside
sub-input needs `WellFormed` (unique ids) and the parent sub-input is the
one `layoutRecursive` builds, whose fixed side tables are the caller's tables
extended by the expanded group. -/
abbrev FramedParentsSub : Prop :=
  ∀ (inp : Input) (o : Options) (group : ModelBox),
    WellFormed (inputModel inp o) → framedParents inp = true →
    framedParents (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) = true ∧
    ∀ (size : Size) (scene : Scene) (area : Int),
      framedParents { selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := inp.fixedSizes ++ [(group.id, size)],
        fixedChildren := inp.fixedChildren ++ [(group.id, scene)],
        fixedAreas := inp.fixedAreas ++ [(group.id, area)] } = true

/-- The C1/C3 lift over `layoutRecursive`, WITHOUT any
`canvasMargin ≤ clusterPad` premise: C1 comes from the inset invariant
(`layoutRecursive_inset`), C3 from the flat clause plus the inset expansion
argument. Parent closedness of the produced scenes is the real
`layoutRecursive_parent_closed_wellFormed`; `framedParents` preservation is
the corrected seam `FramedParentsSub` (proved in `FramedParentsSub.lean`); `SubInputWellFormedC2` transports
well-formedness to the sub-inputs. -/
theorem layoutRecursive_c1_c3_of_inset (hsub : SubInputWellFormedC2)
    (hframedSub : FramedParentsSub) (hflat3 : FlatC3') (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursive fuel inp o = .ok res →
      Validator.C1 res.scene.layoutDump ∧ Validator.C3 res.scene.layoutDump := by
  induction fuel with
  | zero =>
    intro inp o res hwf hframed h
    refine ⟨?_, hflat3 inp o res hwf hframed h⟩
    intro b hb
    obtain ⟨P', _, hmargin, hinset⟩ := layout_inset h
    exact Rect.Contained.trans (insetRect_subset_canvas hmargin) (hinset b hb)
  | succ fuel ih =>
    intro inp o res hwf hframed h
    rcases layoutRecursive_succ h with ⟨_, hlayout⟩ | ⟨group, hg, _⟩
    · refine ⟨?_, hflat3 inp o res hwf hframed hlayout⟩
      intro b hb
      obtain ⟨P', _, hmargin, hinset⟩ := layout_inset hlayout
      exact Rect.Contained.trans (insetRect_subset_canvas hmargin) (hinset b hb)
    · obtain ⟨P', metric', child', titleLines', parent', frame, _lines', dx, dy,
        hP', hm', hchild', hwrap', hparent', hexpand', hframe', _hlines',
        hdxEq, hdyEq, hchildLookup', hparentLookup', _hroutes', _hitems'⟩ :=
        layoutRecursive_embedding_assembly_sources (Model.boxIds_nodup hwf)
          (inputRoutesCovered hwf) hg h
      obtain ⟨hwfChild, hparentWF⟩ := hsub inp o group hwf
      obtain ⟨hframedChild, hframedParent⟩ := hframedSub inp o group hwf hframed
      have hQchild : checkedParams
          { o with direction := directionOf group.direction }.profile
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id)
            group.id).kind = .ok P' := hP'
      have hcIH := ih _ _ _ hwfChild hframedChild hchild'
      have hpIH := ih _ _ _ (hparentWF _ _ _) (hframedParent _ _ _) hparent'
      have hmargin : 0 ≤ P'.canvasMargin := by
        have := checkedParams_canvasMargin_ge_one hP'
        omega
      have hchildInset :=
        (layoutRecursive_inset fuel hsub _ _ _ hwfChild hchild' P' hQchild).2
      have hFitInset : ExpandChildFitsInset P' inp o group
          ((max 1 titleLines'.length : Int) * P'.lineH) parent' child' res := by
        intro frame'' titleLines'' fdx fdy hframeLookup hfdxEq hfdyEq hwrap''
        obtain ⟨metric'', hm'', htl''⟩ := hwrap''
        have hmetricEq : metric'' = metric' := Except.ok.inj (hm''.symm.trans hm')
        have htlEq : titleLines'' = titleLines' := by
          rw [hmetricEq] at htl''
          exact Except.ok.inj (htl''.symm.trans hwrap')
        have hframeEq : frame'' = frame :=
          Option.some.inj (hframeLookup.symm.trans hframe')
        have hfdxDx : fdx = dx := by
          rw [hfdxEq, hframeEq, htlEq, ← hdxEq]
        have hfdyDy : fdy = dy := by
          rw [hfdyEq, hframeEq, htlEq, ← hdyEq]
        refine ⟨?_, ?_, ?_⟩
        · rw [hfdxDx, hfdyDy, hframeEq]
          exact layoutRecursive_childInset_fits_frame hwf h hg hP' hm' hchild' hwrap'
            rfl hparent' frame dx dy hframe' hdxEq hdyEq
        · intro box hbox
          rw [hfdxDx, hfdyDy]
          exact hchildLookup' box hbox
        · exact fun box hbox => hparentLookup' box hbox
      have hcl := layoutRecursive_parent_closed_wellFormed hwfChild fuel child' hchild'
      have hpl := layoutRecursive_parent_closed_wellFormed (hparentWF _ _ _) fuel
        parent' hparent'
      exact expandChild_c1_c3_inset hmargin hpIH.1 hpIH.2 hchildInset hcIH.2
        hFitInset hpl hcl hexpand'

end Elegant.Layered.PipelineImpl

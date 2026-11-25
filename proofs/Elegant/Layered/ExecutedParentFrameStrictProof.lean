import Elegant.Layered.ExpandChildC8aGeometryExecuted
import Elegant.Layered.ExpandChildTitleBandProof
import Elegant.Layered.ExpandChildAncestryProof
import Elegant.Layered.ExpandChildParentFixedForeignProof
import Elegant.Layered.ExpandChildLabelFactsProof
import Elegant.Layered.ExpandChildFitPerCallProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.BracketInsidePremisesProof
import Elegant.Layered.DummyNestedMarkerProof
import Elegant.Layered.TitleCopySpanProof
import Elegant.Layered.ForeignSpansClosed
import Elegant.Layered.SubInputWellFormedFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Validator

/-- The cases to exclude after tracing strict containment through assembly.
`FitReached` records the descent from the original parent sub-input. -/
inductive ExecutedParentFrameObstruction (root : Input) (options : Options) : Prop where
  | flat {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
      {frame : Box} {label : SceneLabel}
      (reached : FitReached root options inp o)
      (wellFormed : WellFormed (inputModel inp o)) (framed : framedParents inp = true)
      (run : layout inp o = .ok res)
      (fixed : ∃ size, (group.id, size) ∈ inp.fixedSizes)
      (frameLookup : res.scene.boxes.find? (fun box => box.id == group.id) = some frame)
      (role : frame.role = "group") (member : label ∈ res.scene.labels)
      (foreignOwner : label.owner ≠ group.id) (inside : frame.rect.StrictInside label.rect)
  | childLabel {fuel : Nat} {P : Params} {inp : Input} {o : Options}
      {inner group : ModelBox} {titleLines : List Measure.Line} {titleHeight : Int}
      {parent child res : FamilyResult} {frame tracked : Box} {label merged : SceneLabel} {dx dy : Int}
      (reached : FitReached root options inp o)
      (ctx : ExpandChildCallContext fuel P inp o inner titleLines titleHeight parent child res)
      (params : ExpandChildCallParams P inp o inner titleLines titleHeight)
      (framed : framedParents inp = true)
      (fixed : ∃ size, (group.id, size) ∈ inp.fixedSizes)
      (frameLookup : parent.scene.boxes.find? (fun box => box.id == inner.id) = some frame)
      (trackedLookup : parent.scene.boxes.find? (fun box => box.id == group.id) = some tracked)
      (role : tracked.role = "group")
      (offsetX : dx = frame.rect.x + (childInset inner.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x - P.canvasMargin)
      (offsetY : dy = frame.rect.y + (childInset inner.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y - P.canvasMargin)
      (member : label ∈ child.scene.labels)
      (foreignOwner : label.owner ≠ group.id) (notCaption : label.owner ≠ inner.id)
      (emitted : merged ∈ res.scene.labels) (owner : merged.owner = label.owner)
      (rect : merged.rect = shiftRect dx dy label.rect)
      (inside : tracked.rect.StrictInside (shiftRect dx dy label.rect))
      (notFit : ¬ ((insetRect child.scene.canvas P.canvasMargin).Contained label.rect ∧
        0 ≤ label.rect.w ∧ 0 ≤ label.rect.h))

private theorem executedFrameC8aStep : RecursiveStepFacts ExpandChildC8aStep :=
  expandChild_c8a_step_of_geometry stepC8aGeometry_holds (by
    intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
    exact expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx
      (stepC8aAncestry_holds fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams))

private theorem executedFrameFlatC8a : FlatC8a := by
  exact flatC8a_of_span_seams foreignBorderSpansSeparated_closed foreignNonGroupSpansClear_closed
    (fun _ _ _ hwf hfp => bracketInsidePremises
      (fun execution => dummyInsideProxyRowClear_executed' execution hwf hfp)
      (fun execution => titleCopySpanClearStrict_executed hwf hfp execution))

private theorem executedFrameLookup {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (run : layoutRecursive fuel inp o = .ok res)
    (frame : Box) (member : frame ∈ res.scene.boxes) :
    res.scene.boxes.find? (fun box => box.id == frame.id) = some frame := by
  have ids := layoutRecursive_ids (fun _ _ _ h => layout_ids h) fuel inp o res
    (routesCovered_of_wellFormed hwf) run
  have distinct : (res.scene.boxes.map (·.id)).Nodup := by
    rw [ids.1]
    exact Model.boxIds_nodup hwf
  exact Assembly.keyed_lookup_eq (·.id) _ distinct frame member

private theorem strictInsideTrans {a b c : Rect}
    (hab : a.StrictInside b) (hbc : b.StrictInside c) : a.StrictInside c := by
  simp only [Rect.StrictInside] at *
  omega

private theorem sharedStrictInside {a b label : Rect}
    (ha : a.StrictInside label) (hb : b.StrictInside label)
    (hw : 0 ≤ label.w) (hh : 0 ≤ label.h) : a.meetsInterior b := by
  simp only [Rect.StrictInside, Rect.meetsInterior] at *
  constructor <;> omega

private theorem foldedTitleWidth_nonneg (lines : List Measure.Line) (width : Int)
    (hw : 0 ≤ width) : 0 ≤ lines.foldl (fun w line => max w line.width) width := by
  induction lines generalizing width with
  | nil => exact hw
  | cons line lines ih => exact ih _ (Int.le_trans hw (Int.le_max_left _ _))

private theorem installedCaption_not_in_child {direction : String}
    {pad tw th margin dx dy : Int} {frame box : Rect} {canvas : Size}
    (htw : 0 ≤ tw) (hth : 0 ≤ th)
    (hfw : (childFrameSize direction pad tw th ⟨canvas.w - 2 * margin, canvas.h - 2 * margin⟩).w ≤ frame.w)
    (hfh : (childFrameSize direction pad tw th ⟨canvas.w - 2 * margin, canvas.h - 2 * margin⟩).h ≤ frame.h)
    (hdx : dx = frame.x + (childInset direction pad tw th).x - margin)
    (hdy : dy = frame.y + (childInset direction pad tw th).y - margin)
    (hbox : (insetRect canvas margin).Contained box) :
    ¬ (shiftRect dx dy box).StrictInside (childTitleRect direction pad tw th frame) := by
  intro hstrict
  by_cases hLR : direction = "LR"
  · rw [hLR] at hdx hstrict
    simp only [childInset, childTitleRect, shiftRect, insetRect, Rect.Contained,
      Rect.StrictInside] at hdx hbox hstrict
    omega
  by_cases hRL : direction = "RL"
  · rw [hRL] at hdx hfw hstrict
    change canvas.w - 2 * margin + tw + 2 * pad ≤ frame.w at hfw
    simp only [childInset, childTitleRect, shiftRect, insetRect,
      Rect.Contained, Rect.StrictInside] at hdx hbox hstrict
    omega
  by_cases hBT : direction = "BT"
  · rw [hBT] at hdy hfh hstrict
    change canvas.h - 2 * margin + th + 2 * pad ≤ frame.h at hfh
    simp only [childInset, childTitleRect, shiftRect, insetRect, Rect.Contained,
      Rect.StrictInside] at hdy hbox hstrict
    omega
  · simp only [childInset, childTitleRect, shiftRect, insetRect,
      Rect.Contained, Rect.StrictInside] at hdy hbox hstrict
    omega

private theorem obstruction_of_recursive (root : Input) (options : Options) (fuel : Nat) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox},
      FitReached root options inp o →
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursive fuel inp o = .ok res → (∃ size, (group.id, size) ∈ inp.fixedSizes) →
      ∀ {tracked : Box} {label : SceneLabel},
        res.scene.boxes.find? (fun box => box.id == group.id) = some tracked →
        tracked.role = "group" → label ∈ res.scene.labels → label.owner ≠ group.id →
        tracked.rect.StrictInside label.rect → ExecutedParentFrameObstruction root options := by
  induction fuel with
  | zero =>
    intro inp o res group hr hwf hfp hrun hfixed tracked label htracked hrole hlabel howner hstrict
    exact .flat hr hwf hfp hrun hfixed htracked hrole hlabel howner hstrict
  | succ fuel ih =>
    intro inp o res group hr hwf hfp hrun hfixed tracked label htracked hrole hlabel howner hstrict
    rcases layoutRecursive_succ_sources hrun with ⟨_, hflat⟩ |
      ⟨inner, P, metric, child, titleLines, parent, hselect, hP, hm, hchild, hwrap, hparent, hexpand⟩
    · exact .flat hr hwf hfp hflat hfixed htracked hrole hlabel howner hstrict
    let titleHeight : Int := (max 1 titleLines.length : Int) * P.lineH
    have hctx : ExpandChildCallContext fuel P inp o inner titleLines titleHeight parent child res :=
      ⟨hwf, hselect, rfl, hchild, hparent, hexpand⟩
    have hparams : ExpandChildCallParams P inp o inner titleLines titleHeight :=
      ⟨hP, rfl, metric, hm, hwrap⟩
    obtain ⟨hwfC, hfpC, hwfP, hfpP⟩ :=
      subInputsWellFormed fuel inp o inner P metric titleLines child parent hwf hfp hP hm hwrap hchild hparent
    have hrC : FitReached root options (childSubInput inp inner) (childSubOptions o inner) :=
      FitReached.child hr inner
    have hrP : FitReached root options (parentSubInput inp inner P titleLines child) o := by
      have hmargin := layoutRecursive_canvas_margins fuel hchild
      apply FitReached.parent hr hwf hP hm hwrap
      · rw [checkedParams_canvasMargin hP]
        exact hmargin.1
      · rw [checkedParams_canvasMargin hP]
        exact hmargin.2
    have hfixC : ∃ size, (group.id, size) ∈ (childSubInput inp inner).fixedSizes := hfixed
    have hfixP : ∃ size, (group.id, size) ∈ (parentSubInput inp inner P titleLines child).fixedSizes := by
      obtain ⟨size, hsize⟩ := hfixed
      exact ⟨size, List.mem_append_left _ hsize⟩
    have hfixInner : ∃ size, (inner.id, size) ∈ (parentSubInput inp inner P titleLines child).fixedSizes :=
      ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩
    have hnotInner : inner.id ≠ group.id := by
      intro heq
      obtain ⟨size, hsize⟩ := hfixed
      have hany : inp.fixedSizes.any (fun fixed => fixed.1 == inner.id) = true :=
        List.any_eq_true.mpr ⟨(group.id, size), hsize, by simp [heq]⟩
      have hsel := List.find?_some hselect
      simp [hany] at hsel
    have hfixedFind : ∃ entry, inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = some entry := by
      obtain ⟨size, hsize⟩ := hfixed
      cases hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) with
      | some entry => exact ⟨entry, rfl⟩
      | none =>
        have hmiss := (List.find?_eq_none.mp hfind) (group.id, size) hsize
        simp at hmiss
    obtain ⟨frame, actualMetric, actualLines, _, dx, dy, hframe, hmetric, hlines,
      _, hdx, hdy, _, hboxes⟩ := expandChild_sources hexpand
    have hmetricEq : actualMetric = metric := Except.ok.inj (hmetric.symm.trans hm)
    subst actualMetric
    have hlinesEq : actualLines = titleLines := Except.ok.inj (hlines.symm.trans hwrap)
    subst actualLines
    have hstructure := executedFrameC8aStep fuel P inp o inner titleLines titleHeight parent child res
      hexpand hfp hctx hparams frame titleLines dx dy hframe hdx hdy hparams.2.2
    have hframeRole := hstructure.2.2.2.2.1
    have hclasses := expandChild_c8b_structure fuel P inp o inner titleLines titleHeight parent child res
      hexpand hfp hctx (expandChild_label_owners fuel P inp o inner titleLines titleHeight
        parent child res hexpand hfp hctx hparams)
      frame titleLines dx dy hframe hdx hdy hparams.2.2
    have hlabelDump : label.toLabel ∈ res.scene.layoutDump.labels :=
      List.mem_map.mpr ⟨label, hlabel, rfl⟩
    have hclass := hclasses label.toLabel hlabelDump
    have htitleWidth := foldedTitleWidth_nonneg titleLines 0 (by omega)
    have htitleHeight : 0 ≤ titleHeight := Int.mul_nonneg
      (Int.le_trans (Int.natCast_nonneg _) (Int.le_max_right _ _))
      (Int.le_of_lt (callParams_lineH_pos hP))
    have htrackedId : tracked.id = group.id := by simpa using List.find?_some htracked
    have htrackedMem := List.mem_of_find?_eq_some htracked
    rw [hboxes] at htrackedMem
    obtain ⟨_, _, hfound⟩ := List.mem_filterMap.mp htrackedMem
    rcases List.mem_append.mp (List.mem_of_find?_eq_some hfound) with hfromChild | hfromParent
    · obtain ⟨cb, hcb, hembed⟩ := List.mem_map.mp hfromChild
      have hcbId : cb.id = group.id := by rw [← hembed] at htrackedId; exact htrackedId
      have hcbRole : cb.role = "group" := by rw [← hembed] at hrole; exact hrole
      have hcbLookup : child.scene.boxes.find? (fun box => box.id == group.id) = some cb := by
        rw [← hcbId]
        exact executedFrameLookup hwfC hchild cb hcb
      have hrect : tracked.rect = shiftRect dx dy cb.rect := by rw [← hembed]; rfl
      rcases hclass with ⟨_, htitle⟩ | ⟨cl, hcl, _, _, hclOwner, hclRect⟩ |
        ⟨pl, hpl, hnotCaption, _, hplOwner, hplRect⟩
      · change label.rect = groupTitleRectC8 inner P titleLines titleHeight frame at htitle
        rw [hrect, htitle] at hstrict
        have hbound := expandChild_frame_size_bounds fuel P inp o inner titleLines titleHeight
          parent child res hexpand hfp hctx hparams frame titleLines hframe hparams.2.2
        have hinset := expandChild_child_boxes_inset fuel P inp o inner titleLines titleHeight
          parent child res hexpand hfp hctx hP cb hcb
        exact False.elim (installedCaption_not_in_child htitleWidth htitleHeight hbound.1 hbound.2
          hdx hdy hinset hstrict)
      · change label.owner = cl.owner at hclOwner
        change label.rect = shiftRect dx dy cl.rect at hclRect
        have hs : cb.rect.StrictInside cl.rect := by
          rw [hrect, hclRect] at hstrict
          simp only [Rect.StrictInside, shiftRect] at hstrict ⊢
          omega
        exact ih (group := group) hrC hwfC hfpC hchild hfixC hcbLookup hcbRole hcl
          (hclOwner ▸ howner) hs
      · change label.rect = pl.rect at hplRect
        change label.owner = pl.owner at hplOwner
        change label.owner ≠ inner.id at hnotCaption
        have hinside := expandChild_content_fit_strict fuel P inp o inner titleLines titleHeight
          parent child res hexpand hfp hctx hparams frame titleLines dx dy hframe hdx hdy hparams.2.2
          cb.rect (expandChild_child_boxes_inset fuel P inp o inner titleLines titleHeight
            parent child res hexpand hfp hctx hP cb hcb)
        rw [hrect, hplRect] at hstrict
        exact ih (group := inner) hrP hwfP hfpP hparent hfixInner hframe hframeRole hpl
          (hplOwner ▸ hnotCaption)
          (strictInsideTrans hinside hstrict)
    · have htrackedLookup : parent.scene.boxes.find? (fun box => box.id == group.id) = some tracked := by
        rw [← htrackedId]
        exact executedFrameLookup hwfP hparent tracked hfromParent
      have hdisj : Disjoint tracked.rect frame.rect := by
        have hframeId : frame.id = inner.id := by simpa using List.find?_some hframe
        have hnoAnc := parentFixedForeign_narrow_holds fuel P inp o inner titleLines titleHeight
          parent child res group hexpand hfp hctx hparams hfixedFind
        have hnoDesc := expandChild_group_ancestor_absent hctx tracked.id
        have h8a := layoutRecursive_c8a_of_flat executedFrameFlatC8a subInputsWellFormed
          executedFrameC8aStep fuel _ _ parent hwfP hfpP hparent
        exact h8a tracked hfromParent hrole frame (List.mem_of_find?_eq_some hframe)
          (by simpa only [hframeId, htrackedId] using hnotInner)
          (by simpa only [hframeId, htrackedId] using hnoAnc)
          (by simpa only [hframeId] using hnoDesc)
      rcases hclass with ⟨_, htitle⟩ | ⟨cl, hcl, hnotCaption, _, hclOwner, hclRect⟩ |
        ⟨pl, hpl, _, _, hplOwner, hplRect⟩
      · change label.rect = groupTitleRectC8 inner P titleLines titleHeight frame at htitle
        rw [htitle] at hstrict
        have hcaption := frame_strictInside_caption fuel P inp o inner titleLines titleHeight
          parent child res hexpand hfp hctx hparams frame titleLines dx dy hframe hdx hdy hparams.2.2
        have hwidth : 0 ≤ (groupTitleRectC8 inner P titleLines titleHeight frame).w := by
          unfold groupTitleRectC8 childTitleRect
          split <;> exact htitleWidth
        have hheight : 0 ≤ (groupTitleRectC8 inner P titleLines titleHeight frame).h := by
          unfold groupTitleRectC8 childTitleRect
          split <;> exact htitleHeight
        exact False.elim (hdisj (sharedStrictInside hstrict hcaption hwidth hheight))
      · change label.rect = shiftRect dx dy cl.rect at hclRect
        change label.owner = cl.owner at hclOwner
        rw [hclRect] at hstrict
        by_cases hfit : (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect ∧
            0 ≤ cl.rect.w ∧ 0 ≤ cl.rect.h
        · have hs := expandChild_content_fit_strict fuel P inp o inner titleLines titleHeight
            parent child res hexpand hfp hctx hparams frame titleLines dx dy hframe hdx hdy hparams.2.2
            cl.rect hfit.1
          exact False.elim (hdisj (sharedStrictInside hstrict hs hfit.2.1 hfit.2.2))
        · change label.owner ≠ inner.id at hnotCaption
          exact .childLabel hr hctx hparams hfp hfixed hframe htrackedLookup hrole hdx hdy hcl
            (hclOwner ▸ howner) (hclOwner ▸ hnotCaption) hlabel hclOwner hclRect hstrict hfit
      · change label.rect = pl.rect at hplRect
        change label.owner = pl.owner at hplOwner
        rw [hplRect] at hstrict
        exact ih (group := group) hrP hwfP hfpP hparent hfixP htrackedLookup hrole hpl
          (hplOwner ▸ howner) hstrict

/-- A strictness violation in the actual parent result reduces to a flat fixed
frame or an unconfined child label shifted into a foreign fixed parent frame. -/
theorem executedParentFrameStrict_obstruction
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult}
    {frame : Box} {label : SceneLabel}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hlabel : label ∈ parent.scene.labels) (howner : label.owner ≠ group.id)
    (hstrict : frame.rect.StrictInside label.rect) :
    ExecutedParentFrameObstruction (parentSubInput inp group P titleLines child) o := by
  have invariant := executedFrameC8aStep fuel P inp o group titleLines titleHeight parent child res
    hctx.2.2.2.2.2 hframed hctx hparams frame titleLines
    (frame.rect.x + (childInset group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x - P.canvasMargin)
    (frame.rect.y + (childInset group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y - P.canvasMargin)
    hframe rfl rfl hparams.2.2
  have hfixed : ∃ size, (group.id, size) ∈ (parentSubInput inp group P titleLines child).fixedSizes :=
    ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩
  exact obstruction_of_recursive (parentSubInput inp group P titleLines child) o fuel
    (group := group) FitReached.refl
    ((subInputWellFormedC2 inp o group hctx.1).2 _ _ _)
    (framedParents_selectInput_outside_append inp o group hctx.1 hframed _ child.scene child.itemArea)
    hctx.2.2.2.2.1 hfixed hframe invariant.2.2.2.2.1 hlabel howner hstrict

end Elegant.Layered.PipelineImpl

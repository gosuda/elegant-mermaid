import Elegant.Layered.ExactStepGeometryProof
import Elegant.Layered.Assembly
import Elegant.Layered.ExactStepShortFacts
import Elegant.Layered.ExactFitClosure
import Elegant.Layered.ExactFlatC3Closure
import Elegant.Layered.ExpandChildC7GeometryProof
import Elegant.Layered.ExpandChildC8GeometryProof
import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.ExpandChildParentRouteClearProof
import Elegant.Layered.ExpandChildParentRouteRunProof
import Elegant.Layered.RecursiveC7
import Elegant.Layered.RecursiveC78
import Elegant.Layered.RecursiveBLiftsA

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Validator

/-! # Exact recursive-step leaf facts.

Closes or narrows the ten open step-geometry `ExactSeams` fields named in
`ExactSeamClosureGlue.lean` (`XG_StepC6DisjB`, `XG_StepC6MissB`,
`XG_StepC7ChildB`, `XG_StepC7ParentB`, `XG_StepC7CaptionB`, `XG_C8bCoreB`,
`XG_StepC8bChildLabelsB`, `XG_StepC8bCapStrictB`, `XG_StepC8bCapDisjB`,
`XG_StepC8bParentFrameB`), the step premises of `stepC6Geometry_layoutX`,
`stepC7Geometry_layoutX`, and `stepC8bGeometry_layoutX`
(`ExactStepGeometryProof.lean`).

Probe evidence (`proofs/wip/Probe/ExactStepGeometryLeavesTProbe.lean`,
`XSGLT_run`, all on `layoutX ["g"]` unless noted): every leaf conclusion
holds on all seven executed `expandChild` calls below. No FALSE witness was
found.

| input | childIn | disj | miss | plabel | cap* | lab | capStrict | capDisj | anc/pf | c1-c4 | core |
| nested g(a,b) | true | true | true | true | true | true | true | true | true | true | true |
| self-loop member a->a,a->b | true | true | true | true | true | true | true | true | true | true | true |
| caption label owned by g | true | true | true | true | true | true | true | true | true | true | true |
Disposition (all probe conclusions TRUE on every input above; no FALSE
witness found):

| leaf field | probe | result in this file |
|---|---|---|
| `stepC6Disj` (`XG_StepC6DisjB`) | disj=true | proved narrower `XSGL_stepC6Disj_of_c8a` (+ parent `C8a`) |
| `stepC6Miss` (`XG_StepC6MissB`) | miss=true | proved narrower `XSGL_stepC6Miss_of_routeClear` (+ route-clear) |
| `stepC7Child` (`XG_StepC7ChildB`) | childIn=true | proved narrower `XSGL_stepC7Child_of_labels` (+ child-label inset) |
| `stepC7Parent` (`XG_StepC7ParentB`) | disj,plabel=true | proved narrower `XSGL_stepC7Parent_of_scene` (+ scene fact) |
| `stepC7Caption` (`XG_StepC7CaptionB`) | capClass,capIn,capClear=true | proved narrower `XSGL_stepC7Caption_of_owners` (+ owner invariant) |
| `stepC8bCore` (`XG_C8bCoreB`) | core=true | proved outright `XSGL_c8bCore` |
| `stepC8bChildLabels` (`XG_StepC8bChildLabelsB`) | lab=true | residual def `XSGL_StepC8bChildLabelsFit` (+ `InputFixedFit`) |
| `stepC8bCapStrict` (`XG_StepC8bCapStrictB`) | capStrict=true | proved outright `XSGL_stepC8bCapStrict` |
| `stepC8bCapDisj` (`XG_StepC8bCapDisjB`) | capDisj=true | proved outright `XSGL_stepC8bCapDisj` |
| `stepC8bParentFrame` (`XG_StepC8bParentFrameB`) | disj,plabel,pfStrict,pfForeign=true | proved narrower `XSGL_stepC8bParentFrame_of` (+ C8a, C8b, two strictness) |
| empty group | true | true | true | true | true | true | true | true | true | true | true |
| zero-size fixed child | true | true | true | true | true | true | true | true | true | true | true |
| duplicate box id (ill-formed) | true | true | true | true | true | true | true | true | true | true | true |
| nested groups g1>g2>a (ids g,g1,g2) | true | true | true | true | true | true | true | true | true | true | true |
-/

/-- C6 miss from the parent route-clear residual: the out-of-scope case goes
through the public `parentRoute_outside_inner` monotonicity, the attached
case is the residual itself. -/
theorem XSGL_stepC6Miss_of_routeClear (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroute : ExpandChildParentRouteClear group parent) :
    ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
      ¬ Polyline.hitsRect pr.points r := by
  intro frame hframe pr hpr r hSI
  have hFrame : ExpandChildParentRouteFrameClear group parent :=
    fun frame' hfind' => (hroute frame' hfind').1
  have hAtt := (hroute frame hframe).2
  by_cases hfrom : pr.fromId = group.id
  · exact hAtt pr hpr (Or.inl hfrom) r hSI
  · by_cases hto : pr.toId = group.id
    · exact hAtt pr hpr (Or.inr hto) r hSI
    · exact parentRoute_outside_inner hFrame hframe hpr hfrom hto hSI

/-- C7 child-inside from the child-label inset: the child-box inset is the
closed `XG_child_boxes_insetB`, the strict fit is `XG_content_fit_strict`. -/
theorem XSGL_stepC7Child_of_labels (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hlabels : ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect) :
    ExpandChildC7ChildInside P inp o group titleHeight parent child := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hfit := XG_content_fit_strict exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams frame tl dx dy
    hframe hdx hdy hwrap
  have hboxes := XG_child_boxes_insetB exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams
  refine ⟨?_, ?_⟩
  · intro cb hcb
    have hr : (⟨P.canvasMargin, P.canvasMargin,
        child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained cb.rect := by
      simpa [insetRect] using hboxes cb hcb
    exact XG_strictInside_contained (hfit cb.rect hr)
  · intro cl hcl
    have hr : (⟨P.canvasMargin, P.canvasMargin,
        child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained cl.rect := by
      simpa [insetRect] using hlabels cl hcl
    exact XG_strictInside_contained (hfit cl.rect hr)

/-- C7 parent-clear from the parent-scene fact: the offsets are irrelevant to
frame disjointness. -/
theorem XSGL_stepC7Parent_of_scene (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)

    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hpar : ExpandChildC7ParentScene group parent) :
    ExpandChildC7ParentClear P inp o group titleHeight parent := by
  intro frame _ _ _ hframe _ _ _
  exact hpar frame hframe

/-- `xsgl_` copy of the private `titleWidth_nonneg`
(`ExpandChildTitleBandProof.lean`). -/
private theorem xsgl_titleWidth_nonneg (ls : List Measure.Line) :
    0 ≤ ls.foldl (fun width line => max width line.width) 0 := by
  suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
      0 ≤ ls.foldl (fun width line => max width line.width) acc by
    exact key ls 0 (by omega)
  intro ls acc hac
  induction ls generalizing acc with
  | nil => simpa using hac
  | cons line ls ih =>
    simp only [List.foldl_cons]
    exact ih _ (Int.le_trans hac (Int.le_max_left _ _))

/-- `xsgl_` copy of the private `titleRect_contained_aux`
(`ExpandChildTitleBandProof.lean`). -/
private theorem xsgl_titleRect_contained_aux {direction : String}
    {pad tw th conw conh fx fy fw fh : Int}
    (hpad : 0 ≤ pad)
    (hconw : 0 ≤ conw) (hconh : 0 ≤ conh)
    (hfw : (childFrameSize direction pad tw th ⟨conw, conh⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad tw th ⟨conw, conh⟩).h ≤ fh) :
    (⟨fx, fy, fw, fh⟩ : Rect).Contained
      (childTitleRect direction pad tw th ⟨fx, fy, fw, fh⟩) := by
  have htw : tw + 2 * pad ≤ fw := by
    unfold childFrameSize at hfw
    split at hfw <;> dsimp only at hfw <;> omega
  have hth : th + 2 * pad ≤ fh := by
    unfold childFrameSize at hfh
    split at hfh <;> dsimp only at hfh <;> omega
  unfold childTitleRect
  split <;> unfold Rect.Contained <;> dsimp only <;>
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] <;> omega

/-- `xsgl_` copy of the private `titleInset_disjoint_aux`
(`ExpandChildTitleBandProof.lean`). -/
private theorem xsgl_titleInset_disjoint_aux {direction : String}
    {pad tw th margin cw ch fx fy fw fh dx dy : Int}
    (htw : 0 ≤ tw) (hth : 0 ≤ th)
    (hfw : (childFrameSize direction pad tw th
      ⟨cw - 2 * margin, ch - 2 * margin⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad tw th
      ⟨cw - 2 * margin, ch - 2 * margin⟩).h ≤ fh)
    (hdx : dx = fx + (childInset direction pad tw th).x - margin)
    (hdy : dy = fy + (childInset direction pad tw th).y - margin) :
    Disjoint (childTitleRect direction pad tw th ⟨fx, fy, fw, fh⟩)
      (shiftRect dx dy (insetRect ⟨cw, ch⟩ margin)) := by
  have hdir : direction = "LR" ∨ direction = "RL" ∨ direction = "BT" ∨
      (direction ≠ "LR" ∧ direction ≠ "RL" ∧ direction ≠ "BT") := by
    by_cases h1 : direction = "LR"
    · exact Or.inl h1
    · by_cases h2 : direction = "RL"
      · exact Or.inr (Or.inl h2)
      · by_cases h3 : direction = "BT"
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
  rcases hdir with hLR | hRL | hBT | ⟨hnLR, hnRL, hnBT⟩
  · rw [hLR] at hfw hfh hdx hdy ⊢
    simp only [childTitleRect, childInset, childFrameSize, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega
  · rw [hRL] at hfw hfh hdx hdy ⊢
    simp only [childTitleRect, childInset, childFrameSize, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega
  · rw [hBT] at hfw hfh hdx hdy ⊢
    have eW : (childFrameSize "BT" pad tw th
        ⟨cw - 2 * margin, ch - 2 * margin⟩).w
        = max (cw - 2 * margin) tw + 2 * pad := rfl
    have eH : (childFrameSize "BT" pad tw th
        ⟨cw - 2 * margin, ch - 2 * margin⟩).h
        = ch - 2 * margin + th + 2 * pad := rfl
    rw [eW] at hfw
    rw [eH] at hfh
    simp only [childTitleRect, childInset, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega
  · simp only [childTitleRect, childInset, childFrameSize, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega


/-- Exact title band: the group caption rect lies in the located frame and
misses the shifted child margin inset. `xsgl_` copy of `expandChild_title_band`
with the exact frame reservation (`XG_frame_size_bounds`) and the exact canvas
margins (`exactCanvasMargins`). -/
private theorem xsgl_title_band (exactIds : List String)
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
    frame.rect.Contained (groupTitleRect group P titleLines' titleHeight frame) ∧
    Disjoint (groupTitleRect group P titleLines' titleHeight frame)
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
  intro frame titleLines' dx dy hfind hdx hdy hwrap
  have hP := hparams.1
  have hheightEq := hparams.2.1
  have hpad : 0 ≤ P.clusterPad := checkedParams_clusterPad_nonneg hP
  have hth : 0 ≤ titleHeight := by
    rw [hheightEq]
    exact Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP)
  have hchild : layoutRecursiveB (layoutX exactIds) fuel
      (childSubInput inp group) (childSubOptions o group) = .ok child :=
    hctxB.2.2.2.1
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  have hcon := (exactCanvasMargins exactIds) fuel _ _ _ hchild P hQchild
  have hconw : 0 ≤ child.scene.canvas.w - 2 * P.canvasMargin := by omega
  have hconh : 0 ≤ child.scene.canvas.h - 2 * P.canvasMargin := by omega
  obtain ⟨hfw, hfh⟩ := XG_frame_size_bounds exactIds fuel P inp o group
    titleLines titleHeight parent child res hexpand hframed hctxB hparams
    frame titleLines' hfind hwrap
  have htw := xsgl_titleWidth_nonneg titleLines'
  refine ⟨?_, ?_⟩
  · unfold groupTitleRect
    exact xsgl_titleRect_contained_aux hpad hconw hconh hfw hfh
  · unfold groupTitleRect
    exact xsgl_titleInset_disjoint_aux htw hth hfw hfh hdx hdy

/-- C7 caption fit from the label-owner invariant: the classification is the
base-independent `expandChild_label_classes_wrapped`, the band is the exact
`xsgl_title_band`, the child boxes are `XG_child_boxes_insetB`. -/
theorem XSGL_stepC7Caption_of_owners (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (howners : ExpandChildLabelOwners inp parent child) :
    ExpandChildC7CaptionFit P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hband := xsgl_title_band exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams frame tl dx dy hframe hdx hdy hwrap
  have hclass := (expandChild_label_classes_wrapped hexpand howners
    frame tl dx dy hframe hdx hdy hwrap).2
  have hchildBoxes := XG_child_boxes_insetB exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams
  have hcap : ∀ rl ∈ res.scene.layoutDump.labels, rl.owner = group.id →
      rl.rect = groupTitleRect group P tl titleHeight frame := by
    intro rl hrl hown
    have h := hclass rl hrl
    rcases h with ⟨_, hrect⟩ | ⟨_, _, hne, _, _, _⟩ | ⟨_, _, hne, _, _, _⟩
    · exact hrect
    · exact absurd hown hne
    · exact absurd hown hne
  refine ⟨hcap, hband.1, ?_⟩
  intro cb hcb hex
  have hshift : (shiftRect dx dy
      (insetRect child.scene.canvas P.canvasMargin)).Contained
      (shiftRect dx dy cb.rect) :=
    (contained_shiftRect dx dy).mpr (hchildBoxes cb hcb)
  have hrev : Disjoint
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin))
      (groupTitleRect group P tl titleHeight frame) :=
    (Disjoint.comm _ _).mp hband.2
  have hlow : Disjoint (shiftRect dx dy cb.rect)
      (groupTitleRect group P tl titleHeight frame) :=
    disjoint_contained_left hshift hrev
  exact (Disjoint.comm _ _).mp hlow

/-- C8b caption disjointness from the exact title band: `groupTitleRectC8` is
definitionally `groupTitleRect`, so the band's second conjunct applies. -/
theorem XSGL_stepC8bCapDisj (exactIds : List String)
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
    Disjoint (groupTitleRectC8 group P titleLines' titleHeight frame)
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
  intro frame titleLines' dx dy hframe hdx hdy hwrap
  exact (xsgl_title_band exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams frame titleLines' dx dy
    hframe hdx hdy hwrap).2

/-- `xsgl_` copy of the private `titleRect_strictInside_aux`
(`ExpandChildC8bGeometryExecuted.lean`). -/
private theorem xsgl_titleRect_strictInside_aux {direction : String}
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

/-- C8b caption strictness from the exact frame reservation, the positive
cluster pad, and the exact canvas margins. `xsgl_` copy of
`frame_strictInside_caption` at the exact base. -/
theorem XSGL_stepC8bCapStrict (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
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
    frame.rect.StrictInside
      (groupTitleRectC8 group P titleLines' titleHeight frame) := by
  intro frame titleLines' _dx _dy hframe _hdx _hdy hwrap'
  obtain ⟨hw, hh⟩ := XG_frame_size_bounds exactIds fuel P inp o group titleLines
    titleHeight parent child res _hexpand _hframed hctxB hparams frame titleLines'
    hframe hwrap'
  obtain ⟨hP, _hheightEq, _hwrapCtx⟩ := hparams
  have hpad : 0 < P.clusterPad := callParams_clusterPad_pos hP
  have hchild : layoutRecursiveB (layoutX exactIds) fuel
      (childSubInput inp group) (childSubOptions o group) = .ok child :=
    hctxB.2.2.2.1
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  have hcon := (exactCanvasMargins exactIds) fuel _ _ _ hchild P hQchild
  have hconw : 0 ≤ child.scene.canvas.w - 2 * P.canvasMargin := by omega
  have hconh : 0 ≤ child.scene.canvas.h - 2 * P.canvasMargin := by omega
  exact xsgl_titleRect_strictInside_aux hpad hconw hconh hw hh

/-- The C8b inset core holds at the exact base: the same case analysis as the
plain `expandChild_c8b_geometry_inset`, with the parent box-id uniqueness
from the closed `XG_parent_box_ids_nodupB`. This discharges the `stepC8bCore`
field outright. -/
theorem XSGL_c8bCore (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hChildBoxes : ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
    (hChildLabels : ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect)
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
    (hCapStrict : ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group titleLines' →
      frame.rect.StrictInside
        (groupTitleRectC8 group P titleLines' titleHeight frame))
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
    (hAnc : ExpandChildC8aAncestry group parent child res)
    (hParentFrame : ExpandChildParentFrame P inp o group titleHeight parent child) :
    ExpandChildC8bGeometry P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hfitS := hFitStrict frame tl dx dy hframe hdx hdy hwrap
  have hfit : frame.rect.Contained
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) :=
    XG_strictInside_contained hfitS
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
  have hnodup := XG_parent_box_ids_nodupB exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams
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
      exact Or.inr (XG_strictInside_of_contained hfitS (hSCcl cl hcl))
    · by_cases hgAnc : g.id ∈ parent.scene.layoutDump.ancestors group.id
      · have hgStrict := hancStrict g hg hgRole hgAnc
        exact Or.inr (XG_strictInside_of_contained hgStrict (hFcl cl hcl))
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
        exact Or.inr (XG_strictInside_of_contained hgStrict
          (XG_strictInside_contained hbandT))
      · have hgNotDesc : group.id ∉ parent.scene.layoutDump.ancestors g.id :=
          hAnc.2 g hg hgId
        have hdisj := hforeignDisj g hg hgRole hgId hgAnc hgNotDesc
        exact Or.inl ((Rect.disjoint_comm _ _).mp
          (disjoint_contained_left (XG_strictInside_contained hbandT)
            ((Rect.disjoint_comm _ _).mp hdisj)))

/-- Exact leaf role fact: every exact scene box carries the role of a source
input box. `xsgl_` copy of the private `XB_layout_role`
(`ExactStepFacts.lean`). -/
private theorem xsgl_layout_role {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.role = sb.role.id := by
  unfold layoutX at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf]
    intro cb hcb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcb
    exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl, rfl⟩

/-- Role transport through `selectInput`: kept boxes keep their role.
`xsgl_` copy of the private `XB_selectInput_box_role`
(`ExactStepFacts.lean`). -/
private theorem xsgl_selectInput_box_role (inp : Input) (keep : ModelBox → Bool)
    (root : String) {b : ModelBox}
    (hb : b ∈ (selectInput inp keep root).boxes) :
    ∃ m ∈ inp.boxes, keep m = true ∧ b.id = m.id ∧ b.role = m.role := by
  unfold selectInput at hb
  dsimp only at hb
  obtain ⟨q, hq, hbq⟩ := List.mem_map.mp hb
  obtain ⟨hqzip, hkq⟩ := List.mem_filter.mp hq
  exact ⟨q.1, List.fst_mem_of_mem_zipIdx hqzip, hkq, by rw [← hbq]; split <;> rfl,
    by rw [← hbq]; split <;> rfl⟩

/-- Successor split for `layoutRecursiveB` at the exact base. `xsgl_` copy of
the private `XB_succ` (`ExactStepFacts.lean`). -/
private theorem xsgl_succ (exactIds : List String) {fuel : Nat} {inp : Input}
    {o : Options} {res : FamilyResult}
    (h : layoutRecursiveB (layoutX exactIds) (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧
      layoutX exactIds inp o = .ok res) ∨
    ∃ group, inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      ∃ P titleHeight child parent a b c,
        layoutRecursiveB (layoutX exactIds) fuel
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
          { o with direction := directionOf group.direction } = .ok child ∧
        layoutRecursiveB (layoutX exactIds) fuel
          { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } o = .ok parent ∧
        expandChild P inp o group titleHeight parent child = .ok res := by
  rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with hflat |
    ⟨group, P, _metric, child, _titleLines, parent, hg, _, _, hc, _, hp, hexpand⟩
  · exact Or.inl hflat
  · exact Or.inr ⟨group, hg, P, _, child, parent, _, _, _, hc, hp, hexpand⟩

/-- Exact `B`-recursion role mirror: every scene box of a successful exact
recursive layout carries the role of a source input box. `xsgl_` copy of the
private `XB_role_mirror` (`ExactStepFacts.lean`). -/
private theorem xsgl_role_mirror (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ bb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = bb.id ∧ bb.role = sb.role.id := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact xsgl_layout_role h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases xsgl_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact xsgl_layout_role hlayout
    · have hselNodup : ∀ (keep : ModelBox → Bool) (root : String),
          ((selectInput inp keep root).boxes.map (·.id)).Nodup := by
        intro keep root
        rw [selectInput_box_ids]
        exact nodup_filter_map keep (·.id) inp.boxes hnodup
      have hchildNodup : ((selectInput inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
            (·.id)).Nodup := hselNodup _ _
      have hparentNodup : (({ selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := a, fixedChildren := b, fixedAreas := c } : Input).boxes.map
            (·.id)).Nodup := by
        show ((selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
            (·.id)).Nodup
        rw [selectInput_box_ids]
        exact nodup_filter_map _ _ _ hnodup
      have hchildRole := ih _ _ _ hchildNodup hchild
      have hparentRole := ih _ _ _ hparentNodup hparent
      obtain ⟨_frame, _metric', _titleLines', _lines, dx, dy, _hframe, _hmetric',
        _htitle', _hlines', _hdx, _hdy, _hcanvas, hboxes⟩ := expandChild_sources hexpand
      intro bb hbb
      rw [hboxes] at hbb
      obtain ⟨_model, _hmodelmem, hfind⟩ := List.mem_filterMap.mp hbb
      have hbbItems : bb ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hbbItems with hbc | hbp
      · obtain ⟨cbb, hcbbmem, hEmbed⟩ := List.mem_map.mp hbc
        obtain ⟨sb, hsbmem, hsbid, hsrole⟩ := hchildRole cbb hcbbmem
        obtain ⟨m, hmmem, _hkeep, hmsbid, hmsbrole⟩ := xsgl_selectInput_box_role inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id hsbmem
        refine ⟨m, hmmem, ?_, ?_⟩
        · have hcid : cbb.id = bb.id := by
            have h := congrArg (fun b : Box => b.id) hEmbed
            simpa [embedBox] using h
          exact hmsbid.symm.trans (hsbid.trans hcid)
        · have hcrole : cbb.role = bb.role := by
            have h := congrArg (fun b : Box => b.role) hEmbed
            simpa [embedBox] using h
          rw [← hcrole, hsrole, hmsbrole]
      · obtain ⟨sb, hsbmem, hsbid, hsrole⟩ := hparentRole bb hbp
        obtain ⟨m, hmmem, _hkeep, hmsbid, hmsbrole⟩ := xsgl_selectInput_box_role inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
        refine ⟨m, hmmem, ?_, ?_⟩
        · exact hmsbid.symm.trans hsbid
        · rw [hsrole, hmsbrole]

/-- One unfolded step of the ancestor walk. `xsgl_` copy of the private
`go_succ` (`ExpandChildParentFrameProof.lean`). -/
private theorem xsgl_go_succ {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

/-- The ancestor walk from a missing id is empty. `xsgl_` copy of the private
`go_none` (`ExpandChildParentFrameProof.lean`). -/
private theorem xsgl_go_none {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

/-- The ancestor walk from a root box is empty. `xsgl_` copy of the private
`go_root` (`ExpandChildParentFrameProof.lean`). -/
private theorem xsgl_go_root {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

/-- Every ancestor group strictly contains the descendant box. `xsgl_` copy
of the private `ancestor_strict_aux` (`ExpandChildParentFrameProof.lean`),
with strict transitivity from `XG_strictInside_of_contained`. -/
private theorem xsgl_ancestor_strict_aux
    (d : LayoutDump)
    (hC3 : Validator.C3 d)
    (hstep : ∀ (b : Box), b ∈ d.boxes → b.parent ≠ "" →
      ∀ (p : Box), d.box? b.parent = some p → p.role = "group" →
        p.rect.StrictInside b.rect)
    (g : Box) (hgRole : g.role = "group")
    (hfindg : d.box? g.id = some g) :
    ∀ (n : Nat) (s : String) (b : Box),
      d.box? s = some b → g.id ∈ LayoutDump.ancestors.go d n s →
      g.rect.StrictInside b.rect := by
  intro n
  induction n with
  | zero =>
      intro s b hb hm
      have e : LayoutDump.ancestors.go d 0 s = [] := rfl
      rw [e] at hm
      cases hm
  | succ n ih =>
      intro s b hb hm
      have hbmem : b ∈ d.boxes := List.mem_of_find?_eq_some hb
      by_cases hpar : b.parent = ""
      · rw [xsgl_go_root hb hpar] at hm
        cases hm
      · rw [xsgl_go_succ hb hpar] at hm
        rcases List.mem_cons.mp hm with heq | hmem
        · have hlook : d.box? b.parent = some g := heq ▸ hfindg
          exact hstep b hbmem hpar g hlook hgRole
        · cases hq : d.box? b.parent with
          | none =>
              cases hn : n with
              | zero =>
                  have e : LayoutDump.ancestors.go d 0 b.parent = [] := rfl
                  rw [hn] at hmem
                  rw [e] at hmem
                  cases hmem
              | succ m =>
                  rw [hn, xsgl_go_none hq] at hmem
                  cases hmem
          | some q1 =>
              have hIH := ih b.parent q1 hq hmem
              have hcont := hC3 b hbmem hpar q1 hq
              exact XG_strictInside_of_contained hIH hcont

/-- The located group frame of an executed exact call carries the group role.
`xsgl_` copy of the role part of `XB_core_wrapped` (`ExactStepFacts.lean`),
via the exact role mirror and the source chain. -/
private theorem xsgl_frame_role (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (frame : Box)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
    frame.role = "group" := by
  have hwf : WellFormed (inputModel inp o) := hctxB.1
  have hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group := hctxB.2.1
  have hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent := hctxB.2.2.2.2.1
  have hpboxes : (parentSubInput inp group P titleLines child).boxes =
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes :=
    hctxB.2.2.1
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hparentNodup : ((parentSubInput inp group P titleLines child).boxes.map
      (·.id)).Nodup := by
    rw [hpboxes, selectInput_box_ids]
    exact nodup_filter_map _ _ _ hids
  obtain ⟨source, hsource, hsbid, hsrole⟩ := xsgl_role_mirror exactIds fuel _ _ _
    hparentNodup hparent frame (List.mem_of_find?_eq_some hframe)
  have hsourceId : source.id = group.id := hsbid.trans hframeId
  have hsourceBase : source ∈ (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := by
    rw [← hpboxes]
    exact hsource
  obtain ⟨original, horiginal, _hkeep, hsourceEq⟩ :=
    selectInput_box_source inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "" source hsourceBase
  have horiginalId : original.id = group.id := by
    have h1 : original.id = source.id := by
      rw [hsourceEq]
      split <;> rfl
    exact h1.trans hsourceId
  have horiginalEq : original = group :=
    expandChild_nodup_map_inj (·.id) hids horiginal
      (List.mem_of_find?_eq_some hgroup) horiginalId
  have hsourceRole : source.role = group.role := by
    rw [hsourceEq]
    split <;> simp only [horiginalEq]
  have hgroupRole : group.role = .group := by
    have hs := List.find?_some hgroup
    simp only [Bool.and_eq_true] at hs
    have hi := hs.1
    unfold Compound.independent at hi
    simp only [Bool.and_eq_true] at hi
    exact beq_iff_eq.mp hi.1.1
  rw [hsrole, hsourceRole, hgroupRole]
  rfl

/-- C6 disjointness from the parent C8a clause: the frame role is the proved
`xsgl_frame_role`, one isolation direction is the closed
`stepC8aAncestry_layoutX`, the other is the scope premise. -/
theorem XSGL_stepC6Disj_of_c8a (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hC8a : Validator.C8a parent.scene.layoutDump) :
    ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
      pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
      Disjoint frame.rect pb.rect := by
  intro frame hframe pb hpb hex hscope
  have hrole := xsgl_frame_role exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams frame hframe
  have hanc := stepC8aAncestry_layoutX exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams
  have hfid : frame.id = group.id := by simpa using List.find?_some hframe
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
    exact hanc.2 pb hpb hne'
  have h2 : pb.id ∉ parent.scene.layoutDump.ancestors frame.id := by
    rw [hfid]
    exact fun hm => hscope (List.mem_cons.mpr (Or.inr hm))
  exact hC8a frame hframeMem hrole pb hpbMem hne h1 h2

/-- Ancestor group frames strictly contain the located frame at the exact
base: the parent C3 comes from the closed `layoutRecursiveB_c1_c3` lift, box
ids from `XG_parent_box_ids_nodupB`. `xsgl_` copy of
`expandChild_parentFrame_ancestor`. -/
private theorem xsgl_parentFrame_ancestor (exactIds : List String)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hstepStrict : ExpandChildParentStrictStep parent)
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
    ∀ g ∈ parent.scene.boxes, g.role = "group" →
      g.id ∈ parent.scene.layoutDump.ancestors group.id →
      g.rect.StrictInside frame.rect := by
  intro frame _titleLines' _dx _dy hframe _hdx _hdy _hwrap g hg hgRole hgAnc
  have hwf : WellFormed (inputModel inp o) := hctxB.1
  have hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent := hctxB.2.2.2.2.1
  obtain ⟨hwfChild, hparentWF⟩ := subInputWellFormedC2 inp o group hwf
  have hwfParent : WellFormed
      (inputModel (parentSubInput inp group P titleLines child) o) := hparentWF _ _ _
  have hframedParent : framedParents
      (parentSubInput inp group P titleLines child) = true :=
    framedParents_selectInput_outside_append inp o group hwf hframed
      _ child.scene child.itemArea
  have hC3 := (layoutRecursiveB_c1_c3 (layoutX exactIds) (XG_flatInset exactIds)
    (flatC3B_layoutX exactIds) subInputWellFormedC2 (exactFitClosed exactIds) fuel
    (parentSubInput inp group P titleLines child) o parent hwfParent hframedParent
    hparent).2
  have hnodup := XG_parent_box_ids_nodupB exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams
  have hfindg : parent.scene.layoutDump.box? g.id = some g :=
    Assembly.keyed_lookup_eq (fun b : Box => b.id) parent.scene.boxes hnodup g hg
  have hbox : parent.scene.layoutDump.box? group.id = some frame := hframe
  have hmem : g.id ∈ LayoutDump.ancestors.go parent.scene.layoutDump
      parent.scene.layoutDump.boxes.length group.id := hgAnc
  exact xsgl_ancestor_strict_aux parent.scene.layoutDump hC3 hstepStrict g hgRole
    hfindg _ group.id frame hbox hmem

/-- The parent frame fact holds at the exact base modulo four scene-local
residuals: the parent C8a/C8b clauses and the two strictness residuals. The
box half replays the C6 argument (role from `xsgl_frame_role`, isolation
from the closed ancestry); the label half excludes the strict C8b case;
the ancestor half is `xsgl_parentFrame_ancestor`; the foreign half is parent
C8a. -/
theorem XSGL_stepC8bParentFrame_of (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hC8a : Validator.C8a parent.scene.layoutDump)
    (hC8b : Validator.C8b parent.scene.layoutDump)
    (hframeStrict : ExpandChildParentFrameStrict group parent)
    (hstepStrict : ExpandChildParentStrictStep parent) :
    ExpandChildParentFrame P inp o group titleHeight parent child := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hrole := xsgl_frame_role exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams frame hframe
  have hanc := stepC8aAncestry_layoutX exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams
  have hfid : frame.id = group.id := by simpa using List.find?_some hframe
  have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
    List.mem_of_find?_eq_some hframe
  have hboxes : ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
      pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
      Disjoint frame.rect pb.rect := by
    intro pb hpb hex hscope
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
      exact hanc.2 pb hpb hne'
    have h2 : pb.id ∉ parent.scene.layoutDump.ancestors frame.id := by
      rw [hfid]
      exact fun hm => hscope (List.mem_cons.mpr (Or.inr hm))
    exact hC8a frame hframeMem hrole pb hpb hne h1 h2
  have hlabels : ∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
      Disjoint frame.rect pl.rect := by
    intro pl hpl hown
    have hplD : pl.toLabel ∈ parent.scene.layoutDump.labels :=
      List.mem_map.mpr ⟨pl, hpl, rfl⟩
    rcases hC8b frame hframeMem hrole pl.toLabel hplD with hdisj | hstrict
    · exact hdisj
    · have hstrict' : frame.rect.StrictInside pl.rect := hstrict
      exact absurd hstrict' (hframeStrict frame hframe pl hpl hown)
  have hancStrict := xsgl_parentFrame_ancestor exactIds hstepStrict hexpand hframed
    hctxB hparams frame tl dx dy hframe hdx hdy hwrap
  have hforeign : ∀ g ∈ parent.scene.boxes, g.role = "group" → g.id ≠ group.id →
      g.id ∉ parent.scene.layoutDump.ancestors group.id →
      group.id ∉ parent.scene.layoutDump.ancestors g.id →
      Disjoint g.rect frame.rect := by
    intro g hg hgRole hgNe hgNotAnc1 hgNotAnc2
    have hgMem : g ∈ parent.scene.layoutDump.boxes := hg
    have hne : frame.id ≠ g.id := by
      rw [hfid]
      exact fun h => hgNe h.symm
    have h1 : g.id ∉ parent.scene.layoutDump.ancestors frame.id := by
      rw [hfid]
      exact hgNotAnc1
    have h2 : frame.id ∉ parent.scene.layoutDump.ancestors g.id := by
      rw [hfid]
      exact hgNotAnc2
    exact hC8a g hgMem hgRole frame hframeMem hne h1 h2
  exact ⟨hboxes, hlabels, hancStrict, hforeign⟩

/-- Narrower residual for `stepC8bChildLabels`: the child-label inset under
the caller `InputFixedFit` premise the plain `expandChild_child_labels_inset`
needs. True on all seven `XSGLT_run` probes (`lab=true`); the exact
`layoutRecursiveB` label-inset induction is left open. -/
def XSGL_StepC8bChildLabelsFit (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    InputFixedFit inp o →
    ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect
end PipelineImpl
end Layered
end Elegant

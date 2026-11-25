import Elegant.Layered.ExpandChildC8GeometryProof
import Elegant.Layered.ExpandChildC8aGeometryExecuted
import Elegant.Layered.ExpandChildParentFrameDirect
import Elegant.Layered.ExpandChildTitleBandProof
import Elegant.Layered.ExpandChildAncestryProof
import Elegant.Layered.ExpandChildChildSceneProof
import Elegant.Layered.ExpandChildCanvasFitProof

set_option autoImplicit false

open Validator
open Elegant.Layered.Compound

namespace Elegant.Layered.PipelineImpl

/-!
# Executed-call C8b geometry: the four cross-scene clearance pairs.

`expandChild_c8b_geometry` (`ExpandChildC8GeometryProof.lean`) discharges the
geometric remainder `ExpandChildC8bGeometry` of `ExpandChildC8bStep`, but its
whole-canvas hypotheses are false as stated (`ExpandChildC7GeometryProof.lean`
shows the canvas starts one margin before the inset the shift was reserved
for). This module assembles the corrected inset form bottom-up:

* the caption rect lies strictly inside the located frame
  (`frame_strictInside_caption` from `ExpandChildTitleBandProof`);
* the inset glue (`expandChild_c8b_geometry_inset`, the same case analysis as
  `expandChild_c8b_geometry` over the shifted inset canvas, the strict
  caption, and the parent-frame facts);
* the fuel closure (`stepC8bGeometry_of_below`, assembling the proved inset
  facts `expandChild_content_fit_strict`, `expandChild_child_boxes_inset`,
  `expandChild_child_labels_inset`, `expandChild_title_band`,
  `stepC8aAncestry_holds`, and `expandChild_parentFrame_direct`);
* the closed seam fact (`stepC8bGeometry_holds`) by `recursiveStepFacts_of_below`.
  The C8a facts below each fuel are free (`stepC8aGeometry_holds` holds
  outright); the only extra hypotheses are the two parent-side residuals in
  per-call form and the caller's `InputFixedFit`, from which the parent
  sub-input fit follows by `InputFixedFit.parentSubInput`.
-/

/-- Strict containment weakens to containment. -/
private theorem strictInside_contained {outer inner : Rect}
    (h : outer.StrictInside inner) : outer.Contained inner := by
  simp only [Rect.StrictInside, Rect.Contained] at h ⊢
  omega

/-- `StrictInside` is transitive through a non-strict containment. -/
private theorem strictInside_of_strictInside_contained {a b c : Rect}
    (hab : a.StrictInside b) (hbc : b.Contained c) : a.StrictInside c := by
  simp only [Rect.StrictInside, Rect.Contained] at *
  omega

/-- Scene box ids of the parent stay nodup along `layoutRecursive`. -/
private theorem parent_scene_box_ids_nodup
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    (parent.scene.boxes.map (·.id)).Nodup := by
  obtain ⟨hwf, _hgroup, _hpb, _hchild, hparent, _he⟩ := hctx
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hcov : RoutesCovered (parentSubInput inp group P titleLines child) :=
    selectInput_routesCovered inp
      (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hids := layoutRecursive_ids (fun _ _ _ h => layout_ids h) fuel
    (parentSubInput inp group P titleLines child) o parent hcov hparent
  rw [hids.1]
  show ((selectInput inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
      (·.id)).Nodup
  rw [selectInput_box_ids]
  show (((inp.boxes.filter
    (fun box => !Compound.inside inp.boxes group.id box.id)).map
      (·.id))).Nodup
  exact hboxIds.sublist (List.Sublist.map _ List.filter_sublist)

/-- The corrected inset C8b geometry of one `expandChild` call.  Same case
analysis as `expandChild_c8b_geometry`, with the shifted child canvas
replaced by the shifted margin inset (which the child boxes and labels
inhabit), the caption strictness from `frame_strictInside_caption`, the
caption clearance from `expandChild_title_band`, and the parent scene facts
from `expandChild_parentFrame_direct`. -/
theorem expandChild_c8b_geometry_inset
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hAnc : ExpandChildC8aAncestry group parent child res)
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
    (hChildBoxes : ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
    (hChildLabels : ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect)
    (hCapStrict : ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group titleLines' →
      frame.rect.StrictInside (groupTitleRectC8 group P titleLines' titleHeight frame))
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
    (hParentFrame : ExpandChildParentFrame P inp o group titleHeight parent child) :
    ExpandChildC8bGeometry P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hfitS := hFitStrict frame tl dx dy hframe hdx hdy hwrap
  have hfit : frame.rect.Contained
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) :=
    strictInside_contained hfitS
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
  have hnodup := parent_scene_box_ids_nodup fuel P inp o group titleLines
    titleHeight parent child res hctx
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
      exact Or.inr (strictInside_of_strictInside_contained hfitS (hSCcl cl hcl))
    · by_cases hgAnc : g.id ∈ parent.scene.layoutDump.ancestors group.id
      · have hgStrict := hancStrict g hg hgRole hgAnc
        exact Or.inr (strictInside_of_strictInside_contained hgStrict (hFcl cl hcl))
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
        exact Or.inr (strictInside_of_strictInside_contained hgStrict
          (strictInside_contained hbandT))
      · have hgNotDesc : group.id ∉ parent.scene.layoutDump.ancestors g.id :=
          hAnc.2 g hg hgId
        have hdisj := hforeignDisj g hg hgRole hgId hgAnc hgNotDesc
        exact Or.inl ((Rect.disjoint_comm _ _).mp
          (disjoint_contained_left (strictInside_contained hbandT)
            ((Rect.disjoint_comm _ _).mp hdisj)))

/-- The C8b geometry at one fuel, from the step facts below it.  The C8a
facts below close outright; the child inset, strict fit, strict caption, and
caption clearance are the proved inset facts; the parent frame comes from
`expandChild_parentFrame_direct`, whose parent sub-input fit follows from the
caller's `InputFixedFit` by `InputFixedFit.parentSubInput`. -/
theorem stepC8bGeometry_of_below
    (fuel : Nat)
    (below8a : StepFactsBelow fuel ExpandChildC8aGeometry)
    (below8b : StepFactsBelow fuel ExpandChildC8bGeometry)
    (hflat8a : FlatC8a) (hflat8b : FlatC8b)
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hframeStrict : ExpandChildParentFrameStrict group parent)
    (hstepStrict : ExpandChildParentStrictStep parent)
    (hfix : InputFixedFit inp o) :
    ExpandChildC8bGeometry P inp o group titleHeight parent child res := by
  have hP := hparams.1
  have hwrapCtx := hparams.2.2
  obtain ⟨metric, hm, hwrap⟩ := hwrapCtx
  have hChildBoxes := expandChild_child_boxes_inset fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctx hP
  have hChildLabels := expandChild_child_labels_inset fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hfix hctx hP
  have hFitStrict : ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      frame.rect.StrictInside
        (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
    intro frame tl dx dy hframe hdx hdy hwrap
    exact expandChild_content_fit_strict fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hparams frame tl dx dy hframe hdx
      hdy hwrap _ (by simp only [insetRect, Rect.Contained]; omega)
  have hCapStrict : ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      frame.rect.StrictInside
        (groupTitleRectC8 group P tl titleHeight frame) := by
    intro frame tl dx dy hframe hdx hdy hwrap
    exact frame_strictInside_caption fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hparams frame tl dx dy hframe hdx
      hdy hwrap
  have hCapDisj : ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      Disjoint (groupTitleRectC8 group P tl titleHeight frame)
        (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
    intro frame tl dx dy hframe hdx hdy hwrap
    exact (expandChild_title_band fuel P inp o group titleLines titleHeight parent
      child res hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy
      hwrap).2
  have hAnc := stepC8aAncestry_holds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams
  have hfitParent : InputFixedFit (parentSubInput inp group P titleLines child) o := by
    obtain ⟨hwf, _hgroup, _hpb, hchild, _hparent, _hexpand'⟩ := hctx
    have hcm := layoutRecursive_canvas_margins fuel hchild
    have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
      rw [checkedParams_canvasMargin hP]
      exact hcm.1
    have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
      rw [checkedParams_canvasMargin hP]
      exact hcm.2
    exact InputFixedFit.parentSubInput hwf hfix hP hm hwrap hcw hch
  have hParentFrame := expandChild_parentFrame_direct hflat8a hflat8b below8a
    below8b hexpand hframed hctx hparams hframeStrict hstepStrict hfitParent
  exact expandChild_c8b_geometry_inset fuel P inp o group titleLines titleHeight
    parent child res hctx hAnc hFitStrict hChildBoxes hChildLabels hCapStrict
    hCapDisj hParentFrame

/-- Executed-call C8b geometry: the four cross-scene clearance pairs hold for
every `expandChild` call `layoutRecursive` performs, from the flat clauses,
the two parent-side residuals and the caller fit in per-call form.  The C8a
facts below each fuel are free (`stepC8aGeometry_holds` holds outright). -/
theorem stepC8bGeometry_holds
    (hflat8a : FlatC8a) (hflat8b : FlatC8b)
    (hframeStrict : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentFrameStrict group parent)
    (hstepStrict : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentStrictStep parent)
    (hfix : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      InputFixedFit inp o) :
    RecursiveStepFacts ExpandChildC8bGeometry := by
  apply recursiveStepFacts_of_below
  intro fuel below8b P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  exact stepC8bGeometry_of_below fuel
    (fun f _ P' inp' o' g' tls' th' par' chi' res' hx hf hc hp =>
      stepC8aGeometry_holds f P' inp' o' g' tls' th' par' chi' res' hx hf hc hp)
    below8b hflat8a hflat8b hexpand hframed hctx hparams
    (hframeStrict fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams)
    (hstepStrict fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams)
    (hfix fuel P inp o group titleLines titleHeight parent child res hexpand
      hframed hctx hparams)

end Elegant.Layered.PipelineImpl

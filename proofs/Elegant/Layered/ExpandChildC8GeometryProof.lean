import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.RecursiveC78
import Elegant.Layered.Assembly
import Elegant.Layered.SelectFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound

/-!
# Per-call C8a/C8b geometry of `expandChild`

Anchor: Tony Hoare, Edsger W. Dijkstra.

`expandChild_c8a_step_of_geometry` / `expandChild_c8b_step_of_geometry`
(`ExpandChildStepsFacts.lean`) consume the geometric remainders
`ExpandChildC8aGeometry` and `ExpandChildC8bGeometry` for every `expandChild`
call `layoutRecursive` performs.  This module discharges both under the call
context `ExpandChildCallContext`.

The executed facts of the call are hypotheses here, proved by sibling
workers and NOT reproved in this file:

* `ExpandChildCanvasFit` — the shifted child canvas lies STRICTLY inside
  the located group frame (the inset is at least `P.clusterPad`);
* `ExpandChildChildScene` — child boxes and child labels lie in the child
  canvas;
* `ExpandChildTitleBand` — the caption rect lies STRICTLY inside the frame
  and is disjoint from the shifted child canvas;
* `ExpandChildParentFrame` — the frame is disjoint from out-of-scope
  exclusive parent boxes and from parent labels it does not own, ancestor
  group frames strictly contain it, foreign group frames are disjoint from
  it (the parent scene's own C8a at the located frame), and the parent
  labels the group owns sit at the caption rect.

What remains is the C8-specific glue: strict containment transports through
the common shift, the located frame is the unique parent box with the
group id (scene box ids are nodup along `layoutRecursive_ids`), and each of
the four cross-scene pairs is dispatched on the group's position in the
parent ancestry.
-/

/-! ### The shared executed facts -/

/-- The shifted child canvas lies strictly inside the located group frame. -/
def ExpandChildCanvasFit (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleHeight : Int) (parent child : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines →
    frame.rect.StrictInside (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump))

/-- Every child-scene box and label lies in the child canvas. -/
def ExpandChildChildScene (child : FamilyResult) : Prop :=
  (∀ cb ∈ child.scene.boxes,
      (Validator.canvasRect child.scene.layoutDump).Contained cb.rect) ∧
    ∀ cl ∈ child.scene.labels,
      (Validator.canvasRect child.scene.layoutDump).Contained cl.rect

/-- The caption rect of the expanded group lies strictly inside the frame
and is disjoint from the shifted child canvas. -/
def ExpandChildTitleBand (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleHeight : Int) (parent child : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines →
    frame.rect.StrictInside (groupTitleRectC8 group P titleLines titleHeight frame) ∧
    Disjoint (groupTitleRectC8 group P titleLines titleHeight frame)
      (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump))

/-- Facts about the located frame inside the parent scene alone: it is
disjoint from out-of-scope exclusive parent boxes and from parent labels it
does not own; ancestor group frames strictly contain it; foreign group
frames are disjoint from it; and the parent labels it owns sit at the
caption rect. -/
def ExpandChildParentFrame (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleHeight : Int) (parent _child : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines →
    (∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
        Disjoint frame.rect pb.rect) ∧
    (∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
        Disjoint frame.rect pl.rect) ∧
    (∀ g ∈ parent.scene.boxes, g.role = "group" →
        g.id ∈ parent.scene.layoutDump.ancestors group.id →
        g.rect.StrictInside frame.rect) ∧
    (∀ g ∈ parent.scene.boxes, g.role = "group" → g.id ≠ group.id →
        g.id ∉ parent.scene.layoutDump.ancestors group.id →
        group.id ∉ parent.scene.layoutDump.ancestors g.id →
        Disjoint g.rect frame.rect) ∧
    (∀ pl ∈ parent.scene.labels, pl.owner = group.id →
        pl.rect = groupTitleRectC8 group P titleLines titleHeight frame)

/-! ### Transport helpers -/

/-- Strict containment weakens to containment. -/
private theorem strictInside_contained {outer inner : Rect}
    (h : outer.StrictInside inner) : outer.Contained inner := by
  simp only [Rect.StrictInside, Rect.Contained] at h ⊢
  omega

/-- `StrictInside` is transitive through a non-strict containment: if `b` is
strictly inside `a` and `c` is contained in `b`, then `c` is strictly inside
`a`. -/
private theorem strictInside_of_strictInside_contained {a b c : Rect}
    (hab : a.StrictInside b) (hbc : b.Contained c) : a.StrictInside c := by
  simp only [Rect.StrictInside, Rect.Contained] at *
  omega

/-- Scene box ids of the parent stay nodup along `layoutRecursive`: the
scene boxes map to the sub-input box ids, which are a sublist of the
well-formed input's nodup ids. -/
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
  exact hboxIds.sublist
    (List.Sublist.map (fun b : ModelBox => b.id) List.filter_sublist)

/-! ### C8a: shifted child boxes lie inside the group frame -/

/-- The C8a geometry of one `expandChild` call: every shifted child box lies
inside the located group frame.  The child box is contained in the child
canvas (`ExpandChildChildScene`), the shifted canvas is contained in the
frame (`ExpandChildCanvasFit`, weakened from strict), and containment
transports through the shift. -/
theorem expandChild_c8a_geometry
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hCanvasFit : ExpandChildCanvasFit P inp o group titleHeight parent child)
    (hChildScene : ExpandChildChildScene child) :
    ExpandChildC8aGeometry P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap cb hcb
  have hfitS := hCanvasFit frame tl dx dy hframe hdx hdy hwrap
  have hfit : frame.rect.Contained
      (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)) :=
    strictInside_contained hfitS
  have hcbC := hChildScene.1 cb hcb
  have hshift := (contained_shiftRect dx dy).mpr hcbC
  exact Rect.Contained.trans hfit hshift

/-! ### C8b: the four cross-scene clearance pairs -/

/-- The C8b geometry of one `expandChild` call.  Conjunct 3 (child groups vs
caption) is discharged outright from the title band; conjunct 2's
`owner ≠ group.id` case from the parent-frame fact; the remaining branches
use the strict canvas fit, the strict title band, the parent-frame
scene facts, and box-id uniqueness. -/
theorem expandChild_c8b_geometry
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hAnc : ExpandChildC8aAncestry group parent child res)
    (_howners : ExpandChildLabelOwners inp parent child)
    (hCanvasFit : ExpandChildCanvasFit P inp o group titleHeight parent child)
    (hChildScene : ExpandChildChildScene child)
    (hTitleBand : ExpandChildTitleBand P inp o group titleHeight parent child)
    (hParentFrame : ExpandChildParentFrame P inp o group titleHeight parent child) :
    ExpandChildC8bGeometry P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hfitS := hCanvasFit frame tl dx dy hframe hdx hdy hwrap
  have hfit : frame.rect.Contained
      (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)) :=
    strictInside_contained hfitS
  obtain ⟨hbandT, hbandD⟩ := hTitleBand frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨_hparentBox, hparentLabel, hancStrict, hforeignDisj, hgroupLabel⟩ :=
    hParentFrame frame tl dx dy hframe hdx hdy hwrap
  -- shifted child rects are contained in the shifted child canvas, which is
  -- contained in the frame
  have hSCcg : ∀ cg ∈ child.scene.boxes,
      (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)).Contained
        (shiftRect dx dy cg.rect) := by
    intro cg hcg
    exact (contained_shiftRect dx dy).mpr (hChildScene.1 cg hcg)
  have hSCcl : ∀ cl ∈ child.scene.labels,
      (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)).Contained
        (shiftRect dx dy cl.rect) := by
    intro cl hcl
    exact (contained_shiftRect dx dy).mpr (hChildScene.2 cl hcl)
  -- the frame contains every shifted child rect
  have hFcg : ∀ cg ∈ child.scene.boxes,
      frame.rect.Contained (shiftRect dx dy cg.rect) := by
    intro cg hcg
    exact Rect.Contained.trans hfit (hSCcg cg hcg)
  have hFcl : ∀ cl ∈ child.scene.labels,
      frame.rect.Contained (shiftRect dx dy cl.rect) := by
    intro cl hcl
    exact Rect.Contained.trans hfit (hSCcl cl hcl)
  -- the located frame is the unique parent box carrying the group id
  have hnodup := parent_scene_box_ids_nodup fuel P inp o group titleLines
    titleHeight parent child res hctx
  have frame_eq : ∀ g ∈ parent.scene.boxes, g.id = group.id → g = frame := by
    intro g hg hid
    have hgf : parent.scene.boxes.find? (fun a => a.id == g.id) = some g :=
      Assembly.keyed_lookup_eq (·.id) _ hnodup g hg
    simp only [hid] at hgf
    exact Option.some.inj (hgf.symm.trans hframe)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- conjunct 1: parent groups vs shifted child labels
    intro g hg hgRole cl hcl
    by_cases hgId : g.id = group.id
    · -- `g` is the located frame: strict canvas fit transports inside
      have hge : g = frame := frame_eq g hg hgId
      subst hge
      exact Or.inr (strictInside_of_strictInside_contained hfitS (hSCcl cl hcl))
    · by_cases hgAnc : g.id ∈ parent.scene.layoutDump.ancestors group.id
      · -- ancestor group strictly contains the frame, hence the label
        have hgStrict := hancStrict g hg hgRole hgAnc
        exact Or.inr (strictInside_of_strictInside_contained hgStrict (hFcl cl hcl))
      · -- foreign group is disjoint from the frame, hence from the label
        have hgNotDesc : group.id ∉ parent.scene.layoutDump.ancestors g.id :=
          hAnc.2 g hg hgId
        have hdisj := hforeignDisj g hg hgRole hgId hgAnc hgNotDesc
        exact Or.inl ((Rect.disjoint_comm _ _).mp
          (disjoint_contained_left (hFcl cl hcl) ((Rect.disjoint_comm _ _).mp hdisj)))
  · -- conjunct 2: shifted child groups vs parent labels
    intro cg hcg cgRole pl hpl
    by_cases howner : pl.owner = group.id
    · -- the group-owned parent label sits at the caption rect, which is
      -- disjoint from the shifted child canvas
      have hprect : pl.rect = groupTitleRectC8 group P tl titleHeight frame :=
        hgroupLabel pl hpl howner
      rw [hprect]
      exact Or.inl (disjoint_contained_left (hSCcg cg hcg)
        ((Rect.disjoint_comm _ _).mp hbandD))
    · have hdisjF := hparentLabel pl hpl howner
      exact Or.inl (disjoint_contained_left (hFcg cg hcg) hdisjF)
  · -- conjunct 3: shifted child groups vs the caption — disjoint via the
    -- title band
    intro cg hcg cgRole
    exact Or.inl (disjoint_contained_left (hSCcg cg hcg)
      ((Rect.disjoint_comm _ _).mp hbandD))
  · -- conjunct 4: parent groups vs the caption
    intro g hg hgRole
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

end Elegant.Layered.PipelineImpl

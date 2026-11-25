import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveC7
import Elegant.Layered.RecursiveC78
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildCanvasFitProof
import Elegant.Layered.ExpandChildTitleBandProof
import Elegant.Layered.InsetFit

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Per-call C7 geometry of the recursive `expandChild` step

`expandChild_c7_geometry` discharges the seam field `stepC7Geometry`:
for every executed `expandChild` call the recursion performs, the four
cross-scene `meetsInterior` clearance pairs of `ExpandChildC7Geometry`
hold. The proof applies pure rectangle glue to three named execution
residuals:

* `ExpandChildC7ChildInside`: shifted child boxes and labels lie in the
  group frame (strict content fit over child content in the shrunk canvas);
* `ExpandChildC7ParentClear`: the group frame is disjoint from foreign
  parent boxes and from parent labels owned elsewhere;
* `ExpandChildC7CaptionFit`: group-owned result labels are the title
  rect at the executed frame, the title rect lies in the frame, and the
  title rect is disjoint from shifted exclusive child boxes (caption
  classification plus the title band over the shifted inset).

Each residual quantifies over the same executed frame, title lines, and
shifts as `ExpandChildC7Geometry`, so every variable it constrains is
pinned by the `find?` equation, the `dx`/`dy` equations, and the wrapped
title equation; the parent, child, and result scenes are the recursive
call context scenes.
-/

/-- Shifted child boxes and labels lie inside the located group frame.
Strictly simpler than the C7 clearance pairs, which follow by combining
it with parent frame clearance. -/
def ExpandChildC7ChildInside (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleHeight : Int)
    (parent child : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines →
    (∀ cb ∈ child.scene.boxes, frame.rect.Contained (shiftRect dx dy cb.rect)) ∧
    (∀ cl ∈ child.scene.labels, frame.rect.Contained (shiftRect dx dy cl.rect))

/-- The located group frame is disjoint from foreign parent boxes and
from parent labels owned elsewhere. Strictly simpler than the goal,
which shifts one side into the frame. -/
def ExpandChildC7ParentClear (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleHeight : Int) (parent : FamilyResult) : Prop :=
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
        Disjoint frame.rect pl.rect)

/-- Group-owned result labels are the title rect at the executed frame,
the title rect lies in the frame, and the title rect misses shifted
exclusive child boxes. Strictly simpler than the caption clearance
pairs, which follow by rewriting the classification. -/
def ExpandChildC7CaptionFit (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleHeight : Int)
    (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines →
    (∀ rl ∈ result.scene.layoutDump.labels, rl.owner = group.id →
        rl.rect = groupTitleRect group P titleLines titleHeight frame) ∧
    frame.rect.Contained (groupTitleRect group P titleLines titleHeight frame) ∧
    (∀ cb ∈ child.scene.boxes, cb.exclusive = true →
        Disjoint (groupTitleRect group P titleLines titleHeight frame)
          (shiftRect dx dy cb.rect))

/-- Per-call C7 geometry of the recursive `expandChild` step: every
executed call satisfies the four cross-scene clearance pairs of
`ExpandChildC7Geometry`, modulo the child-inside, parent-clear, and
caption residuals above. -/
theorem expandChild_c7_geometry
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hchild : ExpandChildC7ChildInside P inp o group titleHeight parent child)
    (hparent : ExpandChildC7ParentClear P inp o group titleHeight parent)
    (hcaption : ExpandChildC7CaptionFit P inp o group titleHeight parent child res) :
    ExpandChildC7Geometry P inp o group titleHeight parent child res := by
  have _hexpandEq := hexpand
  have _hframedEq := hframed
  have _hctxEq := hctx
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

/-- The single parent-scene fact the clearance needs: the located group
frame is disjoint from foreign parent boxes and from parent labels owned
elsewhere. About the parent scene alone plus the group id; the expansion
offsets of `ExpandChildC7ParentClear` are irrelevant to its conclusions. -/
def ExpandChildC7ParentScene (group : ModelBox) (parent : FamilyResult) : Prop :=
  ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    (∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
        Disjoint frame.rect pb.rect) ∧
    (∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
        Disjoint frame.rect pl.rect)

/-- Parent clearance from the single parent-scene fact; the expansion
offsets are irrelevant to frame disjointness. -/
theorem expandChild_c7_parentClear_of_scene
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hpar : ExpandChildC7ParentScene group parent) :
    ExpandChildC7ParentClear P inp o group titleHeight parent := by
  have _hexpandEq := hexpand
  have _hframedEq := hframed
  have _hctxEq := hctx
  have _childEq := child
  have _resEq := res
  intro frame _ _ _ hframe _ _ _
  exact hpar frame hframe

/-- Strict containment downgrades to containment. -/
theorem strictInside_to_contained {a b : Rect} (h : a.StrictInside b) :
    a.Contained b := by
  simp only [Rect.StrictInside, Rect.Contained] at h ⊢
  omega

/-- Child containment from the strict content fit over child content in
the shrunk canvas. The whole-canvas fit is false (the canvas starts one
margin before the inset); only the shrunk content is strictly inside. -/
theorem expandChild_c7_childInside_of_content
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hchildBoxes : ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
    (hchildLabels : ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect) :
    ExpandChildC7ChildInside P inp o group titleHeight parent child := by
  have _hexpandEq := hexpand
  have _hframedEq := hframed
  have _hctxEq := hctx
  intro frame tl dx dy hframe hdx hdy hwrap
  have hfit := expandChild_content_fit_strict
    fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
  refine ⟨?_, ?_⟩
  · intro cb hcb
    have hr : (⟨P.canvasMargin, P.canvasMargin,
        child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained cb.rect := by
      simpa [insetRect] using hchildBoxes cb hcb
    exact strictInside_to_contained (hfit cb.rect hr)
  · intro cl hcl
    have hr : (⟨P.canvasMargin, P.canvasMargin,
        child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained cl.rect := by
      simpa [insetRect] using hchildLabels cl hcl
    exact strictInside_to_contained (hfit cl.rect hr)

/-- Caption fit from the label classification under the owner invariant
plus the title band over the shifted inset. The title rect misses the
whole shifted inset, hence every shifted exclusive child box inside it;
the band theorem is the corrected form of whole-canvas disjointness. -/
theorem expandChild_c7_captionFit_of_content
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (howners : ExpandChildLabelOwners inp parent child)
    (hchildBoxes : ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect) :
    ExpandChildC7CaptionFit P inp o group titleHeight parent child res := by
  have _hframedEq := hframed
  have _hctxEq := hctx
  have _hparamsEq := hparams
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨htitleIn, htitleDisj⟩ := expandChild_title_band
    fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
  have hclass := (expandChild_label_classes_wrapped hexpand howners
    frame tl dx dy hframe hdx hdy hwrap).2
  have hcap : ∀ rl ∈ res.scene.layoutDump.labels, rl.owner = group.id →
      rl.rect = groupTitleRect group P tl titleHeight frame := by
    intro rl hrl hown
    have h := hclass rl hrl
    rcases h with ⟨_, hrect⟩ | ⟨_, _, hne, _, _, _⟩ | ⟨_, _, hne, _, _, _⟩
    · exact hrect
    · exact absurd hown hne
    · exact absurd hown hne
  refine ⟨hcap, htitleIn, ?_⟩
  intro cb hcb hex
  have hshift : (shiftRect dx dy
      (insetRect child.scene.canvas P.canvasMargin)).Contained
      (shiftRect dx dy cb.rect) :=
    (contained_shiftRect dx dy).mpr (hchildBoxes cb hcb)
  have hrev : Disjoint
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin))
      (groupTitleRect group P tl titleHeight frame) :=
    (Disjoint.comm _ _).mp htitleDisj
  have hlow : Disjoint (shiftRect dx dy cb.rect)
      (groupTitleRect group P tl titleHeight frame) :=
    disjoint_contained_left hshift hrev
  exact (Disjoint.comm _ _).mp hlow

/-- Executed-call C7 geometry: child boxes and labels in the shrunk
canvas, the two parent frame facts, and the owner invariant. The call
parameters come from `ExpandChildCallParams`; the canvas fit and title
band are the proved strict theorems. -/
theorem expandChild_c7_geometry_executed
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hchildBoxes : ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
    (hchildLabels : ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect)
    (hparentBoxes : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
        Disjoint frame.rect pb.rect)
    (hparentLabels : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
        Disjoint frame.rect pl.rect)
    (howners : ExpandChildLabelOwners inp parent child) :
    ExpandChildC7Geometry P inp o group titleHeight parent child res := by
  have hchild := expandChild_c7_childInside_of_content
    fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams hchildBoxes hchildLabels
  have hpar : ExpandChildC7ParentScene group parent :=
    fun frame hframe => ⟨hparentBoxes frame hframe, hparentLabels frame hframe⟩
  have hparent := expandChild_c7_parentClear_of_scene
    fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hpar
  have hcaption := expandChild_c7_captionFit_of_content
    fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams howners hchildBoxes
  exact expandChild_c7_geometry
    fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hchild hparent hcaption

end Elegant.Layered.PipelineImpl

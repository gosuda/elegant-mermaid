import Elegant.Layered.ExpandChildC6GeometryExecuted
import Elegant.Layered.ExpandChildC8aGeometryExecuted
import Elegant.Layered.ExpandChildC7GeometryProof
import Elegant.Layered.ExpandChildParentRouteClearProof
import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.ExpandChildParentRouteRunProof
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildC6StepFacts
import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.RegionPipeline
import Elegant.Layered.RecursiveC78
import Elegant.Layered.RecursiveC7

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Region step geometry (base-independent merge glue).

The recursive step `layoutRecursiveB base` reuses the SAME `expandChild`
merge as the exact pipeline; only the base layout differs. The step
geometry conclusions (`ExpandChildC6Geometry`, `ExpandChildC7Geometry`,
`ExpandChildC8aGeometry`) are statements about the merge alone, so the
exact assembly glue replays verbatim at any base:

* `rsg_c7geometry_B`: the `B` twin of `expandChild_c7_geometry`
  (the plain proof discards its call context, so the `B` version is
  identical) — discharges the region `stepC7Geometry` shape.
* `rsg_stepC6Geometry_region`: the region `stepC6Geometry` shape from
  `stepC6Geometry_holdsB` at the reindexing base.
* `rsg_stepC8aGeometry_region`: the region `stepC8aGeometry` shape from
  `stepC8aGeometry_holdsB` at the reindexing base.
* `rsg_c6Miss_of_routeClear`, `rsg_c7Parent_of_scene`: the two parent-scene
  inner premises are base-independent (copies of `XSGL_stepC6Miss_of_routeClear`
  and `XSGL_stepC7Parent_of_scene` generalized over any base); they discharge
  the `hMissB` conjunct of the C6 reduction and the `hparentB` conjunct of the
  C7 reduction from merge-local facts (`ExpandChildParentRouteClear`,
  `ExpandChildC7ParentScene`) that never mention the base.

OPEN residual (exactly one public def): `RSG_ChildInsetB`, the child-box
margin inset over the region base. It is one of the six C6 ingredients and
the child ingredient of C8a (both reductions reuse it); it is strictly
narrower than either target. It awaits the region flat-inset lift
(`partSizing` in `RegionSeams`, still open). The remaining base facts
(strict content fit, child route inset, frame positivity, parent
disjointness/miss beyond route-clear, C7 child-inside/caption) stay as
explicit hypotheses of the proved conditional theorems, not as defs.

Obstructions (not attempted here, stated precisely):
* `stepC6Anchors` needs the child root chain (`ESS_childRootChain`) replayed
  over the region recursion: box-role mirroring and ancestor transport through
  region `selectInput` successes, which only region recursion validity supplies.
* `stepC7Scopes` needs the label-owner/route-agreement/separation walk
  machinery (`XB_label_owners`, `XB_scopes`) replayed over the region
  recursion; `RegionStepAssemblers` keeps it as `R_StepC7ScopesB`.

Probe evidence (`proofs/wip/Probe/RegionStepGeomTProbe.lean`, `lake env lean`):
* nested groups `G>{R1>{A,C},B}` at fuel 9: `(true, true)` — succeeds through
  a genuine `expandChild` (independent group present).
* two-region flat input at fuel 11: `(true, false)` — succeeds with no
  expansion (step premises vacuous).
* self-loop `a1->a1` inside `G` at fuel 7: `(false, true)` at the region base
  while the exact base `(layoutX [])` returns `true` — a region-specific
  rejection, recorded; premises hold vacuously over the failed run.
* empty group `E` plus zero-size fixed box `b1 := ⟨0,0⟩` at fuel 7:
  `(true, true)` — succeeds through genuine expansion.
* duplicate box id `a1` at fuel 7: `(false, false)` — ill-formed, rejected.
-/

/-- The reindexing base of the region tower (copy of `rsmBase` in
`RegionSeams.lean`, which is private there and cannot be imported). -/
private abbrev rsgBase (exactIds : List String) (idSets : List (String × List String)) :
    Input → Options → Except LayoutError FamilyResult :=
  fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'

/-- OPEN residual: child boxes of an executed region `expandChild` call lie
in the margin inset of the child canvas. Strictly narrower than the region
`stepC6Geometry` shape (one of its six per-call ingredients) and than
`stepC8aGeometry` (its child ingredient); both region reductions reuse it.
True on probes 1, 2, and 4 above (runs succeed, 1 and 4 through genuine
expansion); the exact-base twin `XG_child_boxes_insetB` closes outright. -/
def RSG_ChildInsetB (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ cb ∈ child.scene.boxes,
    (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect
/-- C6 miss from the parent route-clear residual, at any base: the
out-of-scope case goes through the public `parentRoute_outside_inner`
monotonicity, the attached case is the residual itself. Generic copy of
`XSGL_stepC6Miss_of_routeClear`; none of the inner premises mentions the
base. Discharges the `hMissB` conjunct of the C6 reduction below. -/
theorem rsg_c6Miss_of_routeClear
    (base : Input → Options → Except LayoutError FamilyResult)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctxB : ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
      parent child res)
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

/-- C7 parent-clear from the parent-scene fact, at any base: the offsets are
irrelevant to frame disjointness. Generic copy of
`XSGL_stepC7Parent_of_scene`. Discharges the `hparentB` conjunct of the C7
reduction below from the base-independent `ExpandChildC7ParentScene`. -/
theorem rsg_c7Parent_of_scene
    (base : Input → Options → Except LayoutError FamilyResult)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctxB : ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
      parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hpar : ExpandChildC7ParentScene group parent) :
    ExpandChildC7ParentClear P inp o group titleHeight parent := by
  intro frame _ _ _ hframe _ _ _
  exact hpar frame hframe

/-- Per-call C7 geometry of the recursive `expandChild` step at any base:
the `B` twin of `expandChild_c7_geometry`. That proof discards its call
context (only the three named residuals are used), so the same rectangle
glue replays verbatim over `ExpandChildCallContextB base`. Discharges the
region `stepC7Geometry` shape from its three per-call ingredients. -/
theorem rsg_c7geometry_B
    (base : Input → Options → Except LayoutError FamilyResult)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctxB : ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
      parent child res)
    (hchild : ExpandChildC7ChildInside P inp o group titleHeight parent child)
    (hparent : ExpandChildC7ParentClear P inp o group titleHeight parent)
    (hcaption : ExpandChildC7CaptionFit P inp o group titleHeight parent child res) :
    ExpandChildC7Geometry P inp o group titleHeight parent child res := by
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

/-- Region `stepC6Geometry` (the `rsmC6Geometry` shape of `RegionSeams`)
from `stepC6Geometry_holdsB` at the reindexing base: content fit, child
boxes (the open `RSG_ChildInsetB`), child routes, and frame positivity are
base facts about the merge; the two parent-scene conjuncts stay open, with
the miss conjunct discharged by `rsg_c6Miss_of_routeClear` from the
base-independent `ExpandChildParentRouteClear`. -/
theorem rsg_stepC6Geometry_region (exactIds : List String)
    (idSets : List (String × List String))
    (hFitB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
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
      ∀ (r : Rect),
      (insetRect child.scene.canvas P.canvasMargin).Contained r →
      frame.rect.StrictInside (shiftRect dx dy r))
    (hBoxB : RSG_ChildInsetB exactIds idSets)
    (hRtB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ cr ∈ child.scene.routes, ∀ p ∈ cr.points,
      PointIn (insetRect child.scene.canvas P.canvasMargin) p)
    (hDisjB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
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
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentRouteClear group parent)
    (hPosB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      0 < frame.rect.w ∧ 0 < frame.rect.h) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Geometry P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  exact stepC6Geometry_holdsB (rsgBase exactIds idSets) hFitB hBoxB hRtB hDisjB
    (fun fuel P inp o group titleLines titleHeight parent child res hexpand hframed
      hctxB hparams frame hframe pr hpr r hSI =>
      rsg_c6Miss_of_routeClear (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res hexpand hframed hctxB hparams
        (hMissB fuel P inp o group titleLines titleHeight parent child res
          hexpand hframed hctxB hparams) frame hframe pr hpr r hSI)
    hPosB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams

/-- Region `stepC7Geometry` (the `rsmC7Geometry` shape of `RegionSeams`)
from `rsg_c7geometry_B` at the reindexing base. The parent-clear conjunct
is discharged by `rsg_c7Parent_of_scene` from the base-independent
`ExpandChildC7ParentScene`; child-inside and caption fit stay as explicit
hypotheses (they need the child scene validity). -/
theorem rsg_stepC7Geometry_region (exactIds : List String)
    (idSets : List (String × List String))
    (hchildB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7ChildInside P inp o group titleHeight parent child)
    (hparentSceneB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7ParentScene group parent)
    (hcaptionB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7CaptionFit P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC7Geometry P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  exact rsg_c7geometry_B (rsgBase exactIds idSets) fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB
    (hchildB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (rsg_c7Parent_of_scene (rsgBase exactIds idSets) fuel P inp o group titleLines
      titleHeight parent child res hexpand hframed hctxB hparams
      (hparentSceneB fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctxB hparams))
    (hcaptionB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)

/-- Region `stepC8aGeometry` (the `rsmC8aGeometry` shape of `RegionSeams`)
from `stepC8aGeometry_holdsB` at the reindexing base: the child ingredient
is the open `RSG_ChildInsetB`, the frame-reservation ingredient stays as an
explicit hypothesis (it needs the child scene validity via the region
fixed-minimum lift). -/
theorem rsg_stepC8aGeometry_region (exactIds : List String)
    (idSets : List (String × List String))
    (hfitB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      ∀ (r : Rect),
      (⟨P.canvasMargin, P.canvasMargin, child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained r →
      frame.rect.StrictInside (shiftRect dx dy r))
    (hchildB : RSG_ChildInsetB exactIds idSets) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (rsgBase exactIds idSets) fuel P inp o group titleLines
        titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aGeometry P inp o group titleHeight parent child res :=
  stepC8aGeometry_holdsB (rsgBase exactIds idSets) hfitB hchildB


end PipelineImpl
end Layered
end Elegant

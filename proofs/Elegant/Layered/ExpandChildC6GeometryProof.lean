import Elegant.Layered.ExpandChildC6StepFacts
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.Pipeline
import Elegant.Layered.PolylineBoxMiss
import Elegant.Layered.RecursiveCallContext
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Per-call C6 geometry of the recursive `expandChild` step

The shared executed facts below are proved by other workers
(`ExpandChildCanvasFitProof.lean`, `ExpandChildChildSceneProof.lean`,
`ExpandChildParentFrameProof.lean`) and taken here as hypotheses, plus
frame positivity. Conjunct (a) (shifted child route vs parent box) goes
through the shelf-miss lemma. Conjunct (b) (parent route vs shifted child
box) needs no geometry transfer: the parent no-cross fact takes any rect
strictly inside the frame, and shifted child boxes are strictly inside it
(child box in canvas, transported through the strict canvas fit). Strictness
is coordinate-wise (`Rect.StrictInside`/`Rect.Contained`), so the transfer
holds even for zero-size boxes; `hitsRect` is separately false for those.
Frame positivity is kept as a hypothesis: the executed frame has the
reserved `childFrameSize` extent (child canvas plus title plus pads). The
group frame is non-exclusive (`modelWellFormed` admits no exclusive group),
so parent C6 is silent about it; the parent no-cross fact below is the exact
replacement (attached routes touch only the boundary, which `hitsRect`
does not count).
-/

/-- Strict containment weakens to containment. -/
private theorem strictInside_contained {outer inner : Rect}
    (h : outer.StrictInside inner) : outer.Contained inner := by
  simp only [Rect.StrictInside, Rect.Contained] at h ⊢
  omega

/-- A rect contained in a rect strictly inside the frame is strictly inside
the frame. Coordinate-wise, so degenerate rects are fine. -/
private theorem strictInside_trans_contained {outer mid inner : Rect}
    (hstrict : outer.StrictInside mid) (hsub : mid.Contained inner) :
    outer.StrictInside inner := by
  simp only [Rect.StrictInside, Rect.Contained] at hstrict hsub ⊢
  omega

/-- Per-call C6 geometry in the form `RecursiveStepFacts` consumes. -/
theorem expandChild_c6_geometry
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (_hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hFitStrict : ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group titleLines →
      frame.rect.StrictInside (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)))
    (hChild : (∀ b ∈ child.scene.boxes,
        (Validator.canvasRect child.scene.layoutDump).Contained b.rect) ∧
      (∀ l ∈ child.scene.labels,
        (Validator.canvasRect child.scene.layoutDump).Contained l.rect) ∧
      (∀ rt ∈ child.scene.routes, ∀ p ∈ rt.points,
        PointIn (Validator.canvasRect child.scene.layoutDump) p))
    (hParentDisj : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
        Disjoint frame.rect pb.rect)
    (hParentRoutes : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
        ¬ Polyline.hitsRect pr.points r)
    (hFramePos : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      0 < frame.rect.w ∧ 0 < frame.rect.h) :
    ExpandChildC6Geometry P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hfitS := hFitStrict frame tl dx dy hframe hdx hdy hwrap
  have hfitC : frame.rect.Contained
      (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)) :=
    strictInside_contained hfitS
  obtain ⟨hfw, hfh⟩ := hFramePos frame hframe
  have ha : ∀ cr ∈ child.scene.routes, ∀ pb ∈ parent.scene.boxes,
      pb.exclusive = true →
      pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
      ¬ Polyline.hitsRect (cr.points.map (shiftPoint dx dy)) pb.rect := by
    intro cr hcr pb hpb hex hscope
    have hconf : ∀ p ∈ cr.points.map (shiftPoint dx dy), PointIn frame.rect p := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hqb := hChild.2.2 cr hcr q hq
      have hqs : PointIn (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump))
          (shiftPoint dx dy q) :=
        pointIn_shift hqb
      simp only [PointIn, shiftRect, shiftPoint, Rect.Contained,
        Validator.canvasRect] at hqs hfitC ⊢
      omega
    have hdisj := hParentDisj frame hframe pb hpb hex hscope
    exact polyline_in_box_misses_disjoint hfw hfh hconf hdisj
  have hb : ∀ pr ∈ parent.scene.routes, ∀ cb ∈ child.scene.boxes,
      cb.exclusive = true →
      ¬ Polyline.hitsRect pr.points (shiftRect dx dy cb.rect) := by
    intro pr hpr cb hcb hex
    have hcbC : (Validator.canvasRect child.scene.layoutDump).Contained cb.rect :=
      hChild.1 cb hcb
    have hshift : (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)).Contained
        (shiftRect dx dy cb.rect) :=
      (contained_shiftRect dx dy).mpr hcbC
    have hinner : frame.rect.StrictInside (shiftRect dx dy cb.rect) :=
      strictInside_trans_contained hfitS hshift
    exact hParentRoutes frame hframe pr hpr (shiftRect dx dy cb.rect) hinner
  exact ⟨ha, hb⟩

end Elegant.Layered.PipelineImpl

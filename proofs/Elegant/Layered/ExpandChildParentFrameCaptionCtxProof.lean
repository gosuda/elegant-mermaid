import Elegant.Layered.Pipeline
import Elegant.Layered.ExpandChildParentFramePlacementCtxProof
import Elegant.Layered.ExpandChildC8bGeometryExecuted
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.RecursiveC78
import Elegant.Layered.BoxRouteIdsDisjoint
import Elegant.Layered.Compound

set_option autoImplicit false

open Elegant
open Elegant.Layered
open Elegant.Layered.PipelineImpl

namespace Elegant.Layered.PipelineImpl

/-!
# Caption and cross-side separation over executed `expandChild` calls

Probes (`proofs/wip/Probe/PfpGroupCaptionCtxTProbe.lean`, 7 inputs A-G,
13 executed `expandChild` calls: nested groups with captions, three-deep
nesting, zero-size fixed node, empty-group-adjacent self-loop on the split
group, ill-formed duplicate ids, top-level outside node, outside group with
its own caption):

* `capConcl` (every `PfpCaptionLabelCase` conclusion instance): true on all
  calls, non-vacuous (up to 4 caption pairs per call).
* `ownFit` (caption strictly inside its own frame in the merged scene):
  true on every call with a caption (correct direction
  `iframe.rect.StrictInside pl.rect`).
* `crossConcl` (every `PfpCrossSideClear` conclusion instance): true on all
  calls; non-vacuous on input G (1 and 2 opposite-side pairs). Only
  group-owned captions survive the merge on these probes, so the observed
  cross-side pairs are title-class.
* `sep` (axis separation with nonnegative sizes on both rects, the narrow
  premise below): true on every caption and cross pair (up to 6 per call).

Closed here: the pure separation helper `pgccT_sep_notStrictInside` and the
parent-level caption fit `pgccT_caption_parentFit` (installed caption rect
strictly inside the split group's own parent frame, from the proved
`frame_strictInside_caption` plus wrap identification). The res-level lift of
the fit and the establishment of separation from frame margins stay open;
each fact below keeps ONE strictly narrower remainder residual carrying the
non-separated case (`PfpCaptionSepRemainder`, `PfpCrossSideSepRemainder`),
with proved cover reductions splitting every call on the decidable
separation conjunction.

-/
/-- Closed caption fit at the parent level: the caption rect `expandChild`
installs for the split group's own labels lies strictly inside the group's
own parent frame. Wrap identification comes from the call params; the frame
reservation, pad positivity, and margin cover are the proved
`frame_strictInside_caption`. The res-level lift needs the merge identities
and stays with the remainder residuals below. -/
theorem pgccT_caption_parentFit
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (frame : Box)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
    frame.rect.StrictInside (groupTitleRectC8 group P titleLines titleHeight frame) := by
  have hwrapCtx := hparams.2.2
  exact frame_strictInside_caption fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams frame titleLines
    (frame.rect.x + (childInset group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin)
    (frame.rect.y + (childInset group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin)
    hframe rfl rfl hwrapCtx

/-- Pure separation helper: an axis-separated rect with nonnegative sizes
cannot strictly contain the other frame. Covers every probe pair; the
non-separated remainder stays in the residuals below. -/
private theorem pgccT_sep_notStrictInside (outer inner : Rect)
    (hsep : inner.x + inner.w ≤ outer.x ∨ outer.x + outer.w ≤ inner.x ∨
      inner.y + inner.h ≤ outer.y ∨ outer.y + outer.h ≤ inner.y)
    (hw : 0 ≤ inner.w) (hh : 0 ≤ inner.h) :
    ¬ outer.StrictInside inner := by
  simp only [Rect.StrictInside] at *
  omega

#eval decide (¬ ((⟨2048, 3328, 10779, 4608⟩ : Rect).StrictInside (⟨6324, 2048, 5810, 1280⟩ : Rect)))
#eval decide (¬ ((⟨1024, 1024, 12827, 7936⟩ : Rect).StrictInside (⟨17435, 2048, 0, 1280⟩ : Rect)))
#eval decide (¬ ((⟨0, 0, 10, 10⟩ : Rect).StrictInside (⟨20, 20, 3, 3⟩ : Rect)))

/-- Narrow caption remainder: `PfpCaptionLabelCase` restricted to the
non-separated case. The extra premise carries the negation of the decidable
separation conjunction (curried): the caption and the foreign frame overlap
on all four sides, or a caption size is negative. Strictly narrower than
`PfpCaptionLabelCase` by this premise; the separated case is closed by
`pgccT_sep_notStrictInside` in the cover below. Probe-seen pairs all fall
in the separated case, so this remainder is unobserved on probes. -/
def PfpCaptionSepRemainder : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (inner G : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o inner titleHeight parent child = .ok res →
    framedParents inp = true →
    BoxRouteIdsDisjoint inp →
    ExpandChildCallContext fuel P inp o inner titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o inner titleLines titleHeight →
    inner.id ≠ G.id →
    ∀ (frame : Box),
    res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id → pl.owner = inner.id →
      ((((∃ b ∈ res.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") ∨
          (∃ b ∈ res.scene.boxes, b.id = pl.owner ∧ b.role = "group")) ∧
          (G.id ∉ res.scene.layoutDump.ancestors pl.owner)) ∨
        ((∀ b ∈ res.scene.boxes, b.id ≠ pl.owner) ∧
          ∀ r ∈ res.scene.routes, r.id = pl.owner →
            (G.id ∉ res.scene.layoutDump.ancestors r.fromId ∨
              G.id ∉ res.scene.layoutDump.ancestors r.toId))) →
      ((pl.rect.x + pl.rect.w ≤ frame.rect.x ∨
          frame.rect.x + frame.rect.w ≤ pl.rect.x ∨
          pl.rect.y + pl.rect.h ≤ frame.rect.y ∨
          frame.rect.y + frame.rect.h ≤ pl.rect.y) →
        0 ≤ pl.rect.w → 0 ≤ pl.rect.h → False) →
      ¬ frame.rect.StrictInside pl.rect

/-- Proved cover: `PfpCaptionLabelCase` follows from its remainder. Every
call splits on the decidable separation conjunction: the separated case is
the closed helper, the non-separated case is the remainder. -/
theorem pfpCaptionLabelCase_of_sepRemainder
    (hnarrow : PfpCaptionSepRemainder) : PfpCaptionLabelCase := by
  intro fuel P inp o inner G titleLines titleHeight parent child res
    hexpand hframed hdisj hctx hparams hne
    frame hframe pl hpl hown hcap hdisjThm
  by_cases hQ : (pl.rect.x + pl.rect.w ≤ frame.rect.x ∨
      frame.rect.x + frame.rect.w ≤ pl.rect.x ∨
      pl.rect.y + pl.rect.h ≤ frame.rect.y ∨
      frame.rect.y + frame.rect.h ≤ pl.rect.y) ∧
      0 ≤ pl.rect.w ∧ 0 ≤ pl.rect.h
  · obtain ⟨hsep, hw, hh⟩ := hQ
    exact pgccT_sep_notStrictInside frame.rect pl.rect hsep hw hh
  · exact hnarrow fuel P inp o inner G titleLines titleHeight parent child res
      hexpand hframed hdisj hctx hparams hne
      frame hframe pl hpl hown hcap hdisjThm
      (fun hsep hw hh => hQ ⟨hsep, hw, hh⟩)

/-- Narrow cross-side remainder: `PfpCrossSideClear` restricted to the
non-separated case, with the same curried negation premise. Strictly
narrower than `PfpCrossSideClear`; the separated case is closed by
`pgccT_sep_notStrictInside` in the cover below. Probe-seen opposite-side
pairs (title-class on these probes) all fall in the separated case. -/
def PfpCrossSideSepRemainder : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (inner G : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o inner titleHeight parent child = .ok res →
    framedParents inp = true →
    BoxRouteIdsDisjoint inp →
    ExpandChildCallContext fuel P inp o inner titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o inner titleLines titleHeight →
    inner.id ≠ G.id →
    ∀ (frame : Box),
    res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id → pl.owner ≠ inner.id →
    (Compound.inside inp.boxes inner.id pl.owner ≠
      Compound.inside inp.boxes inner.id G.id) →
      ((∃ b ∈ res.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") ∨
        (∃ b ∈ res.scene.boxes, b.id = pl.owner ∧ b.role = "group")) →
      (G.id ∉ res.scene.layoutDump.ancestors pl.owner) →
      ((pl.rect.x + pl.rect.w ≤ frame.rect.x ∨
          frame.rect.x + frame.rect.w ≤ pl.rect.x ∨
          pl.rect.y + pl.rect.h ≤ frame.rect.y ∨
          frame.rect.y + frame.rect.h ≤ pl.rect.y) →
        0 ≤ pl.rect.w → 0 ≤ pl.rect.h → False) →
      ¬ frame.rect.StrictInside pl.rect

/-- Proved cover: `PfpCrossSideClear` follows from its remainder, by the same
decidable separation split. -/
theorem pfpCrossSideClear_of_sepRemainder
    (hnarrow : PfpCrossSideSepRemainder) : PfpCrossSideClear := by
  intro fuel P inp o inner G titleLines titleHeight parent child res
    hexpand hframed hdisj hctx hparams hne
    frame hframe pl hpl hown hcap hside hcls hnd
  by_cases hQ : (pl.rect.x + pl.rect.w ≤ frame.rect.x ∨
      frame.rect.x + frame.rect.w ≤ pl.rect.x ∨
      pl.rect.y + pl.rect.h ≤ frame.rect.y ∨
      frame.rect.y + frame.rect.h ≤ pl.rect.y) ∧
      0 ≤ pl.rect.w ∧ 0 ≤ pl.rect.h
  · obtain ⟨hsep, hw, hh⟩ := hQ
    exact pgccT_sep_notStrictInside frame.rect pl.rect hsep hw hh
  · exact hnarrow fuel P inp o inner G titleLines titleHeight parent child res
      hexpand hframed hdisj hctx hparams hne
      frame hframe pl hpl hown hcap hside hcls hnd
      (fun hsep hw hh => hQ ⟨hsep, hw, hh⟩)

end Elegant.Layered.PipelineImpl

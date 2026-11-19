import Elegant.Layered.Pipeline
import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.ExpandChildParentFramePlacementProof
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.InputFixedFit
import Elegant.Layered.SceneBounds
import Elegant.Layered.RecursiveBLiftsB

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Flat parent-frame facts for executed `layout` results

`parentFrameStrict_of_recursion` (in
`ExpandChildParentFramePlacementProof.lean`) takes three flat residuals:
`PfpFlatBoxClear` (narrow: non-descendant owners only), `PfpFlatRouteClear`,
`PfpFlatTitleClear`. Each is a single fact over executed flat runs
(`SceneExecution`), strictly narrower than the recursive target.

Probe evidence (`proofs/wip/Probe/PfpFlatFactsTProbe.lean`,
`PfpFlatFactsTProbe2.lean`, `PfpFlatFactsTProbe3.lean`,
`PfpFlatFactsTRelProbe.lean`, `PfpFlatFactsTGeomProbe.lean`): flat, nested,
self-loop, sibling, empty-group, attached-route, through-route, zero-size
fixed, very wide (20000) and very tall (20000) fixed, and nested fixed-middle
inputs, each under vector/cell profiles and TB/BT/LR/RL directions.

* Route and title fragments hold on every probed executed run
  (route/title-viol = 0 across all inputs and configs).
* The unrestricted box fragment is FALSE and was repaired in the placement
  module to the narrow form below. Witness: input `pfpNE` (vector/TB,
  `framedParents = true` by `#eval`, `fixedSizes = []` so `InputFixedFit`
  holds by `inputFixedFit_of_nil`):
  group `G` with non-exclusive member `x` owning caption `lx`; the executed
  scene has frame `G = (1024, 1024, 5120, 12800)` strictly containing
  `lx = (2560, 6912, 2048, 1280)`, owner `x` a non-group box with
  `x != G`. The same witness shape recurs with empty-text labels
  (`pfpEmpty2`) and in all 8 profile/direction configs; `isDesc` is true
  in every case (the owner is a strict descendant of `G`).

The narrow box form keeps the fragment but adds the title-style
non-descendant premise (`G.id` not among `ancestors pl.owner`), which the
witness violates and every other probed case satisfies. It serves the
consumer: `parentFrameStrict_of_recursion` derives exactly this premise
for the parent scene from `PfpReachedNoDescLabels` (`hndLabels`), so the
narrow box fact plus that premise discharges the consumer's box case
(`pfpFlatBoxCase_of_narrow` below).

Each residual below is therefore discharged from one per-run seam
hypothesis: a single fact quantified over executed runs only, true on all
probe cases. The seams name the run-level router/caption facts the family
seam must eventually supply, with no placeholders and no added assumptions.

Reduction to flat clauses (`_of_flat` below): box and title go through
`FlatC8aB` for unrelated owners, with three missing single facts over
executed runs, all probe-true: `PfpFlatCaptionFit` (label inside owner,
positive size), `PfpFlatAncestorLabelClear` (ancestor-owned labels stay
out), `PfpFlatNodeFrameClear` (non-group frames). Route goes through no
flat clause — none constrains route labels against group frames — with one
missing fact, `PfpFlatRoutePlaced` (endpoint-premise disjointness plus the
degenerate case), also probe-true.
-/

/-- Narrow box fragment: a label owned by a non-group scene box outside the
strict descendants of `G` never strictly contains the frame of `G`. Bridge
language matching the repaired `PfpFlatBoxClear` fragment, stated with
public vocabulary. -/
def pfpffBoxFragNarrow (S : FamilyResult) (G : ModelBox) : Prop :=
  ∀ (frame : Box),
    S.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ S.scene.labels, pl.owner ≠ G.id →
      (∃ b ∈ S.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") →
      (G.id ∉ S.scene.layoutDump.ancestors pl.owner) →
      ¬ frame.rect.StrictInside pl.rect

/-- Consumer adequacy: the narrow box fact plus the reached-scene
no-descendant premise (`PfpReachedNoDescLabels` gives `hnd` for the parent
scene in `parentFrameStrict_of_recursion`) discharges the consumer's box
case, which is `pfp_boxFrag` at the parent scene. -/
theorem pfpFlatBoxCase_of_narrow {S : FamilyResult} {G : ModelBox}
    (hfrag : pfpffBoxFragNarrow S G)
    (hnd : ∀ pl ∈ S.scene.labels, pl.owner ≠ G.id →
      G.id ∉ S.scene.layoutDump.ancestors pl.owner) :
    ∀ (frame : Box),
    S.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ S.scene.labels, pl.owner ≠ G.id →
      (∃ b ∈ S.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") →
      ¬ frame.rect.StrictInside pl.rect := by
  intro frame hframe pl hpl hown hbox
  exact hfrag frame hframe pl hpl hown hbox (hnd pl hpl hown)

/-- Per-run route seam: a label on a route with an endpoint outside the
strict descendants of `G` never strictly contains the frame of `G`, for one
executed run. Probe: true on every probed run (through-routes, attached
routes, self-loops, fixed wide/tall groups, all profiles/directions). -/
def PfpFlatRouteSeam : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → ∀ (G : ModelBox) (frame : Box),
    res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
      (∀ b ∈ res.scene.boxes, b.id ≠ pl.owner) →
      (∀ r ∈ res.scene.routes, r.id = pl.owner →
        (G.id ∉ res.scene.layoutDump.ancestors r.fromId ∨
          G.id ∉ res.scene.layoutDump.ancestors r.toId)) →
      ¬ frame.rect.StrictInside pl.rect

/-- The route-class flat fact holds from its seam. -/
theorem pfpFlatRouteClear_holds (hseam : PfpFlatRouteSeam) :
    PfpFlatRouteClear := by
  intro inp o res execution hwf hfp hfit G frame hframe pl hpl hown hnoBox hends
  exact hseam execution hwf hfp hfit G frame hframe pl hpl hown hnoBox hends

/-- Per-run title seam: a label owned by a group box that is not a strict
descendant of `G` never strictly contains the frame of `G`, for one executed
run. Probe: true on every probed run (nested and sibling group titles,
ancestor titles, fixed groups, all profiles/directions). -/
def PfpFlatTitleSeam : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → ∀ (G : ModelBox) (frame : Box),
    res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
      (∃ b ∈ res.scene.boxes, b.id = pl.owner ∧ b.role = "group") →
      (G.id ∉ res.scene.layoutDump.ancestors pl.owner) →
      ¬ frame.rect.StrictInside pl.rect

/-- The title-class flat fact holds from its seam. -/
theorem pfpFlatTitleClear_holds (hseam : PfpFlatTitleSeam) :
    PfpFlatTitleClear := by
  intro inp o res execution hwf hfp hfit G frame hframe pl hpl hown hgroup hnd
  exact hseam execution hwf hfp hfit G frame hframe pl hpl hown hgroup hnd

/-- Missing caption fact: every box-owned scene label lies inside its owner
box (closed) with positive size. Probe (`PfpFlatFactsTProbe6`, `checkCap`):
true on every probed run; the closed direction is `b.rect.Contained
pl.rect`. No flat validity clause provides it (`SceneCaptionBoxContainment`
covers exclusive boxes only). -/
def PfpFlatCaptionFit : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    ∀ pl ∈ res.scene.labels, ∀ b ∈ res.scene.boxes,
    b.id = pl.owner →
    b.rect.Contained pl.rect ∧ 0 < pl.rect.w ∧ 0 < pl.rect.h
/-- Missing ancestor fact: a label owned by a strict ancestor box of `G` is
never strictly inside `G`'s frame. Probe (`checkAnc`): true on every probed
run. Covers the ancestor-owner branch neither flat C8a (which needs both
non-ancestor directions) nor caption containment reaches. -/
def PfpFlatAncestorLabelClear : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    ∀ (G : ModelBox) (frame : Box),
    res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
    ∀ b ∈ res.scene.boxes, b.id = pl.owner →
    b.id ∈ res.scene.layoutDump.ancestors G.id →
    ¬ frame.rect.StrictInside pl.rect

/-- Missing node-frame fact: for a non-group frame, no foreign label of the
box classes strictly contains it. Probe (`checkNode`): true on every probed
run. Flat C8a/C2 do not apply to node-role frames. -/
def PfpFlatNodeFrameClear : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    ∀ (G : ModelBox) (frame : Box),
    res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    frame.role ≠ "group" →
    ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
    (∃ b ∈ res.scene.boxes, b.id = pl.owner) →
    (G.id ∉ res.scene.layoutDump.ancestors pl.owner) →
    ¬ frame.rect.StrictInside pl.rect

/-- Missing route-placement fact: a route-owned label with a qualifying
endpoint is disjoint from the frame and, when degenerate, lies outside it.
Probe (`PfpFlatFactsTProbe7`, `checkD2`/`checkP`): true on every probed run;
the endpoint premise is load-bearing (`checkD1` fails exactly on internal
routes whose labels sit strictly inside the frame). No flat clause provides
it: C2/C6/C7 need exclusive boxes, C8a needs owner boxes, C8b leaves the
strictly-inside disjunct open, and run-level clearance is exclusive-only. -/
def PfpFlatRoutePlaced : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    ∀ (G : ModelBox) (frame : Box),
    res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
    (∀ b ∈ res.scene.boxes, b.id ≠ pl.owner) →
    (∀ r ∈ res.scene.routes, r.id = pl.owner →
      (G.id ∉ res.scene.layoutDump.ancestors r.fromId ∨
        G.id ∉ res.scene.layoutDump.ancestors r.toId)) →
    Disjoint frame.rect pl.rect ∧
      ((0 < pl.rect.w ∧ 0 < pl.rect.h) ∨ ¬ frame.rect.StrictInside pl.rect)

/-- The narrow box fact from the flat C8a clause. Unrelated owners go
through `FlatC8aB` plus caption containment and positivity (interiors
meet); ancestor owners through `PfpFlatAncestorLabelClear`; non-group
frames through `PfpFlatNodeFrameClear`. The extra `hlay` premise is the one
`FlatC8aB` itself takes. -/
theorem pfpFlatBoxClearNarrow_of_flat
    (h8a : FlatC8aB layout) (hcap : PfpFlatCaptionFit)
    (hanc : PfpFlatAncestorLabelClear) (hnode : PfpFlatNodeFrameClear) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (_execution : SceneExecution inp o res),
      layout inp o = .ok res →
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o → ∀ (G : ModelBox), pfpffBoxFragNarrow res G := by
  intro inp o res execution hlay hwf hfp hfit G frame hframe pl hpl hown hbox hnd
  obtain ⟨b, hbmem, heq, hrole⟩ := hbox
  by_cases hgroup : frame.role = "group"
  · by_cases hrel : b.id ∈ res.scene.layoutDump.ancestors G.id
    · exact hanc execution G frame hframe pl hpl hown b hbmem heq hrel
    · have hC8a := h8a inp o res hwf hfp hlay
      have hmemF : frame ∈ res.scene.layoutDump.boxes :=
        List.mem_of_find?_eq_some hframe
      have hfid : frame.id = G.id := by simpa using List.find?_some hframe
      have hne : b.id ≠ frame.id := by rw [hfid, heq]; exact hown
      have hn1 : frame.id ∉ res.scene.layoutDump.ancestors b.id := by
        rw [hfid, heq]; exact hnd
      have hn2 : b.id ∉ res.scene.layoutDump.ancestors frame.id := by
        rw [hfid]; exact hrel
      have hdis := hC8a frame hmemF hgroup b hbmem hne hn1 hn2
      obtain ⟨hC, hpw, hph⟩ := hcap execution pl hpl b hbmem heq
      intro hS
      obtain ⟨fx1, fx2, fy1, fy2⟩ := hS
      obtain ⟨cx1, cx2, cy1, cy2⟩ := hC
      have hmeet : frame.rect.meetsInterior b.rect := by
        unfold Rect.meetsInterior
        constructor <;> omega
      exact hdis hmeet
  · exact hnode execution G frame hframe hgroup pl hpl hown ⟨b, hbmem, heq⟩ hnd

/-- The narrow title fact from the flat C8a clause: same three branches as
the box fact (unrelated owners through `FlatC8aB` plus caption containment
and positivity; ancestor owners through `PfpFlatAncestorLabelClear`;
non-group frames through `PfpFlatNodeFrameClear`). -/
theorem pfpFlatTitleClear_of_flat
    (h8a : FlatC8aB layout) (hcap : PfpFlatCaptionFit)
    (hanc : PfpFlatAncestorLabelClear) (hnode : PfpFlatNodeFrameClear) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (_execution : SceneExecution inp o res),
      layout inp o = .ok res →
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o → ∀ (G : ModelBox),
      ∀ (frame : Box),
      res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
      (∃ b ∈ res.scene.boxes, b.id = pl.owner ∧ b.role = "group") →
      (G.id ∉ res.scene.layoutDump.ancestors pl.owner) →
      ¬ frame.rect.StrictInside pl.rect := by
  intro inp o res execution hlay hwf hfp hfit G frame hframe pl hpl hown hgroup hnd
  obtain ⟨b, hbmem, heq, hrole⟩ := hgroup
  by_cases hgr : frame.role = "group"
  · by_cases hrel : b.id ∈ res.scene.layoutDump.ancestors G.id
    · exact hanc execution G frame hframe pl hpl hown b hbmem heq hrel
    · have hC8a := h8a inp o res hwf hfp hlay
      have hmemF : frame ∈ res.scene.layoutDump.boxes :=
        List.mem_of_find?_eq_some hframe
      have hfid : frame.id = G.id := by simpa using List.find?_some hframe
      have hne : b.id ≠ frame.id := by rw [hfid, heq]; exact hown
      have hn1 : frame.id ∉ res.scene.layoutDump.ancestors b.id := by
        rw [hfid, heq]; exact hnd
      have hn2 : b.id ∉ res.scene.layoutDump.ancestors frame.id := by
        rw [hfid]; exact hrel
      have hdis := hC8a frame hmemF hgr b hbmem hne hn1 hn2
      obtain ⟨hC, hpw, hph⟩ := hcap execution pl hpl b hbmem heq
      intro hS
      obtain ⟨fx1, fx2, fy1, fy2⟩ := hS
      obtain ⟨cx1, cx2, cy1, cy2⟩ := hC
      have hmeet : frame.rect.meetsInterior b.rect := by
        unfold Rect.meetsInterior
        constructor <;> omega
      exact hdis hmeet
  · exact hnode execution G frame hframe hgr pl hpl hown ⟨b, hbmem, heq⟩ hnd

/-- The route-class flat fact from the missing placement fact. No flat
validator clause constrains route labels against group frames (C2/C6/C7
need exclusive boxes, C8a needs owner boxes, C8b leaves the strictly-inside
disjunct open, C4 is orthogonality only, and run-level clearance is
exclusive-only), so no flat premise is taken: the content is entirely
`PfpFlatRoutePlaced`. A positive label strictly inside the frame meets its
interior (contradicting disjointness); a degenerate one is outside by the
second disjunct. -/
theorem pfpFlatRouteClear_of_flat (hmiss : PfpFlatRoutePlaced) :
    PfpFlatRouteClear := by
  intro inp o res execution hwf hfp hfit G frame hframe pl hpl hown hnoBox hends
  obtain ⟨hdis, hpos⟩ := hmiss execution G frame hframe pl hpl hown hnoBox hends
  intro hS
  cases hpos with
  | inl h =>
    obtain ⟨hpw, hph⟩ := h
    have hmeet : frame.rect.meetsInterior pl.rect := by
      unfold Rect.meetsInterior
      obtain ⟨fx1, fx2, fy1, fy2⟩ := hS
      constructor <;> omega
    exact hdis hmeet
  | inr h => exact h hS
end Elegant.Layered.PipelineImpl


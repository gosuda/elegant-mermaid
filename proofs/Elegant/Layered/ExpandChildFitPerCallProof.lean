import Elegant.Layered.InputFixedFit
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Per-call fixed fit from the top-level fit

The `LayeredSeams.fitPerCall` field (`FamilyAssembly.lean:135`) asks for
`InputFixedFit inp o` at *every* executed `expandChild` call, with no
hypothesis linking the call input to the top-level input that carries the
family theorem's `hfix : InputFixedFit inp o` premise
(`layoutFamily_valid_of_seams`). As stated over arbitrary call inputs that
field is false.

Executed witness (`proofs/wip/Probe/FitPerCallProbe.lean`, `badFirst`):
top input `inpBad` (group `G` with `x`,`y` inside, `a` outside, plus a
non-exclusive node `v` with label `lv` and `fixedSizes = [("v", (0, 0))]`,
vector profile) satisfies every `fitPerCall` premise at its single executed
call — `WellFormed`, `framedParents`, the `find?` group choice, the
parent-sub-input shape, `ExpandChildCallParams`, `expandChild = .ok`,
and the real `layoutRecursive` succeeds — yet `FixedSizeFit` fails at
`("v", (0, 0))` (`1 * lineH <= 0` is false for the executed `lineH`).
The same witness runs in the cell profile, with `LR` direction, and with
zero-width and negative fixed sizes. Hence no proof of the arbitrary form
exists; the seam owner must not supply the field as stated.

The true, reachable form below threads the top-level fit down the exact
sub-inputs the recursion builds, using the two proved transports
`InputFixedFit.childSubInput` (unconditional) and
`InputFixedFit.parentSubInput` (with the call-site wrap/margin premises).
`fitParent_of_top` mirrors `fitParent_of_seams` (`FamilyAssembly.lean:1603`)
with the field replaced by the reachable fit.

Seam-owner cutover (no new induction needed beyond what is proved here):
1. Delete the `fitPerCall` field. The two recursion lifts already thread the
   current input's fit: `RecursiveC7.lean:315,324` (`hfitChild`,
   `hfitParent`) and `RecursiveC78.lean:552,560` (same).
2. Strengthen the two lift step hypotheses to also take the current-call
   fit, exactly as they already take the threaded `BoxRouteIdsDisjoint`:
   - `layoutRecursive_c7_of_flat`'s `hgeo` gains
     `(hfit : InputFixedFit inp o)` and passes `hfit` at `hstep`
     (`RecursiveC7.lean:328-330`).
   - `layoutRecursive_c8b_of_flat`'s `hgeo` gains
     `(hfit : InputFixedFit inp o)` and passes `hfit` at `hstep`
     (`RecursiveC78.lean:563-565`).
3. In `FamilyAssembly.lean`, `c8bGeometry_of_seams` passes that `hfit`
   where it now passes `S.fitPerCall` (line 1586, via `stepC8bGeometry_holds`
   line 1491); `c7Geometry_of_seams` passes it where it now passes
   `S.fitPerCall` (line 1658) and `fitParent_of_top htop hr` (proved here)
   where it now passes `fitParent_of_seams S` (line 1659); `fitParent_of_seams`
   itself becomes `fitParent_of_top` with `htop`/`hr` from the strengthened
   `hgeo` scope.
Step bodies (`ExpandChildC7GeometryExecuted`, `ExpandChildC8bGeometryExecuted`)
are unchanged: they already take the per-call fit as a hypothesis.
-/

/-- How a call input reached from a top-level input descends: reflexivity at
the top, the unconditional child sub-input, and the parent sub-input whose
extra premises are exactly what `InputFixedFit.parentSubInput` needs and
what every executed call site has (`hwrap` from `ExpandChildCallParams`,
`hcw`/`hch` from `layoutRecursive_canvas_margins` at the call's child). -/
inductive FitReached (tin : Input) (to : Options) : Input → Options → Prop where
  | refl : FitReached tin to tin to
  | child {mid : Input} {mo : Options}
      (base : FitReached tin to mid mo) (group : ModelBox) :
      FitReached tin to (childSubInput mid group) (childSubOptions mo group)
  | parent {mid : Input} {mo : Options} {group : ModelBox} {P : Params}
      {metric : Measure.Metric} {titleLines : List Measure.Line}
      {child : FamilyResult}
      (base : FitReached tin to mid mo)
      (hwf : WellFormed (inputModel mid mo))
      (hP : checkedParams mo.profile mid.kind = .ok P)
      (hm : metricOf mo.profile = .ok metric)
      (hwrap : StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if mo.profile == .cell then mo.maxWidth else 0))
        (mid.texts.getD ((mid.boxes.findIdx? (fun box => box.id == group.id)).getD 0)
          group.id).toList = .ok titleLines)
      (hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w)
      (hch : 2 * P.canvasMargin ≤ child.scene.canvas.h) :
      FitReached tin to (parentSubInput mid group P titleLines child) mo

/-- The reachable per-call fit: every input reached from a top-level input
satisfying `InputFixedFit` satisfies it. Induction on the descent, one
proved transport per step. -/
theorem fitPerCall_of_top {tin : Input} {to : Options} {inp : Input}
    {o : Options} (htop : InputFixedFit tin to)
    (hr : FitReached tin to inp o) : InputFixedFit inp o := by
  induction hr with
  | refl => exact htop
  | child _ group ih => exact ih.childSubInput group
  | parent _ hwf hP hm hwrap hcw hch ih =>
      exact ih.parentSubInput hwf hP hm hwrap hcw hch

/-- The parent sub-input fit for a call reached from a fit top input:
`fitParent_of_seams` with the `S.fitPerCall` field replaced by the reachable
fit. The wrap/margin premises come from the call's own context and params. -/
theorem fitParent_of_top {tin : Input} {to : Options} {fuel : Nat}
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (htop : InputFixedFit tin to) (hr : FitReached tin to inp o)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    InputFixedFit (parentSubInput inp group P titleLines child) o := by
  obtain ⟨hwf, _hgroup, _hpb, hchild, _hparent, _hexpand⟩ := hctx
  have hP := hparams.1
  obtain ⟨metric, hm, hwrap⟩ := hparams.2.2
  have hcm := layoutRecursive_canvas_margins fuel hchild
  have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
    rw [checkedParams_canvasMargin hP]
    exact hcm.1
  have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
    rw [checkedParams_canvasMargin hP]
    exact hcm.2
  exact (fitPerCall_of_top htop hr).parentSubInput hwf hP hm hwrap hcw hch

end PipelineImpl
end Layered
end Elegant

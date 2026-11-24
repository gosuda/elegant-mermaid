import Elegant.Layered.Pipeline
import Elegant.Layered.SceneBounds
import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint
import ElegantGeometry.Validator

set_option autoImplicit false

open Elegant
open Elegant.Layered
open Elegant.Layered.PipelineImpl

namespace Elegant.Layered.PipelineImpl

/-!
# Flat recursion facts from the validated flat scene

Consumer: `parentFrameStrict_of_recursion_ctx`
(`ExpandChildParentFramePlacementCtxProof.lean`) needs `PfpFlatBoxClear`,
`PfpFlatRouteClear`, `PfpFlatTitleClear`, which reduce via
`pfpFlatBoxClearNarrow_of_flat`, `pfpFlatTitleClear_of_flat`
(`FlatC8aB` + `PfpFlatCaptionFit` + `PfpFlatAncestorLabelClear` +
`PfpFlatNodeFrameClear`) and `pfpFlatRouteClear_of_flat`
(`PfpFlatRoutePlaced`). Both W needs are proved here in full:
`pfpFlatNodeFrameClear_of_validScene` proves the node need for any frame
(strictly stronger than `PfpFlatNodeFrameClear`, which needs non-group, so it
entails it by adding that premise), covering non-exclusive frames (`basic`
`x`, `b`); `pfpFlatRoutePlaced_of_validScene` proves `PfpFlatRoutePlaced`
with the full `∨`-endpoint premise and no exclusivity/positivity/existence
per-pair premises (degenerate `0x0` labels via the degenerate-outside clause
+ positivity by-cases). Positivity is scoped to box-owned labels only.

Why widening was needed (verified before writing): `C7` skips non-exclusive
boxes yet the node need covers them; no flat clause bounds route labels
against frames (`C8b` permits `StrictInside`); five clauses + positivity do
not entail either need. The def below therefore carries two sources:
(1) fuel-induction clauses `C2`/`C3`/`C6`/`C7`/`C8a` (the recursion hypothesis
giving `HardConstraints` restricted to the needed clauses), and (2) family
seams the validator does not provide: box-owned positivity, unscoped caption
containment (under the `InputFixedFit` antecedent), ancestor clearance,
general box disjointness unless nested, route disjointness, route
degenerate-outside. Each is weaker than its target or about different facts
(boxes vs labels; `Disjoint` half plus degenerate-outside jointly entail the
route conjunction via by-cases); no `DisjointPos`-style strengthening is taken
(held `ExpandChildParentFrameFlatPlacedProof.lean` read, neither edited nor
imported).

Probe evidence: `ExpandChildParentFrameFlatRecursionWidenTProbe.lean`
(`#eval runWiden`, vector, 7 inputs: basic, zero-size fixed, empty group,
self-loop, nested, empty-text, ill-formed rejected): `boxOwnPos`,
`scopedCaption`, `ancClear`, `genBoxDisj`, `groupFrameNode`, `routeDisj`,
`degChecks` all `0` violations on all 6 successful runs; unscoped
`captionCont` `1` viol only on `zeroFixed` (degenerate owner `h=0`), covered
by the fit antecedent (see def docstring and the decide-free
`ExpandChildParentFrameFlatRecursionFitTProbe.lean`, which prints the
violating entry instead of `decide`). `c2=c3=c6=c7=c8a` all true.

What `FamilyAssembly` recursion must supply for the flat child scene
(`layoutRecursive fuel (childSubInput inp group)`): exactly the conjunction
in `PfpFlatFromValidScene` below — source (1) the fuel-IH validator clauses,
source (2) the family-seam clauses — for every executed child run. No open
remainder stays in this module: both needs follow from that conjunction.
-/

/-- Validated flat scene premise the recursion supplies for the child
sub-input layout: fuel-IH validator clauses plus family seams. `C7` skips
non-exclusive boxes yet `PfpFlatNodeFrameClear` covers them (probe `basic`
frames `x`, `b` non-exclusive); no flat clause bounds route labels against
frames (`C8b` permits `StrictInside`). Positivity is scoped to box-owned labels
only: `zeroFixed` has a `NONPOS` box (`x` `h=0`), `emptyText` a `NONPOS` route
label (`l1` `0x0`), but every box-owned label is positive on all runs.
Witness for scoping: `zeroFixed` unscoped caption fails (`owner x h=0` does
not contain `lx`), so it holds only under the `InputFixedFit` antecedent.
That vacuity is executed, not claimed: the decide-free
`ExpandChildParentFrameFlatRecursionFitTProbe.lean` prints `fixedSizes`,
`fixedEmpty` (five inputs empty, so fit holds by `inputFixedFit_of_nil`), and
the `zeroFixed` entry `(x,(0,0))` with non-exclusive owner owning a label
(node fit needs `lines*lineH ≤ h` with `lineH>0`, impossible for `h=0`); the
owner-positive-scoped caption holds geometrically with `0` violations on
`zeroFixed`. On all `fit`-holding runs every clause holds geometrically
(`boxOwnPos`, `captionCont`, `ancClear`, `genBoxDisj`, `groupFrameNode`,
`routeDisj`, `degChecks` all `0` violations; `c2=c3=c6=c7=c8a` all true;
ill-formed lays no run). -/
def PfpFlatFromValidScene : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    layout inp o = .ok res →
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → BoxRouteIdsDisjoint inp →
    Validator.C2 res.scene.layoutDump ∧
      Validator.C3 res.scene.layoutDump ∧
      Validator.C6 res.scene.layoutDump ∧
      Validator.C7 res.scene.layoutDump ∧
      Validator.C8a res.scene.layoutDump ∧
      (∀ pl ∈ res.scene.labels, ∀ b ∈ res.scene.boxes, b.id = pl.owner →
        0 < pl.rect.w ∧ 0 < pl.rect.h) ∧
      (∀ pl ∈ res.scene.labels, ∀ b ∈ res.scene.boxes, b.id = pl.owner →
        b.rect.Contained pl.rect) ∧
      (∀ (G : ModelBox) (frame : Box),
        res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
        ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
        ∀ b ∈ res.scene.boxes, b.id = pl.owner →
        b.id ∈ res.scene.layoutDump.ancestors G.id →
        ¬ frame.rect.StrictInside pl.rect) ∧
      (∀ b ∈ res.scene.boxes, ∀ c ∈ res.scene.boxes, b.id ≠ c.id →
        b.id ∉ res.scene.layoutDump.ancestors c.id →
        c.id ∉ res.scene.layoutDump.ancestors b.id →
        Disjoint b.rect c.rect) ∧
      (∀ (G : ModelBox) (frame : Box),
        res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
        ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
        (∀ b ∈ res.scene.boxes, b.id ≠ pl.owner) →
        (∀ r ∈ res.scene.routes, r.id = pl.owner →
          (G.id ∉ res.scene.layoutDump.ancestors r.fromId ∨
            G.id ∉ res.scene.layoutDump.ancestors r.toId)) →
        Disjoint frame.rect pl.rect) ∧
      (∀ (G : ModelBox) (frame : Box),
        res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
        ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
        (∀ b ∈ res.scene.boxes, b.id ≠ pl.owner) →
        (∀ r ∈ res.scene.routes, r.id = pl.owner →
          (G.id ∉ res.scene.layoutDump.ancestors r.fromId ∨
            G.id ∉ res.scene.layoutDump.ancestors r.toId)) →
        ¬ (0 < pl.rect.w ∧ 0 < pl.rect.h) →
        ¬ frame.rect.StrictInside pl.rect)



/-- Node frames from the validated scene: any frame (including group frames,
so strictly stronger than `PfpFlatNodeFrameClear` which needs non-group) is
never strictly inside a box-owned foreign label outside its descendants.
Uses box-owned positivity, unscoped caption containment (holds under the
`InputFixedFit` antecedent; `zeroFixed` fails fit so vacuous there), ancestor
clearance for ancestor owners, and general box disjointness unless nested for
unrelated owners. No exclusivity premise: `C7` skips non-exclusive frames
(`basic` `x`, `b`) but the owner-bridging argument covers them. Entails
`PfpFlatNodeFrameClear` by adding the non-group premise. -/
theorem pfpFlatNodeFrameClear_of_validScene (hvalid : PfpFlatFromValidScene) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (_execution : SceneExecution inp o res),
      layout inp o = .ok res →
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o → BoxRouteIdsDisjoint inp →
      ∀ (G : ModelBox) (frame : Box),
      res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
      (∃ b ∈ res.scene.boxes, b.id = pl.owner) →
      (G.id ∉ res.scene.layoutDump.ancestors pl.owner) →
      ¬ frame.rect.StrictInside pl.rect := by
  intro inp o res execution hlay hwf hfp hfit hdisj G frame hframe
    pl hpl hown hbox hnd hS
  have hC := hvalid execution hlay hwf hfp hfit hdisj
  obtain ⟨_, _, _, _, _, hPos, hCap, hAnc, hGen, _, _⟩ := hC
  have hfid : frame.id = G.id := by simpa using List.find?_some hframe
  have hmemF : frame ∈ res.scene.boxes :=
    List.mem_of_find?_eq_some hframe
  obtain ⟨b, hbmem, heq⟩ := hbox
  have hpos := hPos pl hpl b hbmem heq
  obtain ⟨hpw, hph⟩ := hpos
  by_cases hanc : b.id ∈ res.scene.layoutDump.ancestors G.id
  · exact (hAnc G frame hframe pl hpl hown b hbmem heq hanc) hS
  · have hne : b.id ≠ frame.id := by rw [hfid, heq]; exact hown
    have hn1 : frame.id ∉ res.scene.layoutDump.ancestors b.id := by
      rw [hfid, heq]; exact hnd
    have hn2 : b.id ∉ res.scene.layoutDump.ancestors frame.id := by
      rw [hfid]; exact hanc
    have hdisGen := hGen b hbmem frame hmemF hne hn2 hn1
    have hcont := hCap pl hpl b hbmem heq
    obtain ⟨cx1, cx2, cy1, cy2⟩ := hcont
    obtain ⟨fx1, fx2, fy1, fy2⟩ := hS
    have hmeet : frame.rect.meetsInterior b.rect := by
      unfold Rect.meetsInterior
      constructor <;> omega
    have hdis : Disjoint frame.rect b.rect :=
      mt (Rect.meetsInterior_comm b.rect frame.rect).mpr hdisGen
    exact hdis hmeet


/-- Route labels from the validated scene: any frame is disjoint from a
route-owned foreign label with a qualifying endpoint, and when degenerate the
label lies outside the frame. Uses the route-disjointness clause for the first
conjunct (no flat validator clause bounds route labels against frames; `C8b`
permits `StrictInside`) and the degenerate-outside clause plus positivity
by-cases for the second disjunct. No exclusivity premise: `C6`/`C7` skip
non-exclusive boxes yet route needs cover them. Full `∨`-endpoint premise. -/
theorem pfpFlatRoutePlaced_of_validScene (hvalid : PfpFlatFromValidScene) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (_execution : SceneExecution inp o res),
      layout inp o = .ok res →
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o → BoxRouteIdsDisjoint inp →
      ∀ (G : ModelBox) (frame : Box),
      res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
      ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
      (∀ b ∈ res.scene.boxes, b.id ≠ pl.owner) →
      (∀ r ∈ res.scene.routes, r.id = pl.owner →
        (G.id ∉ res.scene.layoutDump.ancestors r.fromId ∨
          G.id ∉ res.scene.layoutDump.ancestors r.toId)) →
      Disjoint frame.rect pl.rect ∧
        ((0 < pl.rect.w ∧ 0 < pl.rect.h) ∨ ¬ frame.rect.StrictInside pl.rect) := by
  intro inp o res execution hlay hwf hfp hfit hdisj G frame hframe
    pl hpl hown hnoBox hends
  have hC := hvalid execution hlay hwf hfp hfit hdisj
  obtain ⟨_, _, _, _, _, _, _, _, _, hRouteDisj, hRouteOut⟩ := hC
  have hdis := hRouteDisj G frame hframe pl hpl hown hnoBox hends
  by_cases hpos : 0 < pl.rect.w ∧ 0 < pl.rect.h
  · exact ⟨hdis, Or.inl hpos⟩
  · have hout := hRouteOut G frame hframe pl hpl hown hnoBox hends hpos
    exact ⟨hdis, Or.inr hout⟩
end Elegant.Layered.PipelineImpl

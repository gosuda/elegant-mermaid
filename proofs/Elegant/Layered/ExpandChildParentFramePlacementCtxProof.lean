import Elegant.Layered.Pipeline
import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildFitPerCallProof
import Elegant.Layered.InputFixedFit
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.FramedParentsSub
import Elegant.Layered.SelectFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.BoxRouteIdsDisjoint
import Elegant.Layered.ExpandChildParentFramePlacementProof
import Elegant.Layered.ExpandChildParentFrameTransportFactsProof

set_option autoImplicit false

open Elegant
open Elegant.Layered
open Elegant.Layered.PipelineImpl

namespace Elegant.Layered.PipelineImpl

/-!
# Parent-frame placement over executed `expandChild` calls

`pfp_frags_of_recursive` (in `ExpandChildParentFramePlacementProof.lean`) takes
the three bare transports `PfpBoxLabelTransport`, `PfpRouteLabelTransport`,
`PfpTitleLabelTransport`, which are all proved FALSE
(`pfpBoxLabelTransport_false`, `pfpRouteLabelTransport_false`,
`pfpTitleLabelTransport_false` in
`ExpandChildParentFrameTransportFactsProof.lean`). This module rewires the same
recursion to the true executed-call forms `PfpBoxLabelTransportCtx`,
`PfpRouteLabelTransportCtx`, `PfpTitleLabelTransportCtx`, threading per
recursive split the call bundle the Ctx forms demand: fuel, titleLines,
`ExpandChildCallContext`, `ExpandChildCallParams`, `framedParents`,
`BoxRouteIdsDisjoint`.

Two label classes cannot go through the Ctx forms and are split out as public
residuals over executed calls, taken as premises:

* `PfpCaptionLabelCase`: the group-caption label (`pl.owner = inner.id`),
  excluded by the non-caption premise of all three Ctx conclusions.
* `PfpCrossSideClear`: box/title-class labels on the opposite model side of
  the tracked group (`inside(inner, owner) != inside(inner, G)`). The Ctx
  forms only transport same-side pairs; cross-side pairs need the open
  geometric clearance (e.g. a fixed group disjoint from the splitting group,
  whose frame/label chains avoid each other), so they stay a residual.

Method: every non-caption result label is either same-side (Ctx transport) or
cross-side (residual) by decidable case split on the `Compound.inside`
equation, so no label-provenance lemmas are needed. The route Ctx conclusion
carries no label-side premise (endpoint parity is assumed inside its route
condition and discharged from the fragment hypothesis), hence needs no
side split at all.
-/

/-- Box-owned fragment copy: a label owned by a non-group scene box outside the
strict descendants of `G` never strictly contains the frame of `G`. Same
statement as `pfp_boxFrag`; copied because that def is private. -/
private def pfpCtx_boxFrag (S : FamilyResult) (G : ModelBox) : Prop :=
  ∀ (frame : Box),
    S.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ S.scene.labels, pl.owner ≠ G.id →
      (∃ b ∈ S.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") →
      (G.id ∉ S.scene.layoutDump.ancestors pl.owner) →
      ¬ frame.rect.StrictInside pl.rect

/-- Route-owned fragment copy: same statement as `pfp_routeFrag`. -/
private def pfpCtx_routeFrag (S : FamilyResult) (G : ModelBox) : Prop :=
  ∀ (frame : Box),
    S.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ S.scene.labels, pl.owner ≠ G.id →
      (∀ b ∈ S.scene.boxes, b.id ≠ pl.owner) →
      (∀ r ∈ S.scene.routes, r.id = pl.owner →
        (G.id ∉ S.scene.layoutDump.ancestors r.fromId ∨
          G.id ∉ S.scene.layoutDump.ancestors r.toId)) →
      ¬ frame.rect.StrictInside pl.rect

/-- Title fragment copy: same statement as `pfp_titleFrag`. -/
private def pfpCtx_titleFrag (S : FamilyResult) (G : ModelBox) : Prop :=
  ∀ (frame : Box),
    S.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ S.scene.labels, pl.owner ≠ G.id →
      (∃ b ∈ S.scene.boxes, b.id = pl.owner ∧ b.role = "group") →
      (G.id ∉ S.scene.layoutDump.ancestors pl.owner) →
      ¬ frame.rect.StrictInside pl.rect

/-- The parent sub-input is well-formed. Copy of the private lemma in
`ExpandChildParentFramePlacementProof.lean`. -/
private theorem pfpCtx_parentInput_wellFormed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    WellFormed (inputModel (parentSubInput inp group P titleLines child) o) := by
  exact (subInputWellFormedC2 inp o group hctx.1).2 _ _ _

/-- The parent sub-input is framed. Copy of the private lemma in
`ExpandChildParentFramePlacementProof.lean`. -/
private theorem pfpCtx_parentInput_framed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    framedParents (parentSubInput inp group P titleLines child) = true := by
  exact framedParents_selectInput_outside_append inp o group hctx.1 hframed
    _ child.scene child.itemArea

/-- Group-caption case: the caption label of the split group (`pl.owner =
inner.id`, whose rect `expandChild` replaces with the title band) never
strictly contains a tracked foreign frame. Over executed calls only; the three
Ctx conclusions all exclude `pl.owner = inner.id`, so the recursion cannot
supply this case. Probe-true on the `PfpTransportCtxTProbe` inputs (see the
`#eval`s below): the box/title disjuncts are instances of the box/title
fragment pairs, which all hold there; the route disjunct is vacuous there
since the split group's box is present in the result scene. -/
def PfpCaptionLabelCase : Prop :=
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
      ¬ frame.rect.StrictInside pl.rect

/-- Cross-side case: a box/title-class label on the opposite model side of the
tracked group needs the open geometric clearance, so it stays a residual over
executed calls. The Ctx conclusions only transport same-side pairs. Probe-true
on the `PfpTransportCtxTProbe` inputs (cross-side pairs are a subset of the
box/title fragment pairs, which all hold there). -/
def PfpCrossSideClear : Prop :=
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
      ¬ frame.rect.StrictInside pl.rect

/-- All three class fragments hold for every recursive result reached from the
call's parent input, via the executed-call transports. Same conclusions as
`pfp_frags_of_recursive` with the three bare transports replaced by the three
Ctx forms plus disjointness and the two executed-call residuals. -/
private theorem pfp_frags_of_recursive_ctx (P0 : Input) (o0 : Options)
    (hboxT : PfpBoxLabelTransportCtx) (hrouteT : PfpRouteLabelTransportCtx)
    (htitleT : PfpTitleLabelTransportCtx)
    (hflatB : PfpFlatBoxClear) (hflatR : PfpFlatRouteClear)
    (hflatT : PfpFlatTitleClear)
    (hcap : PfpCaptionLabelCase) (hcross : PfpCrossSideClear)
    (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult) (G : ModelBox),
      InputFixedFit P0 o0 → FitReached P0 o0 inp o →
      (∃ s, (G.id, s) ∈ inp.fixedSizes) →
      layoutRecursive fuel inp o = .ok res →
      WellFormed (inputModel inp o) → framedParents inp = true →
      BoxRouteIdsDisjoint inp →
      pfpCtx_boxFrag res G ∧ pfpCtx_routeFrag res G ∧
        pfpCtx_titleFrag res G := by
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro inp o res G hfitP0 hr hfixG hrec hwf hfp hdisj
    cases fuel with
    | zero =>
      have hfit : InputFixedFit inp o := fitPerCall_of_top hfitP0 hr
      have hlay : layout inp o = .ok res := hrec
      obtain ⟨exec⟩ := layout_sceneExecution hlay
      exact ⟨hflatB exec hwf hfp hfit G, hflatR exec hwf hfp hfit G,
        hflatT exec hwf hfp hfit G⟩
    | succ f =>
      rcases layoutRecursive_succ_sources hrec with ⟨_, hlay⟩ |
        ⟨g', P'', met'', chi'', tls'', par'', hg', hP'', hm'',
          hchild'', hwrap'', hparent'', hexpand''⟩
      · have hfit : InputFixedFit inp o := fitPerCall_of_top hfitP0 hr
        obtain ⟨exec⟩ := layout_sceneExecution hlay
        exact ⟨hflatB exec hwf hfp hfit G, hflatR exec hwf hfp hfit G,
          hflatT exec hwf hfp hfit G⟩
      · have hwfChi : WellFormed
            (inputModel (childSubInput inp g') (childSubOptions o g')) :=
          (subInputWellFormedC2 inp o g' hwf).1
        have hfpChi : framedParents (childSubInput inp g') = true :=
          (framedParentsSub inp o g' hwf hfp).1
        have hwfPar : WellFormed
            (inputModel (parentSubInput inp g' P'' tls'' chi'') o) :=
          (subInputWellFormedC2 inp o g' hwf).2 _ _ _
        have hfpPar : framedParents
            (parentSubInput inp g' P'' tls'' chi'') = true :=
          framedParents_selectInput_outside_append inp o g' hwf hfp
            _ chi''.scene chi''.itemArea
        have hdisjChi : BoxRouteIdsDisjoint (childSubInput inp g') :=
          hdisj.childSubInput g'
        have hdisjPar : BoxRouteIdsDisjoint
            (parentSubInput inp g' P'' tls'' chi'') :=
          hdisj.parentSubInput g' P'' tls'' chi''
        have hcm := layoutRecursive_canvas_margins f hchild''
        have hcw : 2 * P''.canvasMargin ≤ chi''.scene.canvas.w := by
          rw [checkedParams_canvasMargin hP'']
          exact hcm.1
        have hch : 2 * P''.canvasMargin ≤ chi''.scene.canvas.h := by
          rw [checkedParams_canvasMargin hP'']
          exact hcm.2
        have hrChi : FitReached P0 o0 (childSubInput inp g')
            (childSubOptions o g') := FitReached.child hr g'
        have hrPar : FitReached P0 o0
            (parentSubInput inp g' P'' tls'' chi'') o :=
          FitReached.parent hr hwf hP'' hm'' hwrap'' hcw hch
        have hfixChi : ∃ s, (G.id, s) ∈ (childSubInput inp g').fixedSizes :=
          hfixG
        have hfixPar : ∃ s,
            (G.id, s) ∈
              (parentSubInput inp g' P'' tls'' chi'').fixedSizes := by
          obtain ⟨s, hs⟩ := hfixG
          exact ⟨s, List.mem_append_left _ hs⟩
        have hne : g'.id ≠ G.id := by
          intro heq
          obtain ⟨s, hs⟩ := hfixG
          have hbeq : ((G.id, s).1 == g'.id) = true := by
            rw [heq]
            exact beq_self_eq_true _
          have hleft : inp.fixedSizes.any (fun fixed => fixed.1 == g'.id) = true := by
            rw [List.any_eq_true]
            exact ⟨(G.id, s), hs, hbeq⟩
          have hpred := List.find?_some hg'
          simp [hleft] at hpred
        have hctx'' : ExpandChildCallContext f P'' inp o g' tls'' _
            par'' chi'' res :=
          ⟨hwf, hg', rfl, hchild'', hparent'', hexpand''⟩
        have hparams'' : ExpandChildCallParams P'' inp o g' tls'' _ :=
          ⟨hP'', rfl, ⟨met'', hm'', hwrap''⟩⟩
        have ihPar := ih f (Nat.lt_succ_self f)
          (parentSubInput inp g' P'' tls'' chi'') o par'' G
          hfitP0 hrPar hfixPar hparent'' hwfPar hfpPar hdisjPar
        have ihChi := ih f (Nat.lt_succ_self f) (childSubInput inp g')
          (childSubOptions o g') chi'' G hfitP0 hrChi hfixChi hchild''
          hwfChi hfpChi hdisjChi
        refine ⟨?_, ?_, ?_⟩
        · intro frame hframe pl hpl hown hex hnd
          by_cases hcap' : pl.owner = g'.id
          · exact hcap f P'' inp o g' G tls'' _ par'' chi'' res
              hexpand'' hfp hdisj hctx'' hparams'' hne
              frame hframe pl hpl hown hcap' (Or.inl ⟨Or.inl hex, hnd⟩)
          · by_cases hside : Compound.inside inp.boxes g'.id pl.owner =
              Compound.inside inp.boxes g'.id G.id
            · exact hboxT f P'' inp o g' G tls'' _ par'' chi'' res
                hexpand'' hfp hdisj hctx'' hparams'' hne
                ihPar.1 ihChi.1
                frame hframe pl hpl hown hcap' hside hex hnd
            · exact hcross f P'' inp o g' G tls'' _ par'' chi'' res
                hexpand'' hfp hdisj hctx'' hparams'' hne
                frame hframe pl hpl hown hcap' hside (Or.inl hex) hnd
        · intro frame hframe pl hpl hown hnoBox hroute
          by_cases hcap' : pl.owner = g'.id
          · exact hcap f P'' inp o g' G tls'' _ par'' chi'' res
              hexpand'' hfp hdisj hctx'' hparams'' hne
              frame hframe pl hpl hown hcap'
              (Or.inr ⟨hnoBox, hroute⟩)
          · exact hrouteT f P'' inp o g' G tls'' _ par'' chi'' res
              hexpand'' hfp hdisj hctx'' hparams'' hne
              ihPar.2.1 ihChi.2.1
              frame hframe pl hpl hown hcap' hnoBox
              (fun r hr hid _ _ => hroute r hr hid)
        · intro frame hframe pl hpl hown hgroup hnd
          by_cases hcap' : pl.owner = g'.id
          · exact hcap f P'' inp o g' G tls'' _ par'' chi'' res
              hexpand'' hfp hdisj hctx'' hparams'' hne
              frame hframe pl hpl hown hcap' (Or.inl ⟨Or.inr hgroup, hnd⟩)
          · by_cases hside : Compound.inside inp.boxes g'.id pl.owner =
              Compound.inside inp.boxes g'.id G.id
            · exact htitleT f P'' inp o g' G tls'' _ par'' chi'' res
                hexpand'' hfp hdisj hctx'' hparams''
                ihPar.2.2 ihChi.2.2
                frame hframe pl hpl hown hcap' hside hgroup hnd
            · exact hcross f P'' inp o g' G tls'' _ par'' chi'' res
                hexpand'' hfp hdisj hctx'' hparams'' hne
                frame hframe pl hpl hown hcap' hside (Or.inr hgroup) hnd

/-- `parentFrameStrict`: the parent scene of every executed `expandChild` call
satisfies `ExpandChildParentFrameStrict`, via the executed-call transports.
Same conclusion as `parentFrameStrict_of_recursion` with the three bare
transports (proved false) replaced by the three Ctx forms plus disjointness
and the two executed-call residuals. -/
theorem parentFrameStrict_of_recursion_ctx
    (tin : Input) (to : Options)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (htop : InputFixedFit tin to)
    (hr : FitReached tin to inp o)
    (hdisjTop : BoxRouteIdsDisjoint
      (parentSubInput inp group P titleLines child))
    (hboxT : PfpBoxLabelTransportCtx) (hrouteT : PfpRouteLabelTransportCtx)
    (htitleT : PfpTitleLabelTransportCtx)
    (hflatB : PfpFlatBoxClear) (hflatR : PfpFlatRouteClear)
    (hflatT : PfpFlatTitleClear)
    (hNoDesc : PfpReachedNoDescLabels)
    (hcap : PfpCaptionLabelCase) (hcross : PfpCrossSideClear) :
    ExpandChildParentFrameStrict group parent := by
  have hctx0 := hctx
  obtain ⟨hwf, _, _, hchild, hparent, _⟩ := hctx0
  have hP := hparams.1
  obtain ⟨metric, hm, hwrap⟩ := hparams.2.2
  have hcm := layoutRecursive_canvas_margins fuel hchild
  have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
    rw [checkedParams_canvasMargin hP]
    exact hcm.1
  have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
    rw [checkedParams_canvasMargin hP]
    exact hcm.2
  have hfitP0 : InputFixedFit
      (parentSubInput inp group P titleLines child) o :=
    (fitPerCall_of_top htop hr).parentSubInput hwf hP hm hwrap hcw hch
  have hwfPar : WellFormed
      (inputModel (parentSubInput inp group P titleLines child) o) :=
    pfpCtx_parentInput_wellFormed hctx
  have hfpPar : framedParents
      (parentSubInput inp group P titleLines child) = true :=
    pfpCtx_parentInput_framed hframed hctx
  have hfixP0 : ∃ s,
      (group.id, s) ∈
        (parentSubInput inp group P titleLines child).fixedSizes :=
    ⟨childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0)
      ((max 1 titleLines.length : Int) * P.lineH)
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩,
      List.mem_append_right _ (List.mem_singleton_self _)⟩
  have hfrags := pfp_frags_of_recursive_ctx
    (parentSubInput inp group P titleLines child) o
    hboxT hrouteT htitleT hflatB hflatR hflatT hcap hcross fuel
    (parentSubInput inp group P titleLines child) o parent group
    hfitP0 FitReached.refl hfixP0 hparent hwfPar hfpPar hdisjTop
  obtain ⟨hndLabels, hndRoutes⟩ := hNoDesc fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctx fuel
    (parentSubInput inp group P titleLines child) o parent FitReached.refl
    hparent
  intro frame hframe pl hpl hown
  by_cases hbox : ∃ b ∈ parent.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group"
  · exact hfrags.1 frame hframe pl hpl hown hbox (hndLabels pl hpl hown)
  · by_cases hgroup : ∃ b ∈ parent.scene.boxes,
      b.id = pl.owner ∧ b.role = "group"
    · exact hfrags.2.2 frame hframe pl hpl hown hgroup
        (hndLabels pl hpl hown)
    · have hnoBox : ∀ b ∈ parent.scene.boxes, b.id ≠ pl.owner := by
        intro b hb heq
        by_cases hrole : b.role = "group"
        · exact absurd ⟨b, hb, heq, hrole⟩ hgroup
        · exact absurd ⟨b, hb, heq, hrole⟩ hbox
      exact hfrags.2.1 frame hframe pl hpl hown hnoBox
        (hndRoutes pl hpl hown)

end Elegant.Layered.PipelineImpl

namespace PfpTransportCtxEvidence

open Elegant
open Elegant.Layered
open Elegant.Layered.PipelineImpl

/-- Probe input A copy: nested groups with member and sibling labels. -/
def pfpcInpA : Input :=
  { kind := "flowchart",
    boxes := [{ id := "A", role := .group, parent := "", direction := "TB", exclusive := false },
      { id := "G", role := .group, parent := "A", direction := "TB", exclusive := false },
      { id := "X", role := .node, parent := "G", exclusive := false },
      { id := "S", role := .node, parent := "A", exclusive := false }],
    routes := [], texts := ["root title here", "group title here long", "", ""],
    edges := [],
    labels := [{ id := "LX", owner := "X", text := "hello hello hello world" },
      { id := "LS", owner := "S", text := "sibling" }] }

/-- Probe input B copy: nested groups with an edge label. -/
def pfpcInpB : Input :=
  { kind := "flowchart",
    boxes := [{ id := "A", role := .group, parent := "", direction := "LR", exclusive := false },
      { id := "G", role := .group, parent := "A", direction := "LR", exclusive := false },
      { id := "X", role := .node, parent := "G", exclusive := false },
      { id := "Y", role := .node, parent := "G", exclusive := false },
      { id := "S", role := .node, parent := "A", exclusive := false }],
    routes := [{ id := "e1", fromId := "X", toId := "Y" },
      { id := "e2", fromId := "S", toId := "A" }],
    texts := ["root title here", "group title here long", "", "", ""],
    edges := [],
    labels := [{ id := "LX", owner := "X", text := "member label here" },
      { id := "Le1", owner := "e1", text := "edge label here" },
      { id := "LS", owner := "S", text := "sibling" }] }

/-- Probe input C copy: three-deep nesting. -/
def pfpcInpC : Input :=
  { kind := "flowchart",
    boxes := [{ id := "R", role := .group, parent := "", direction := "TB", exclusive := false },
      { id := "A", role := .group, parent := "R", direction := "TB", exclusive := false },
      { id := "G", role := .group, parent := "A", direction := "TB", exclusive := false },
      { id := "X", role := .node, parent := "G", exclusive := false }],
    routes := [], texts := ["root title here", "mid title here", "inner title here long", ""],
    edges := [],
    labels := [{ id := "LX", owner := "X", text := "deep member label here" }] }

/-- Extra input D: probe input A plus a label owned by group `A`, so that
caption pairs (owner = split group at the `A` split) occur non-vacuously. -/
def pfpcInpD : Input :=
  { kind := "flowchart",
    boxes := [{ id := "A", role := .group, parent := "", direction := "TB", exclusive := false },
      { id := "G", role := .group, parent := "A", direction := "TB", exclusive := false },
      { id := "X", role := .node, parent := "G", exclusive := false },
      { id := "S", role := .node, parent := "A", exclusive := false }],
    routes := [], texts := ["root title here", "group title here long", "", ""],
    edges := [],
    labels := [{ id := "LX", owner := "X", text := "hello hello hello world" },
      { id := "LS", owner := "S", text := "sibling" },
      { id := "LA", owner := "A", text := "group A caption here" }] }

def pfpcOpt : Options := {}

/-- Decidable box-fragment check on a concrete scene for one group id. Every
box-class conclusion of `PfpCaptionLabelCase` and `PfpCrossSideClear` (box
disjunct) is an instance of one such check. -/
def pfpcBoxFragBool (S : FamilyResult) (G : String) : Bool :=
  S.scene.boxes.all fun frame =>
    if frame.id != G then true else
      S.scene.labels.all fun pl =>
        if pl.owner == G then true else
          let hasBox := S.scene.boxes.any fun b => (b.id == pl.owner) && (b.role != "group")
          if !hasBox then true else
            if (S.scene.layoutDump.ancestors pl.owner).contains G then true else
              !(decide (frame.rect.StrictInside pl.rect))

/-- Decidable route-fragment check. Every route-class conclusion of
`PfpCaptionLabelCase` (route disjunct) is an instance of one such check. -/
def pfpcRouteFragBool (S : FamilyResult) (G : String) : Bool :=
  S.scene.boxes.all fun frame =>
    if frame.id != G then true else
      S.scene.labels.all fun pl =>
        if pl.owner == G then true else
          let boxed := S.scene.boxes.any fun b => (b.id == pl.owner)
          if boxed then true else
            let okEnds := S.scene.routes.all fun r =>
              if r.id != pl.owner then true else
                let a1 := (S.scene.layoutDump.ancestors r.fromId).contains G
                let a2 := (S.scene.layoutDump.ancestors r.toId).contains G
                (!a1 || !a2)
            if !okEnds then true else
              !(decide (frame.rect.StrictInside pl.rect))

/-- Decidable title-fragment check. Every title-class conclusion of
`PfpCaptionLabelCase` (group disjunct) and `PfpCrossSideClear` is an instance
of one such check. -/
def pfpcTitleFragBool (S : FamilyResult) (G : String) : Bool :=
  S.scene.boxes.all fun frame =>
    if frame.id != G then true else
      S.scene.labels.all fun pl =>
        if pl.owner == G then true else
          let hasGroup := S.scene.boxes.any fun b => (b.id == pl.owner) && (b.role == "group")
          if !hasGroup then true else
            if (S.scene.layoutDump.ancestors pl.owner).contains G then true else
              !(decide (frame.rect.StrictInside pl.rect))

def pfpcGroupsOf (inp : Input) : List String :=
  (inp.boxes.filter fun b => b.role == .group).map (·.id)

#eval match layoutRecursive 2 pfpcInpA pfpcOpt with
  | .error _ => ("A failed", false, false, false)
  | .ok res =>
    ("A ok",
      (pfpcGroupsOf pfpcInpA).all fun g => pfpcBoxFragBool res g,
      (pfpcGroupsOf pfpcInpA).all fun g => pfpcRouteFragBool res g,
      (pfpcGroupsOf pfpcInpA).all fun g => pfpcTitleFragBool res g)

#eval match layoutRecursive 2 pfpcInpB pfpcOpt with
  | .error _ => ("B failed", false, false, false)
  | .ok res =>
    ("B ok",
      (pfpcGroupsOf pfpcInpB).all fun g => pfpcBoxFragBool res g,
      (pfpcGroupsOf pfpcInpB).all fun g => pfpcRouteFragBool res g,
      (pfpcGroupsOf pfpcInpB).all fun g => pfpcTitleFragBool res g)

#eval match layoutRecursive 3 pfpcInpC pfpcOpt with
  | .error _ => ("C failed", false, false, false)
  | .ok res =>
    ("C ok",
      (pfpcGroupsOf pfpcInpC).all fun g => pfpcBoxFragBool res g,
      (pfpcGroupsOf pfpcInpC).all fun g => pfpcRouteFragBool res g,
      (pfpcGroupsOf pfpcInpC).all fun g => pfpcTitleFragBool res g)

#eval match layoutRecursive 2 pfpcInpD pfpcOpt with
  | .error _ => ("D failed", false, false, false)
  | .ok res =>
    ("D ok",
      (pfpcGroupsOf pfpcInpD).all fun g => pfpcBoxFragBool res g,
      (pfpcGroupsOf pfpcInpD).all fun g => pfpcRouteFragBool res g,
      (pfpcGroupsOf pfpcInpD).all fun g => pfpcTitleFragBool res g)

/- Non-vacuity: labels owned by groups (caption pairs) occur on input D. -/
#eval match layoutRecursive 2 pfpcInpD pfpcOpt with
  | .error _ => ([("failed", "")] : List (String × String))
  | .ok res =>
    (res.scene.labels.filter fun (pl : SceneLabel) =>
      res.scene.boxes.any fun (b : Box) => (b.id == pl.owner) && (b.role == "group")).map
      fun (pl : SceneLabel) => (pl.id, pl.owner)

#eval ((pfpcInpA.boxes.all fun b => !(pfpcInpA.routes.map (·.id)).contains b.id),
  (pfpcInpB.boxes.all fun b => !(pfpcInpB.routes.map (·.id)).contains b.id),
  (pfpcInpC.boxes.all fun b => !(pfpcInpC.routes.map (·.id)).contains b.id),
  (pfpcInpD.boxes.all fun b => !(pfpcInpD.routes.map (·.id)).contains b.id))

end PfpTransportCtxEvidence

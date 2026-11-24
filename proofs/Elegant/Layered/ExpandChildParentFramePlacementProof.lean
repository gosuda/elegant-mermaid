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
import Elegant.Layered.ExpandChildAncestryProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Parent-frame placement for executed `expandChild` calls

`ExpandChildParentFrameStrict group parent` says the group frame does not
strictly contain a foreign-owned label in the parent scene. The label classes need
different placement facts (box labels: anchoring and width; route labels: route
anchor and route miss; group titles: title band ordering), and every label
inset fact consumes `InputFixedFit`, which the seam field hypotheses do not
provide. The top-level fit reaches each call through `FitReached`
(`ExpandChildFitPerCall.fitPerCall_of_top`).

Probe evidence refuted the naive universal shapes: a flat layout of a
nested input puts a descendant group title strictly inside the outer frame,
and a non-exclusive member caption is strictly inside its outer frame on
executed runs (`proofs/wip/Probe/PfpFlatFactsTProbe2.lean`: witness `pfpNE`,
label `lx` strictly inside frame `G` with `isDesc` true, across all
profile/direction configs; empty-text labels behave the same). The residuals
below are narrowed accordingly:

* the box fragment only covers labels whose owner is not a strict
  descendant of the frame (member captions stay inside their own frame);
* the title fragment only covers labels whose owner is not a strict
  descendant of the frame (ancestor and unrelated titles);
* the route fragment only covers labels on routes with an endpoint outside
  the frame's strict descendants;
* every transport assumes the assembled call splits a different group.
  `expandChild_group_ancestor_absent` proves the non-descendant premises for
  the call's parent scene.

Each residual is a single fact, strictly narrower than the goal. The
scene-level fuel induction over the parent input's descent and the per-call
conclusion are proved from them.
-/

/-- Box-owned fragment: the frame of `G` does not strictly contain a label
owned by a non-group scene box outside the strict descendants of `G`. The
unrestricted form is false: a member caption is strictly inside its outer
frame on executed runs (see the module docstring); the non-descendant
premise follows from `expandChild_group_ancestor_absent` for the parent scene. -/
private def pfp_boxFrag (S : FamilyResult) (G : ModelBox) : Prop :=
  ∀ (frame : Box),
    S.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ S.scene.labels, pl.owner ≠ G.id →
      (∃ b ∈ S.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group") →
      (G.id ∉ S.scene.layoutDump.ancestors pl.owner) →
      ¬ frame.rect.StrictInside pl.rect

/-- Route-owned fragment: the frame of `G` does not strictly contain a label
on a route with an endpoint outside the strict descendants of `G`. -/
private def pfp_routeFrag (S : FamilyResult) (G : ModelBox) : Prop :=
  ∀ (frame : Box),
    S.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ S.scene.labels, pl.owner ≠ G.id →
      (∀ b ∈ S.scene.boxes, b.id ≠ pl.owner) →
      (∀ r ∈ S.scene.routes, r.id = pl.owner →
        (G.id ∉ S.scene.layoutDump.ancestors r.fromId ∨
          G.id ∉ S.scene.layoutDump.ancestors r.toId)) →
      ¬ frame.rect.StrictInside pl.rect

/-- Title fragment: the frame of `G` does not strictly contain a label owned
by a group box that is not a strict descendant of `G`. -/
private def pfp_titleFrag (S : FamilyResult) (G : ModelBox) : Prop :=
  ∀ (frame : Box),
    S.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ S.scene.labels, pl.owner ≠ G.id →
      (∃ b ∈ S.scene.boxes, b.id = pl.owner ∧ b.role = "group") →
      (G.id ∉ S.scene.layoutDump.ancestors pl.owner) →
      ¬ frame.rect.StrictInside pl.rect

/-- Box-class flat placement residual: in a flat executed layout with fit,
the group frame does not strictly contain a box-owned foreign label outside
its strict descendants. -/
def PfpFlatBoxClear : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → ∀ (G : ModelBox), pfp_boxFrag res G

/-- Route-class flat placement residual: flat only, endpoint-restricted. -/
def PfpFlatRouteClear : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → ∀ (G : ModelBox), pfp_routeFrag res G

/-- Title-class flat placement residual: flat only, descendant-restricted. -/
def PfpFlatTitleClear : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecution inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → ∀ (G : ModelBox), pfp_titleFrag res G

/-- Box-class transport residual: one `expandChild` assembly step for a
different group preserves the box fragment from both sub-scenes. -/
def PfpBoxLabelTransport : Prop :=
  ∀ (P : Params) (inp : Input) (o : Options) (inner G : ModelBox)
    (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o inner titleHeight parent child = .ok res →
    inner.id ≠ G.id →
    pfp_boxFrag parent G → pfp_boxFrag child G → pfp_boxFrag res G

/-- Route-class transport residual: one assembly step for a different group
preserves the route fragment. -/
def PfpRouteLabelTransport : Prop :=
  ∀ (P : Params) (inp : Input) (o : Options) (inner G : ModelBox)
    (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o inner titleHeight parent child = .ok res →
    inner.id ≠ G.id →
    pfp_routeFrag parent G → pfp_routeFrag child G → pfp_routeFrag res G

/-- Title-class transport residual: one assembly step for a different group
preserves the title fragment. -/
def PfpTitleLabelTransport : Prop :=
  ∀ (P : Params) (inp : Input) (o : Options) (inner G : ModelBox)
    (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o inner titleHeight parent child = .ok res →
    inner.id ≠ G.id →
    pfp_titleFrag parent G → pfp_titleFrag child G → pfp_titleFrag res G

/-- The parent sub-input is well-formed. -/
private theorem pfp_parentInput_wellFormed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    WellFormed (inputModel (parentSubInput inp group P titleLines child) o) := by
  exact (subInputWellFormedC2 inp o group hctx.1).2 _ _ _

/-- The parent sub-input is framed. -/
private theorem pfp_parentInput_framed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    framedParents (parentSubInput inp group P titleLines child) = true := by
  exact framedParents_selectInput_outside_append inp o group hctx.1 hframed
    _ child.scene child.itemArea

/-- All three class fragments hold for every recursive result reached from the
call's parent input, by scene-level fuel induction. The group stays fixed
along the descent, so every inner split is for a different group and the
transports apply. -/
private theorem pfp_frags_of_recursive (P0 : Input) (o0 : Options)
    (hboxT : PfpBoxLabelTransport) (hrouteT : PfpRouteLabelTransport)
    (htitleT : PfpTitleLabelTransport)
    (hflatB : PfpFlatBoxClear) (hflatR : PfpFlatRouteClear)
    (hflatT : PfpFlatTitleClear) (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult) (G : ModelBox),
      InputFixedFit P0 o0 → FitReached P0 o0 inp o →
      (∃ s, (G.id, s) ∈ inp.fixedSizes) →
      layoutRecursive fuel inp o = .ok res →
      WellFormed (inputModel inp o) → framedParents inp = true →
      pfp_boxFrag res G ∧ pfp_routeFrag res G ∧ pfp_titleFrag res G := by
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro inp o res G hfitP0 hr hfixG hrec hwf hfp
    cases fuel with
    | zero =>
      have hfit : InputFixedFit inp o := fitPerCall_of_top hfitP0 hr
      have hlay : layout inp o = .ok res := hrec
      obtain ⟨exec⟩ := layout_sceneExecution hlay
      exact ⟨hflatB exec hwf hfp hfit G, hflatR exec hwf hfp hfit G,
        hflatT exec hwf hfp hfit G⟩
    | succ f =>
      rcases layoutRecursive_succ_sources hrec with ⟨_, hlay⟩ |
        ⟨g', _, _, _, _, _, hg', _, _, _, _, _, _⟩
      · have hfit : InputFixedFit inp o := fitPerCall_of_top hfitP0 hr
        obtain ⟨exec⟩ := layout_sceneExecution hlay
        exact ⟨hflatB exec hwf hfp hfit G, hflatR exec hwf hfp hfit G,
          hflatT exec hwf hfp hfit G⟩
      · have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
        have hcovered : RoutesCovered inp := inputRoutesCovered hwf
        obtain ⟨P'', met'', chi'', tls'', par'', _, _, _, _, hP'', hm'',
          hchild'', hwrap'', hparent'', hexpand'', _, _, _, _, _, _, _, _⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg' hrec
        have hwfChi : WellFormed
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

        have ihPar := ih f (Nat.lt_succ_self f)
          (parentSubInput inp g' P'' tls'' chi'') o par'' G
          hfitP0 hrPar hfixPar hparent'' hwfPar hfpPar
        have ihChi := ih f (Nat.lt_succ_self f) (childSubInput inp g')
          (childSubOptions o g') chi'' G hfitP0 hrChi hfixChi hchild''
          hwfChi hfpChi
        exact ⟨hboxT P'' inp o g' G _ par'' chi'' res hexpand'' hne
          ihPar.1 ihChi.1,
          hrouteT P'' inp o g' G _ par'' chi'' res hexpand'' hne
          ihPar.2.1 ihChi.2.1,
          htitleT P'' inp o g' G _ par'' chi'' res hexpand'' hne
          ihPar.2.2 ihChi.2.2⟩

/-- `parentFrameStrict`: the parent scene of every executed `expandChild` call
satisfies `ExpandChildParentFrameStrict`, given the top-level fit threaded to
the call plus the six placement residuals. -/
theorem parentFrameStrict_of_recursion
    (tin : Input) (to : Options)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (htop : InputFixedFit tin to)
    (hr : FitReached tin to inp o)
    (hboxT : PfpBoxLabelTransport) (hrouteT : PfpRouteLabelTransport)
    (htitleT : PfpTitleLabelTransport)
    (hflatB : PfpFlatBoxClear) (hflatR : PfpFlatRouteClear)
    (hflatT : PfpFlatTitleClear) :
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
    pfp_parentInput_wellFormed hctx
  have hfpPar : framedParents
      (parentSubInput inp group P titleLines child) = true :=
    pfp_parentInput_framed hframed hctx
  have hfixP0 : ∃ s,
      (group.id, s) ∈
        (parentSubInput inp group P titleLines child).fixedSizes :=
    ⟨childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0)
      ((max 1 titleLines.length : Int) * P.lineH)
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩,
      List.mem_append_right _ (List.mem_singleton_self _)⟩
  have hfrags := pfp_frags_of_recursive
    (parentSubInput inp group P titleLines child) o
    hboxT hrouteT htitleT hflatB hflatR hflatT fuel
    (parentSubInput inp group P titleLines child) o parent group
    hfitP0 FitReached.refl hfixP0 hparent hwfPar hfpPar
  have hancestor := expandChild_group_ancestor_absent hctx
  intro frame hframe pl hpl hown
  by_cases hbox : ∃ b ∈ parent.scene.boxes, b.id = pl.owner ∧ b.role ≠ "group"
  · exact hfrags.1 frame hframe pl hpl hown hbox (hancestor pl.owner)
  · by_cases hgroup : ∃ b ∈ parent.scene.boxes,
      b.id = pl.owner ∧ b.role = "group"
    · exact hfrags.2.2 frame hframe pl hpl hown hgroup (hancestor pl.owner)
    · have hnoBox : ∀ b ∈ parent.scene.boxes, b.id ≠ pl.owner := by
        intro b hb heq
        by_cases hrole : b.role = "group"
        · exact absurd ⟨b, hb, heq, hrole⟩ hgroup
        · exact absurd ⟨b, hb, heq, hrole⟩ hbox
      exact hfrags.2.1 frame hframe pl hpl hown hnoBox
        (fun r _ _ => Or.inl (hancestor r.fromId))

end Elegant.Layered.PipelineImpl

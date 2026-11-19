import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.ExpandChildC8GeometryProof
import Elegant.Layered.RecursiveC78
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExpandChildAncestryProof
import Elegant.Layered.ExpandChildLabelFactsProof
import Elegant.Layered.ExactStepFacts
import Elegant.Layered.RecursiveBEq
set_option autoImplicit false

open Elegant.Layered.Compound

namespace Elegant.Layered.PipelineImpl

/-!
# Parent-frame facts below the fuel

`expandChild_parentFrame_boxes` and its siblings in
`ExpandChildParentFrameProof.lean` take `hgeoAll : RecursiveStepFacts
ExpandChildC8aGeometry` / `...C8bGeometry`, which is the open seam itself.
The parent scene of an executed call, however, is a successful recursive
layout at the same fuel whose own C8a/C8b follow from the flat clauses plus
the step facts at strictly smaller fuels.  This module carries those
smaller-fuel facts as the induction hypothesis (`StepFactsBelow`), proves
the full `ExpandChildParentFrame` from them, and closes the loop with the
generic fuel-induction principle `recursiveStepFacts_of_below`.

Residual hypotheses kept here: `ExpandChildParentFrameStrict`,
`ExpandChildParentStrictStep` (used via the public ancestor theorem), and
`InputFixedFit` of the parent sub-input (which `RecursiveStepFacts` does not
provide; the C8b lift needs it).  Each is strictly narrower than the target:
one parent-scene fact about one pipeline stage.  The route fact
`ExpandChildParentRouteClear` is not needed for the four-conjunct target and
is left to `expandChild_parentFrame_routes`, which has no circular premise.
-/

/-- The step fact restricted to strictly smaller fuels: the induction
hypothesis that breaks the `hgeoAll` circle.  Same premises as
`RecursiveStepFacts`, with the call fuel bound below `fuel`. -/
def StepFactsBelow (fuel : Nat)
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop) : Prop :=
  ∀ (fuel' : Nat), fuel' < fuel → ∀ (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContext fuel' P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    Step P inp o group titleHeight parent child res

/-- Base-parametric form of `StepFactsBelow`, over `ExpandChildCallContextB`. -/
def StepFactsBelowB (base : Input → Options → Except LayoutError FamilyResult)
    (fuel : Nat)
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop) : Prop :=
  ∀ (fuel' : Nat), fuel' < fuel → ∀ (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB base fuel' P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    Step P inp o group titleHeight parent child res

/-- Fuel induction closes the loop for any step: if the step at each fuel
follows from the step facts strictly below it, the step holds at all fuels. -/
theorem recursiveStepFacts_of_below
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop)
    (hclose : ∀ (fuel : Nat), StepFactsBelow fuel Step →
      ∀ (P : Params) (inp : Input) (o : Options) (group : ModelBox)
        (titleLines : List Measure.Line) (titleHeight : Int)
        (parent child res : FamilyResult),
        expandChild P inp o group titleHeight parent child = .ok res →
        framedParents inp = true →
        ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
        ExpandChildCallParams P inp o group titleLines titleHeight →
        Step P inp o group titleHeight parent child res) :
    RecursiveStepFacts Step := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
    exact hclose fuel (fun f hlt P' inp' o' g' tls' th' par' chi' res' hx hf hc hp =>
      ih f hlt P' inp' o' g' tls' th' par' chi' res' hx hf hc hp)
      P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
 /-- Base-parametric fuel induction: the same closure principle over
 `ExpandChildCallContextB`. -/
theorem recursiveStepFactsB_of_below
    (base : Input → Options → Except LayoutError FamilyResult)
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop)
    (hclose : ∀ (fuel : Nat), StepFactsBelowB base fuel Step →
      ∀ (P : Params) (inp : Input) (o : Options) (group : ModelBox)
        (titleLines : List Measure.Line) (titleHeight : Int)
        (parent child res : FamilyResult),
        expandChild P inp o group titleHeight parent child = .ok res →
        framedParents inp = true →
        ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res →
        ExpandChildCallParams P inp o group titleLines titleHeight →
        Step P inp o group titleHeight parent child res) :
    RecursiveStepFactsB base Step := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
    exact hclose fuel (fun f hlt P' inp' o' g' tls' th' par' chi' res' hx hf hc hp =>
      ih f hlt P' inp' o' g' tls' th' par' chi' res' hx hf hc hp)
      P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams

/-! ## Below-fuel copies of the private parent-scene toolkit -/

/-- The parent sub-input is well-formed (copy of the private lemma in
`ExpandChildParentFrameProof.lean`; `inputModel` ignores the fixed side
tables). -/
private theorem parentInput_wellFormed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    WellFormed (inputModel (parentSubInput inp group P titleLines child) o) := by
  exact inputModel_wellFormed_fixed_congr _ _ _
    (selectInput_wellFormed inp o
      (fun box => !Compound.inside inp.boxes group.id box.id) "" hctx.1
      (fun c hc hkept => keepOutside_close (group := group.id)
        (inputFacts_of_wellFormed hctx.1) hc hkept) o)

/-- The parent sub-input is framed (copy of the private lemma in
`ExpandChildParentFrameProof.lean`). -/
private theorem parentInput_framed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    framedParents (parentSubInput inp group P titleLines child) = true := by
  exact framedParents_selectInput_outside_append inp o group hctx.1 hframed
    _ child.scene child.itemArea

/-- The located frame carries the group id (copy of the private lemma in
`ExpandChildParentFrameProof.lean`). -/
private theorem frame_id_eq {group : ModelBox} {parent : FamilyResult}
    {frame : Box}
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
    frame.id = group.id := by
  simpa using List.find?_some hframe

/-- The frame has group role and the group's ancestor chain is isolated from
the other parent boxes (copy of the private lemma in
`ExpandChildParentFrameProof.lean`, taking the single ancestry fact from the
globally proved `stepC8aAncestry_holds` instead of a `∀`-quantified seam). -/
private theorem parentFrame_role_isolation
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines titleLines' : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult} {frame : Box} {dx dy : Int}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hanc : ExpandChildC8aAncestry group parent child res)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hdx : dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin)
    (hdy : dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin)
    (hwrap : ExpandChildTitleWrapped P inp o group titleLines') :
    frame.role = "group" ∧
      (∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
        group.id ∉ parent.scene.layoutDump.ancestors pb.id) := by
  obtain ⟨_, _, _, _, hrole, _, _, hiso⟩ :=
    expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hanc
      frame titleLines' dx dy hframe hdx hdy hwrap
  exact ⟨hrole, hiso⟩

/-- The C8a step of one expansion from the below-fuel geometry: the same
assembly as the private `hstep` in `parentScene_c8a`, with `hgeoAll` replaced
by `below8a` at `n` and the ancestry by the globally proved
`stepC8aAncestry_holds`. -/
private theorem c8aStep_of_below {F n : Nat} (hlt : n < F)
    (below8a : StepFactsBelow F ExpandChildC8aGeometry)
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext n P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC8aStep P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
    expandChild_c8a_structure n P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx
      (stepC8aAncestry_holds n P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams)
      frame tl dx dy hframe hdx hdy hwrap
  have hg := below8a n hlt P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
  exact ⟨s1, s2, s3, s4, s5, s6, hg, s7, s8⟩

/-- `layoutRecursive` preserves C8a from the flat clause and the below-fuel
geometry: the same induction as `layoutRecursive_c8a_of_flat`, querying the
step only at fuels below `F`. -/
private theorem layoutRecursive_c8a_of_below (hflat8a : FlatC8a) {F : Nat}
    (below8a : StepFactsBelow F ExpandChildC8aGeometry) :
    ∀ (n : Nat), n ≤ F → ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursive n inp o = .ok res → Validator.C8a res.scene.layoutDump := by
  intro n
  induction n with
  | zero =>
    intro _ inp o res hwf hframed h
    exact hflat8a inp o res hwf hframed h
  | succ n ih =>
    intro hle inp o res hwf hframed h
    have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
    have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
    rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
      ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
    · exact hflat8a inp o res hwf hframed hlayout
    · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
        hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
        layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
      obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
        subInputsWellFormed n inp o group P metric titleLines child parent hwf hframed hP hm hwrap
          hchild hparentAt
      have hchildC8a := ih (by omega : n ≤ F) _ _ _ hwfChild hframedChild hchild
      have hparentC8a := ih (by omega : n ≤ F) _ _ _ hwfParent hframedParent hparentAt
      have hstep := c8aStep_of_below (by omega : n < F) below8a hexpandAt hframed
        ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
        ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
      exact expandChild_c8a hchildC8a hparentC8a hstep hexpandAt

/-- The parent scene satisfies C8a from the flat clause and the below-fuel
geometry (below-fuel replacement for the private `parentScene_c8a`). -/
private theorem parentScene_c8a_below {F : Nat} (hflat8a : FlatC8a)
    (below8a : StepFactsBelow F ExpandChildC8aGeometry)
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext F P inp o group titleLines titleHeight parent child res) :
    Validator.C8a parent.scene.layoutDump := by
  have hparent : layoutRecursive F (parentSubInput inp group P titleLines child) o = .ok parent :=
    hctx.2.2.2.2.1
  exact layoutRecursive_c8a_of_below hflat8a below8a F (Nat.le_refl _)
    (parentSubInput inp group P titleLines child) o parent
    (parentInput_wellFormed hctx) (parentInput_framed hframed hctx) hparent

/-- The C8b step of one expansion from the below-fuel geometry: the same
assembly as the private `hstep` in `parentScene_c8b`, with `hgeoAll` replaced
by `below8b` at `n` and the owners by the proved `expandChild_label_owners`. -/
private theorem c8bStep_of_below {F n : Nat} (hlt : n < F)
    (below8b : StepFactsBelow F ExpandChildC8bGeometry)
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext n P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildC8bStep P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have howners := expandChild_label_owners n P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  have hc := expandChild_c8b_structure n P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx howners
    frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨g1, g2, g3, g4⟩ := below8b n hlt P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
  exact ⟨hc, g1, g2, g3, g4⟩

/-- `layoutRecursive` preserves C8b from the flat clause and the below-fuel
geometry: the same induction as `layoutRecursive_c8b_of_flat`, querying the
step only at fuels below `F`. -/
private theorem layoutRecursive_c8b_of_below (hflat8b : FlatC8b) {F : Nat}
    (below8b : StepFactsBelow F ExpandChildC8bGeometry) :
    ∀ (n : Nat), n ≤ F → ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o →
      layoutRecursive n inp o = .ok res → Validator.C8b res.scene.layoutDump := by
  intro n
  induction n with
  | zero =>
    intro _ inp o res hwf hframed hfit h
    exact hflat8b inp o res hwf hframed hfit h
  | succ n ih =>
    intro hle inp o res hwf hframed hfit h
    have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
    have hcovered : RoutesCovered inp := routesCovered_of_wellFormed hwf
    rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
      ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
    · exact hflat8b inp o res hwf hframed hfit hlayout
    · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
        hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
        layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
      obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
        subInputsWellFormed n inp o group P metric titleLines child parent hwf hframed hP hm hwrap
          hchild hparentAt
      have hfitChild : InputFixedFit
          (Elegant.Layered.PipelineImpl.childSubInput inp group)
          (Elegant.Layered.PipelineImpl.childSubOptions o group) :=
        hfit.childSubInput group
      have hcm := layoutRecursive_canvas_margins n hchild
      have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
        rw [checkedParams_canvasMargin hP]
        exact hcm.1
      have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
        rw [checkedParams_canvasMargin hP]
        exact hcm.2
      have hfitParent : InputFixedFit
          (parentSubInput inp group P titleLines child) o :=
        InputFixedFit.parentSubInput hwf hfit hP hm hwrap hcw hch
      have hchildC8b := ih (by omega : n ≤ F) _ _ _ hwfChild hframedChild hfitChild hchild
      have hparentC8b := ih (by omega : n ≤ F) _ _ _ hwfParent hframedParent hfitParent hparentAt
      have hstep := c8bStep_of_below (by omega : n < F) below8b hexpandAt hframed
        ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
        ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
      exact expandChild_c8b hchildC8b hparentC8b hstep hexpandAt

/-- The parent scene satisfies C8b from the flat clause and the below-fuel
geometry (below-fuel replacement for the private `parentScene_c8b`). -/
private theorem parentScene_c8b_below {F : Nat} (hflat8b : FlatC8b)
    (below8b : StepFactsBelow F ExpandChildC8bGeometry)
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hfit : InputFixedFit (parentSubInput inp group P titleLines child) o)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext F P inp o group titleLines titleHeight parent child res) :
    Validator.C8b parent.scene.layoutDump := by
  have hparent : layoutRecursive F (parentSubInput inp group P titleLines child) o = .ok parent :=
    hctx.2.2.2.2.1
  exact layoutRecursive_c8b_of_below hflat8b below8b F (Nat.le_refl _)
    (parentSubInput inp group P titleLines child) o parent
    (parentInput_wellFormed hctx) (parentInput_framed hframed hctx) hfit hparent

/-! ## The direct parent-frame fact -/

/-- The located frame satisfies the full `ExpandChildParentFrame` for every
executed call, from the flat clauses, the step geometry strictly below the
call fuel, the proved ancestry/owners, and the three per-call residuals.
The ancestor conjunct goes through the public `expandChild_parentFrame_ancestor`
(which needs no geometry seam); the route fact is separate
(`expandChild_parentFrame_routes` has no circular premise either). -/
theorem expandChild_parentFrame_direct
    (hflat8a : FlatC8a)
    (hflat8b : FlatC8b)
    {fuel : Nat}
    (below8a : StepFactsBelow fuel ExpandChildC8aGeometry)
    (below8b : StepFactsBelow fuel ExpandChildC8bGeometry)
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hframeStrict : ExpandChildParentFrameStrict group parent)
    (hstepStrict : ExpandChildParentStrictStep parent)
    (hfit : InputFixedFit (parentSubInput inp group P titleLines child) o) :
    ExpandChildParentFrame P inp o group titleHeight parent child := by
  have hanc : ExpandChildC8aAncestry group parent child res :=
    stepC8aAncestry_holds fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams
  intro frame titleLines' dx dy hframe hdx hdy hwrap
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pb hpbMem _hex hforeign
    have hfid := frame_id_eq hframe
    have hC8a := parentScene_c8a_below hflat8a below8a hexpand hframed hctx
    obtain ⟨hrole, hiso⟩ := parentFrame_role_isolation hexpand hframed hctx hanc
      hframe hdx hdy hwrap
    have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
      List.mem_of_find?_eq_some hframe
    have hpbMemD : pb ∈ parent.scene.layoutDump.boxes := hpbMem
    have hne' : pb.id ≠ group.id := by
      intro h
      apply hforeign
      rw [h]
      exact List.mem_cons.mpr (Or.inl rfl)
    have hne : pb.id ≠ frame.id := by
      rw [hfid]
      exact hne'
    have h1 : frame.id ∉ parent.scene.layoutDump.ancestors pb.id := by
      rw [hfid]
      exact hiso pb hpbMem hne'
    have h2 : pb.id ∉ parent.scene.layoutDump.ancestors frame.id := by
      rw [hfid]
      exact fun hm => hforeign (List.mem_cons.mpr (Or.inr hm))
    exact hC8a frame hframeMem hrole pb hpbMemD hne h1 h2
  · intro pl hplMem hown
    have hC8b := parentScene_c8b_below hflat8b below8b hfit hexpand hframed hctx
    obtain ⟨hrole, _⟩ := parentFrame_role_isolation hexpand hframed hctx hanc
      hframe hdx hdy hwrap
    have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
      List.mem_of_find?_eq_some hframe
    have hplD : pl.toLabel ∈ parent.scene.layoutDump.labels :=
      List.mem_map.mpr ⟨pl, hplMem, rfl⟩
    rcases hC8b frame hframeMem hrole pl.toLabel hplD with hdisj | hstrict
    · exact hdisj
    · have hstrict' : frame.rect.StrictInside pl.rect := hstrict
      exact absurd hstrict' (hframeStrict frame hframe pl hplMem hown)
  · exact expandChild_parentFrame_ancestor hstepStrict hexpand hframed hctx
      frame titleLines' dx dy hframe hdx hdy hwrap
  · intro g hg hgRole hgNe hgNotAnc1 hgNotAnc2
    have _hdx := hdx
    have _hdy := hdy
    have _hwrap := hwrap
    have _hdxv : dx = dx := rfl
    have _hdyv : dy = dy := rfl
    have _htlv : titleLines' = titleLines' := rfl
    have hfid := frame_id_eq hframe
    have hC8a := parentScene_c8a_below hflat8a below8a hexpand hframed hctx
    have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
      List.mem_of_find?_eq_some hframe
    have hgMemD : g ∈ parent.scene.layoutDump.boxes := hg
    have hne : frame.id ≠ g.id := by
      rw [hfid]
      exact fun h => hgNe h.symm
    have h1 : g.id ∉ parent.scene.layoutDump.ancestors frame.id := by
      rw [hfid]
      exact hgNotAnc1
    have h2 : frame.id ∉ parent.scene.layoutDump.ancestors g.id := by
      rw [hfid]
      exact hgNotAnc2
    exact hC8a g hgMemD hgRole frame hframeMem hne h1 h2

end Elegant.Layered.PipelineImpl

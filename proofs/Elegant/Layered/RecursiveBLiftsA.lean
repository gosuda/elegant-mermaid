import Elegant.Layered.InsetFit
import Elegant.Layered.RecursiveC2
import Elegant.Layered.OrthogonalityFacts
import Elegant.Layered.FramedParentsSub
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveCallParams

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound

/-- Successor sources for `layoutRecursiveB`: the counterpart of
`layoutRecursive_succ_sources`, by the same unfolding.  At `fuel + 1` either no
group is selected and `base` runs directly, or the selected group fixes `P`,
the metric, the two recursive `base` results and the `expandChild` merge. -/
theorem layoutRecursiveB_succ_sources
    (base : Input → Options → Except LayoutError FamilyResult)
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRecursiveB base (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧
      base inp o = .ok res) ∨
    ∃ (group : ModelBox) (P : Params) (metric : Measure.Metric)
      (child : FamilyResult) (titleLines : List Measure.Line) (parent : FamilyResult),
      inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      checkedParams o.profile inp.kind = .ok P ∧
      metricOf o.profile o.fontFamily = .ok metric ∧
      layoutRecursiveB base fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child ∧
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines ∧
      let titleWidth := titleLines.foldl (fun width line => max width line.width) 0
      let titleHeight := (max 1 titleLines.length : Int) * P.lineH
      let size := childFrameSize group.direction P.clusterPad titleWidth titleHeight
        ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩
      let parentInput := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
      layoutRecursiveB base fuel
        { parentInput with
          fixedSizes := parentInput.fixedSizes ++ [(group.id, size)]
          fixedChildren := parentInput.fixedChildren ++ [(group.id, child.scene)]
          fixedAreas := parentInput.fixedAreas ++ [(group.id, child.itemArea)] } o = .ok parent ∧
      expandChild P inp o group titleHeight parent child = .ok res := by
  unfold layoutRecursiveB at h
  dsimp only at h
  split at h
  · next hn => exact Or.inl ⟨hn, h⟩
  · next group hg =>
    obtain ⟨P, hP, h⟩ := bind_ok' h
    obtain ⟨metric, hm, h⟩ := bind_ok' h
    obtain ⟨child, hc, h⟩ := bind_ok' h
    obtain ⟨titleLines, ht, h⟩ := bind_ok' h
    obtain ⟨parent, hp, h⟩ := bind_ok' h
    exact Or.inr ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hc, ht, hp, h⟩

/-- Base-parametric copy of the flat inset fact `layout_inset`: `base` places
every scene box inside the margin inset of its canvas. -/
def FlatInsetB (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    base inp o = .ok res →
    ∃ P : Params, checkedParams o.profile inp.kind = .ok P ∧
      0 ≤ P.canvasMargin ∧ InsetC1 res.scene P.canvasMargin

/-- Base-parametric copy of the flat C3 fact `FlatC3'`. -/
def FlatC3B (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    base inp o = .ok res → Validator.C3 res.scene.layoutDump

/-- Base-parametric copy of the flat C4 fact behind `layout_c4`: `base`
places only orthogonal routes.  The plain lift is hard-wired to
`layout_sceneExecution`; here it is the `hflat` hypothesis on `base`. -/
def FlatC4B (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    base inp o = .ok res →
    ∀ route ∈ res.scene.routes, Polyline.isOrthogonal route.points = true
/-- Base-parametric copy of the flat C2 fact `FlatC2`. -/
def FlatC2B (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) →
    base inp o = .ok res → Validator.C2 res.scene.layoutDump


/-- Per-call fit and parent-closure for the `expandChild` calls
`layoutRecursiveB base` performs, over the base-parametric call context plus
the tracked call parameters.  This packages what the inset and C1/C3 lifts
need beyond the flat facts: the shifted child inset stays inside the frame
with both lookup transports (`ExpandChildFitsInset`), and both recursive
scenes are parent-closed.  True for executed layouts at `base := layout` by
`layoutRecursive_childInset_fits_frame` with the executed title wrap and by
`layoutRecursive_parent_closed_wellFormed` through the sub-inputs. -/
def ExpandChildFitClosedB
    (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildFitsInset P inp o group titleHeight parent child res ∧
      SceneParentClosed parent.scene ∧ SceneParentClosed child.scene

/-- The inset invariant through `layoutRecursiveB base`: mirror of
`layoutRecursive_inset`, with the flat inset as the `hflat` hypothesis on
`base` and the per-call frame fit supplied by `hfit`. -/
theorem layoutRecursiveB_inset
    (base : Input → Options → Except LayoutError FamilyResult)
    (hflat : FlatInsetB base) (hsub : SubInputWellFormedC2)
    (hfit : ExpandChildFitClosedB base) (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB base fuel inp o = .ok res →
      ∀ Q : Params, checkedParams o.profile inp.kind = .ok Q →
        0 ≤ Q.canvasMargin ∧ InsetC1 res.scene Q.canvasMargin := by
  induction fuel with
  | zero =>
    intro inp o res _hwf _hframed h Q hQ
    obtain ⟨P', hchecked, hm, hinset⟩ := hflat inp o res h
    have hQm : P' = Q := Except.ok.inj (hchecked.symm.trans hQ)
    subst hQm
    exact ⟨hm, hinset⟩
  | succ fuel ih =>
    intro inp o res hwf hframed h Q hQ
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hlayout⟩ |
      ⟨group, Pm, metric, child, titleLines, parent, hg, hPm, hm, hc, ht, hp, hexpand⟩
    · obtain ⟨P', hchecked, hm, hinset⟩ := hflat inp o res hlayout
      have hQm : P' = Q := Except.ok.inj (hchecked.symm.trans hQ)
      subst hQm
      exact ⟨hm, hinset⟩
    · have hQm : Pm = Q := Except.ok.inj (hPm.symm.trans hQ)
      subst hQm
      obtain ⟨hwfChild, hparentWF⟩ := hsub inp o group hwf
      obtain ⟨hframedChild, hframedParent⟩ :=
        framedParentsSub inp o group hwf hframed
      have hQchild : checkedParams
          { o with direction := directionOf group.direction }.profile
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id)
            group.id).kind = .ok Pm := hQ
      have hcIH := ih _ _ _ hwfChild hframedChild hc Pm hQchild
      have hQparent : checkedParams o.profile
          (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).kind =
          .ok Pm := hQ
      have hpIH := ih _ _ _ (hparentWF _ _ _) (hframedParent _ _ _) hp Pm hQparent
      have hparams : ExpandChildCallParams Pm inp o group titleLines
          ((max 1 titleLines.length : Int) * Pm.lineH) :=
        ⟨hPm, rfl, ⟨metric, hm, ht⟩⟩
      have hctx : ExpandChildCallContextB base fuel Pm inp o group titleLines
          ((max 1 titleLines.length : Int) * Pm.lineH) parent child res :=
        ⟨hwf, hg, rfl, hc, hp, hexpand⟩
      have hfitRes := hfit fuel Pm inp o group titleLines
        ((max 1 titleLines.length : Int) * Pm.lineH) parent child res
        hexpand hctx hparams
      obtain ⟨frame, _fm, ftl, _fl, dx, dy, hframe, hmS, htS, _hlS,
          hdx, hdy, hcanvas, hboxes⟩ := expandChild_sources hexpand
      obtain ⟨hfitC, _, _⟩ :=
        hfitRes.1 frame ftl dx dy hframe hdx hdy ⟨_fm, hmS, htS⟩
      refine ⟨hpIH.1, ?_⟩
      unfold InsetC1
      rw [hcanvas]
      intro b hb
      have hbMem : b ∈ res.scene.boxes := hb
      rw [hboxes] at hbMem
      obtain ⟨_, -, hfind⟩ := List.mem_filterMap.mp hbMem
      have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hfind
      have hFrameInInset : (insetRect parent.scene.canvas Pm.canvasMargin).Contained
          frame.rect := hpIH.2 frame (List.mem_of_find?_eq_some hframe)
      rcases List.mem_append.mp hbItems with hbc | hbp
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hbc
        have hshift :
            (shiftRect dx dy (insetRect child.scene.canvas Pm.canvasMargin)).Contained
              (shiftRect dx dy c.rect) :=
          (contained_shiftRect dx dy).mpr (hcIH.2 c hc)
        exact Rect.Contained.trans hFrameInInset (Rect.Contained.trans hfitC hshift)
      · exact hpIH.2 b hbp

/-- The C1/C3 lift over `layoutRecursiveB base`: mirror of
`layoutRecursive_c1_c3_of_inset`, with the flat inset and flat C3 as
hypotheses on `base` and the per-call fit and closure supplied by `hfit`. -/
theorem layoutRecursiveB_c1_c3
    (base : Input → Options → Except LayoutError FamilyResult)
    (hflatInset : FlatInsetB base) (hflat3 : FlatC3B base)
    (hsub : SubInputWellFormedC2) (hfit : ExpandChildFitClosedB base)
    (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB base fuel inp o = .ok res →
      Validator.C1 res.scene.layoutDump ∧ Validator.C3 res.scene.layoutDump := by
  induction fuel with
  | zero =>
    intro inp o res hwf hframed h
    refine ⟨?_, hflat3 inp o res hwf hframed h⟩
    intro b hb
    obtain ⟨_, _, hmargin, hinset⟩ := hflatInset inp o res h
    exact Rect.Contained.trans (insetRect_subset_canvas hmargin) (hinset b hb)
  | succ fuel ih =>
    intro inp o res hwf hframed h
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hlayout⟩ |
      ⟨group, P', metric', child', titleLines', parent', hg, hP', hm', hchild',
        hwrap', hparent', hexpand'⟩
    · refine ⟨?_, hflat3 inp o res hwf hframed hlayout⟩
      intro b hb
      obtain ⟨_, _, hmargin, hinset⟩ := hflatInset inp o res hlayout
      exact Rect.Contained.trans (insetRect_subset_canvas hmargin) (hinset b hb)
    · obtain ⟨hwfChild, hparentWF⟩ := hsub inp o group hwf
      obtain ⟨hframedChild, hframedParent⟩ :=
        framedParentsSub inp o group hwf hframed
      have hQchild : checkedParams
          { o with direction := directionOf group.direction }.profile
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id)
            group.id).kind = .ok P' := hP'
      have hcIH := ih _ _ _ hwfChild hframedChild hchild'
      have hpIH := ih _ _ _ (hparentWF _ _ _) (hframedParent _ _ _) hparent'
      have hmargin : 0 ≤ P'.canvasMargin := by
        have := checkedParams_canvasMargin_ge_one hP'
        omega
      have hparams' : ExpandChildCallParams P' inp o group titleLines'
          ((max 1 titleLines'.length : Int) * P'.lineH) :=
        ⟨hP', rfl, ⟨metric', hm', hwrap'⟩⟩
      have hctx' : ExpandChildCallContextB base fuel P' inp o group titleLines'
          ((max 1 titleLines'.length : Int) * P'.lineH) parent' child' res :=
        ⟨hwf, hg, rfl, hchild', hparent', hexpand'⟩
      have hfitRes' := hfit fuel P' inp o group titleLines'
        ((max 1 titleLines'.length : Int) * P'.lineH) parent' child' res
        hexpand' hctx' hparams'
      have hQparent : checkedParams o.profile
          (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).kind =
          .ok P' := hP'
      have hchildInset :=
        (layoutRecursiveB_inset base hflatInset hsub hfit fuel _ _ _
          hwfChild hframedChild hchild' P' hQchild).2
      exact expandChild_c1_c3_inset hmargin hpIH.1 hpIH.2 hchildInset hcIH.2
        hfitRes'.1 hfitRes'.2.1 hfitRes'.2.2 hexpand'

/-- `layoutRecursiveB base` preserves C2 given the flat clause for `base`:
mirror of `layoutRecursive_c2_of_flat`, with the per-call step stated over
`ExpandChildCallContextB base` followed by `ExpandChildCallParams`. -/
theorem layoutRecursiveB_c2
    (base : Input → Options → Except LayoutError FamilyResult)
    (hflat : FlatC2B base) (hsub : SubInputWellFormedC2)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      (∀ m ∈ inp.boxes, m.id ≠ "") →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC2Step P inp o group titleHeight parent child res)
    (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      (∀ m ∈ inp.boxes, m.id ≠ "") →
      layoutRecursiveB base fuel inp o = .ok res →
      Validator.C2 res.scene.layoutDump := by
  induction fuel with
  | zero =>
    intro inp o res hwf _hframed _ h
    exact hflat inp o res hwf h
  | succ fuel ih =>
    intro inp o res hwf hframed hidsCur h
    rcases layoutRecursiveB_succ_sources base h with ⟨_, hlayout⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hchild, hwrap,
        hparentAt, hexpandAt⟩
    · exact hflat inp o res hwf hlayout
    · obtain ⟨hchildWf, hparentWF⟩ := hsub inp o group hwf
      obtain ⟨hframedChild, hframedParent⟩ :=
        framedParentsSub inp o group hwf hframed
      have hstep := hgeo fuel P inp o group titleLines _ parent child res hexpandAt
        hidsCur ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
        ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
      refine expandChild_c2 (ih _ _ _ hchildWf hframedChild ?_ hchild)
        (ih _ _ _ (hparentWF _ _ _) (hframedParent _ _ _) ?_ hparentAt) hstep hexpandAt
      · exact selectInput_ids_nonempty hidsCur
          (fun box => Compound.inside inp.boxes group.id box.id) group.id
      · exact selectInput_ids_nonempty hidsCur
          (fun box => !Compound.inside inp.boxes group.id box.id) ""

/-- Orthogonality through `layoutRecursiveB base`: mirror of
`layoutRecursive_routes_orthogonal`, with the flat C4 fact on `base`. -/
theorem layoutRecursiveB_routes_orthogonal
    (base : Input → Options → Except LayoutError FamilyResult)
    (hflat : FlatC4B base) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursiveB base fuel inp o = .ok res →
      ∀ route ∈ res.scene.routes, Polyline.isOrthogonal route.points = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h
    exact hflat inp o res h
  | succ fuel ih =>
    intro inp o res h
    cases hg : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) with
    | none =>
      simp only [layoutRecursiveB, hg] at h
      exact hflat inp o res h
    | some group =>
      simp only [layoutRecursiveB, hg] at h
      obtain ⟨P, _, h⟩ := bind_ok' h
      obtain ⟨metric, _, h⟩ := bind_ok' h
      obtain ⟨child, hchild, h⟩ := bind_ok' h
      obtain ⟨titleLines, _, h⟩ := bind_ok' h
      obtain ⟨parent, hparent, h⟩ := bind_ok' h
      exact expandChild_routes_orthogonal
        (ih _ _ parent hparent) (ih _ _ child hchild) h

/-- The C4 lift over `layoutRecursiveB base`: mirror of `layoutRecursive_c4`. -/
theorem layoutRecursiveB_c4
    (base : Input → Options → Except LayoutError FamilyResult)
    (hflat : FlatC4B base) (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveB base fuel inp o = .ok res →
      Validator.C4 res.scene.layoutDump := by
  intro inp o res _hwf _hframed h
  intro route hroute _
  exact layoutRecursiveB_routes_orthogonal base hflat fuel inp o res h route hroute

/-- Sanity: the flat inset fact gives the `B` fact at `base := layout`. -/
theorem flatInsetB_of_flat
    (h : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      layout inp o = .ok res →
      ∃ P : Params, checkedParams o.profile inp.kind = .ok P ∧
        0 ≤ P.canvasMargin ∧ InsetC1 res.scene P.canvasMargin) :
    FlatInsetB layout := h

/-- Sanity: the flat C3 fact gives the `B` fact at `base := layout`. -/
theorem flatC3B_of_flat (h : FlatC3') : FlatC3B layout :=
  fun inp o res hwf hframed hok => h inp o res hwf hframed hok

/-- Sanity: the flat C2 fact gives the `B` fact at `base := layout`. -/
theorem flatC2B_of_flat (h : FlatC2) : FlatC2B layout :=
  fun inp o res hwf hok => h inp o res hwf hok

/-- Sanity: the flat orthogonality fact gives the `B` fact at `base := layout`. -/
theorem flatC4B_of_flat
    (h : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      layout inp o = .ok res →
      ∀ route ∈ res.scene.routes, Polyline.isOrthogonal route.points = true) :
    FlatC4B layout := h


end Elegant.Layered.PipelineImpl

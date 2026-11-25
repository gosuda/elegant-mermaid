import Elegant.Layered.ExactFitClosure
import Elegant.Layered.ExactStepFacts
import Elegant.Layered.ExactSubInputStepC2
import Elegant.Layered.ExpandChildParentFrameDirect
import Elegant.Layered.RecursiveBLiftsB

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- A run at fuel at most `F` uses expansion geometry only at context fuels
strictly below `F`. An expansion in a successor run has both subruns at the
predecessor fuel. -/
theorem layoutRecursiveB_c8b_of_below (exactIds : List String) {F : Nat}
    (hflat8b : FlatC8bB (layoutX exactIds))
    (hmargins : CanvasMarginsB (layoutX exactIds))
    (hsub : SubInputWellFormedB (layoutX exactIds))
    (below8b : StepFactsBelowB (layoutX exactIds) F
      (fun P inp o group titleHeight parent child res =>
        InputFixedFit inp o → ExpandChildC8bGeometry P inp o group titleHeight parent child res)) :
    ∀ (n : Nat), n ≤ F → ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      InputFixedFit inp o → layoutRecursiveB (layoutX exactIds) n inp o = .ok res →
      Validator.C8b res.scene.layoutDump := by
  intro n
  induction n with
  | zero =>
    intro _ inp o res hwf hframed hfit h
    have hbase : layoutX exactIds inp o = .ok res := by simpa [layoutRecursiveB] using h
    exact hflat8b inp o res hwf hframed hfit hbase
  | succ n ih =>
    intro hle inp o res hwf hframed hfit h
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with ⟨_, hbase⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hchild, hwrap, hparent, hexpand⟩
    · exact hflat8b inp o res hwf hframed hfit hbase
    · have hlt : n < F := by omega
      obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
        hsub n inp o group P metric titleLines child parent hwf hframed hP hm hwrap
          hchild hparent
      have hfitChild : InputFixedFit (childSubInput inp group) (childSubOptions o group) :=
        hfit.childSubInput group
      have hPchild : checkedParams (childSubOptions o group).profile
          (childSubInput inp group).kind = .ok P := hP
      have hmargin := hmargins n (childSubInput inp group) (childSubOptions o group)
        child hchild P hPchild
      have hfitParent : InputFixedFit (parentSubInput inp group P titleLines child) o :=
        InputFixedFit.parentSubInput hwf hfit hP hm hwrap hmargin.1 hmargin.2
      have hchildC8b := ih (Nat.le_of_lt hlt) _ _ _ hwfChild hframedChild hfitChild hchild
      have hparentC8b := ih (Nat.le_of_lt hlt) _ _ _ hwfParent hframedParent hfitParent hparent
      let titleHeight : Int := (max 1 titleLines.length : Int) * P.lineH
      have hctx : ExpandChildCallContextB (layoutX exactIds) n P inp o group titleLines
          titleHeight parent child res :=
        ⟨hwf, hg, rfl, hchild, hparent, hexpand⟩
      have hparams : ExpandChildCallParams P inp o group titleLines titleHeight :=
        ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
      have hgeometry := below8b n hlt P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams hfit
      have howners := XB_label_owners exactIds n P inp o group titleLines titleHeight
        parent child res hexpand hframed hctx hparams
      have hstep : ExpandChildC8bStep P inp o group titleHeight parent child res := by
        intro frame tl dx dy hframe hdx hdy hwrapped
        exact ⟨expandChild_c8b_structure_wrapped hexpand howners frame tl dx dy
          hframe hdx hdy hwrapped, hgeometry frame tl dx dy hframe hdx hdy hwrapped⟩
      exact expandChild_c8b hchildC8b hparentC8b hstep hexpand

/-- The executed parent run at context fuel `F` already satisfies C8b from
geometry below `F`. The successful child run supplies the margins needed to
transfer the caller's fit to the parent sub-input. -/
theorem XSGLB_parentScene_c8b_below (exactIds : List String) {F : Nat}
    (hflat8b : FlatC8bB (layoutX exactIds))
    (below8b : StepFactsBelowB (layoutX exactIds) F
      (fun P inp o group titleHeight parent child res =>
        InputFixedFit inp o → ExpandChildC8bGeometry P inp o group titleHeight parent child res))
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContextB (layoutX exactIds) F P inp o group titleLines
      titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hfit : InputFixedFit inp o) :
    Validator.C8b parent.scene.layoutDump := by
  obtain ⟨hwf, _, _, hchild, hparent, _⟩ := hctx
  obtain ⟨hP, _, metric, hm, hwrap⟩ := hparams
  obtain ⟨_, _, hwfParent, hframedParent⟩ :=
    subInputWellFormedB_layoutX exactIds F inp o group P metric titleLines child parent
      hwf hframed hP hm hwrap hchild hparent
  have hPchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  have hmargin := exactCanvasMargins exactIds F (childSubInput inp group)
    (childSubOptions o group) child hchild P hPchild
  have hfitParent : InputFixedFit (parentSubInput inp group P titleLines child) o :=
    InputFixedFit.parentSubInput hwf hfit hP hm hwrap hmargin.1 hmargin.2
  exact layoutRecursiveB_c8b_of_below exactIds hflat8b (exactCanvasMargins exactIds)
    (subInputWellFormedB_layoutX exactIds) below8b F (Nat.le_refl F)
    (parentSubInput inp group P titleLines child) o parent hwfParent hframedParent hfitParent hparent

end Elegant.Layered.PipelineImpl

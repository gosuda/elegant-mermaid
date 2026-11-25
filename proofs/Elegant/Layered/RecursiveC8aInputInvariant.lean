import Elegant.Layered.NotesAlignmentTransport
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.FamilyC5B

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

abbrev FlatC8aBOn (condition : Input → Prop)
    (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true → condition inp →
    base inp o = .ok res → Validator.C8a res.scene.layoutDump

abbrev FlatC8aBAligned (base : Input → Options → Except LayoutError FamilyResult) : Prop :=
  FlatC8aBOn (fun inp => attachedNoteParents inp = true) base

/-- This is the C8a recursion induction with a local condition on flat calls.
The existing unrestricted lift specializes to `fun _ => True`. -/
theorem layoutRecursiveB_c8a_on
    (base : Input → Options → Except LayoutError FamilyResult) {condition : Input → Prop}
    (hFlat : FlatC8aBOn condition base) (hSub : SubInputWellFormedB base)
    (hChild : ∀ (inp : Input) (o : Options) (group : ModelBox),
      WellFormed (inputModel inp o) → condition inp → condition (childSubInput inp group))
    (hParent : ∀ (inp : Input) (o : Options) (group : ModelBox) (P : Params)
      (lines : List Measure.Line) (child : FamilyResult),
      WellFormed (inputModel inp o) → condition inp →
      condition (parentSubInput inp group P lines child))
    (hStep : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStep P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true → condition inp →
      layoutRecursiveB base fuel inp o = .ok res → Validator.C8a res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf hfp hCond hok
    exact hFlat inp o res hwf hfp hCond hok
  | succ fuel ih =>
    intro inp o res hwf hfp hCond hok
    rcases layoutRecursiveB_succ_sources base hok with ⟨_, hBase⟩ |
      ⟨group, P, metric, child, lines, parent, hGroup, hParams, hMetric,
        hc, hWrap, hp, hExpand⟩
    · exact hFlat inp o res hwf hfp hCond hBase
    · obtain ⟨hwfC, hfpC, hwfP, hfpP⟩ := hSub fuel inp o group P metric lines child parent
        hwf hfp hParams hMetric hWrap hc hp
      have hCC := ih _ _ child hwfC hfpC (hChild inp o group hwf hCond) hc
      have hPC := ih _ _ parent hwfP hfpP (hParent inp o group P lines child hwf hCond) hp
      have hCallParams : ExpandChildCallParams P inp o group lines ((max 1 lines.length : Int) * P.lineH) :=
        ⟨hParams, rfl, ⟨metric, hMetric, hWrap⟩⟩
      have hContext : ExpandChildCallContextB base fuel P inp o group lines
          ((max 1 lines.length : Int) * P.lineH) parent child res :=
        ⟨hwf, hGroup, rfl, hc, hp, hExpand⟩
      exact expandChild_c8a hCC hPC (hStep fuel P inp o group lines _ parent child res
        hExpand hfp hContext hCallParams) hExpand

/-- Both local transport arguments come from the same box-selection invariant. -/
theorem layoutRecursiveB_c8a_aligned
    (base : Input → Options → Except LayoutError FamilyResult)
    (hFlat : FlatC8aBAligned base) (hSub : SubInputWellFormedB base)
    (hStep : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStep P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true → attachedNoteParents inp = true →
      layoutRecursiveB base fuel inp o = .ok res → Validator.C8a res.scene.layoutDump :=
  layoutRecursiveB_c8a_on base (condition := fun inp => attachedNoteParents inp = true) hFlat hSub
    (fun _ _ group hwf halign => attachedNoteParents_childSubInput (Model.boxIds_nodup hwf) halign group)
    (fun _ _ group P lines child hwf halign =>
      attachedNoteParents_parentSubInput (Model.boxIds_nodup hwf) halign group P lines child)
    hStep

end Elegant.Layered.PipelineImpl

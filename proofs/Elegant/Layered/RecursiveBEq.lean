import Elegant.Layered.ExactPipeline
import Elegant.Layered.RecursiveCallContext

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

theorem layoutRecursive_eq_B :
    ∀ (fuel : Nat) (inp : Input) (o : Options),
      layoutRecursive fuel inp o = layoutRecursiveB layout fuel inp o := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o
    rfl
  | succ fuel ih =>
    intro inp o
    unfold layoutRecursive layoutRecursiveB
    simp only [ih]
    rfl

theorem layoutFamily_eq_B :
    ∀ (inp : Input) (o : Options),
      layoutFamily inp o = layoutFamilyB layout inp o := by
  intro inp o
  unfold layoutFamily layoutFamilyB
  simp only [layoutRecursive_eq_B]
  rfl

theorem layoutRecursiveB_compose :
    ∀ (base : Input → Options → Except LayoutError FamilyResult) (m n : Nat) (inp : Input)
      (o : Options),
      layoutRecursiveB (layoutRecursiveB base n) m inp o =
        layoutRecursiveB base (m + n) inp o := by
  intro base m
  induction m with
  | zero =>
    intro n inp o
    simp only [Nat.zero_add, layoutRecursiveB]
  | succ m ih =>
    intro n inp o
    have hmn : m + 1 + n = (m + n) + 1 := by omega
    rw [hmn]
    cases hfind : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) with
    | none =>
      have hbase : layoutRecursiveB base n inp o = base inp o := by
        cases n with
        | zero => rfl
        | succ n =>
          unfold layoutRecursiveB
          simp only [hfind]
      unfold layoutRecursiveB
      simp only [hfind]
      exact hbase
    | some group =>
      unfold layoutRecursiveB
      simp only [hfind, ih]

def ExpandChildCallContextB (base : Input → Options → Except LayoutError FamilyResult)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult) :
    Prop :=
  WellFormed (inputModel inp o) ∧
    inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
    (parentSubInput inp group P titleLines child).boxes =
      (selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes ∧
    layoutRecursiveB base fuel (childSubInput inp group) (childSubOptions o group) = .ok child ∧
    layoutRecursiveB base fuel (parentSubInput inp group P titleLines child) o = .ok parent ∧
    expandChild P inp o group titleHeight parent child = .ok res

theorem expandChildCallContext_iff :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res ↔
        ExpandChildCallContextB layout fuel P inp o group titleLines titleHeight parent child
          res := by
  intro fuel P inp o group titleLines titleHeight parent child res
  unfold ExpandChildCallContext ExpandChildCallContextB
  simp only [layoutRecursive_eq_B]

end PipelineImpl
end Layered
end Elegant

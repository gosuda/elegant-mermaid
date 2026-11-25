import Elegant.Layered.RegionC8aSelectedGroupPairs
import Elegant.Layered.RegionFlatC8a

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

open RegionImpl

inductive R8a_SelectedAfterGroupsCase {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {g b : Box} (pair : R8a_SelectedPair execution g b) : Prop
  | groupPlain (hb : (pair.uNode.border = -2 ∧ pair.wNode.border = 0) ∨
      (pair.uNode.border = 0 ∧ pair.wNode.border = -2))
  | demotedCrossParent (hg : pair.uNode.border = 0) (hb : pair.wNode.border = 0)
      (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == pair.sourceGroup.id) = true)
      (hrank : (rk pair.selected.run.proper.rank pair.u).toNat =
        (rk pair.selected.run.proper.rank pair.w).toNat)
      (hparent : pair.sourceGroup.parent ≠ pair.sourcePeer.parent)

def R8a_SelectedAfterGroupsClearance {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (g b : Box) (pair : R8a_SelectedPair execution g b), R8a_SelectedAfterGroupsCase pair →
    R8a_OverlapRowsXGap
      (frameRect execution.params pair.selected.cg pair.selected.run pair.u)
      (frameRect execution.params pair.selected.cg pair.selected.run pair.w)

theorem r8a_selectedClearance_iff_afterGroups {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
    R8a_SelectedClearance execution ↔ R8a_SelectedAfterGroupsClearance execution := by
  constructor
  · intro h g b pair hcase
    cases hcase with
    | groupPlain hb => exact h g b pair (.groupPlain hb)
    | demotedCrossParent hg hb hfixed hrank hparent =>
      exact h g b pair (.demotedCrossParent hg hb hfixed hrank hparent)
  · intro h g b pair hcase
    cases hcase with
    | groups hg hb => exact r8a_selected_groups_xgap hwf hfp pair hg hb
    | groupPlain hb => exact h g b pair (.groupPlain hb)
    | demotedCrossParent hg hb hfixed hrank hparent =>
      exact h g b pair (.demotedCrossParent hg hb hfixed hrank hparent)

def R8a_ReindexedSelectedAfterGroupsClearance (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
    ∀ execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res,
      R8a_SelectedAfterGroupsClearance execution

theorem r8a_reindexedSelectedClearance_iff_afterGroups (exactIds : List String)
    (idSets : List (String × List String)) :
    R8a_ReindexedSelectedClearance exactIds idSets ↔
      R8a_ReindexedSelectedAfterGroupsClearance exactIds idSets := by
  constructor
  · intro h inp o res hwf hfp hok execution
    exact (r8a_selectedClearance_iff_afterGroups execution hwf hfp).mp
      (h inp o res hwf hfp hok execution)
  · intro h inp o res hwf hfp hok execution
    exact (r8a_selectedClearance_iff_afterGroups execution hwf hfp).mpr
      (h inp o res hwf hfp hok execution)

theorem flatC8aB_layoutRIds_reindex_iff_selectedAfterGroups (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC8aB (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) ↔
      R8a_ReindexedSelectedAfterGroupsClearance exactIds idSets :=
  (flatC8aB_layoutRIds_reindex_iff_selected exactIds idSets).trans
    (r8a_reindexedSelectedClearance_iff_afterGroups exactIds idSets)

end Elegant.Layered.PipelineImpl

import Elegant.Layered.RegionC8aGroupsCutover
import Elegant.Layered.RegionC8aGroupPlain

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

open RegionImpl

theorem r8a_selectedAfterGroupsClearance_holds {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
    R8a_SelectedAfterGroupsClearance execution := by
  intro g b pair hcase
  cases hcase with
  | groupPlain hb => exact r8a_selected_group_plain_xgap hwf hfp pair hb
  | demotedCrossParent hg hb hfixed hrank hparent =>
    exact r8a_selected_demoted_cross_parent hwf hfp pair hg hb hfixed hrank hparent

theorem flatC8aB_layoutRIds_reindex_closed (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC8aB (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) := by
  apply (flatC8aB_layoutRIds_reindex_iff_selectedAfterGroups exactIds idSets).mpr
  intro inp o res hwf hfp _hok execution
  exact r8a_selectedAfterGroupsClearance_holds execution hwf hfp

end Elegant.Layered.PipelineImpl

#print axioms Elegant.Layered.PipelineImpl.r8a_selectedAfterGroupsClearance_holds
#print axioms Elegant.Layered.PipelineImpl.flatC8aB_layoutRIds_reindex_closed

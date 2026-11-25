import Elegant.Layered.ExactNonfwdHullFactsProof
import Elegant.Layered.ExactNonforwardAncestorRightProof
import Elegant.Layered.ExactNonforwardForeignHullProof
import Elegant.Layered.ExactNonforwardPlainAncestorProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Every compared group frame either misses the loop footprint or strictly
contains it on an admitted exact candidate run. -/
theorem exactNonforward_groupHullExtW (exactIds : List String) :
    XNonfwd_GroupHullExtW exactIds := by
  apply xnonfwd_groupHullExtW_closed exactIds
  unfold XNonfwd_HullRemW
  refine ⟨?_, ?_, ?_⟩
  · intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
      hcomp hcg hrun hloop _hpos _hne owner hplain howner group hgroup hgroupBorder
      hancestor _hcontained
    subst hcg
    exact exactNonforwardPlainAncestor_strict execution hwf hfp hcomp hrun
      howner hplain hgroup hgroupBorder hancestor hloop
  · intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
      hcomp hcg hrun hloop _hpos hne owner howner group hgroup hgroupBorder hnotAncestor
    subst hcg
    by_cases hdescendant : owner.decl ∈ group.clusterPath
    · exact exactNonforwardHull_nested_disjointW execution hwf hfp hcomp hrun
        hloop howner hgroup hgroupBorder hne.symm hdescendant
    · exact exactNonforwardForeignHull_disjointW execution hwf hfp hcomp hrun
        hloop howner hgroup hgroupBorder hnotAncestor hdescendant
  · intro inp o res execution hwf hfp comp candidate run orderOptions cg t pos
      hcomp hcg hrun hloop _hpos hne owner hnotPlain howner group hgroup hgroupBorder hancestor
    subst hcg
    rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq howner).1 with
      hplain | htop | hbottom
    · exact (hnotPlain hplain).elim
    · exact exactNonforwardHull_group_ancestor_strict execution hwf hfp hcomp hrun
        howner hgroup htop hgroupBorder hne.symm hancestor hloop
    · exact (exactBottomNoLoopX execution comp candidate run orderOptions hcomp _ rfl
        hrun t owner howner hbottom hloop).elim

end Elegant.Layered.PipelineImpl

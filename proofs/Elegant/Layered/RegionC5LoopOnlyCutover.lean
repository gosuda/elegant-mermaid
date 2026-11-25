import Elegant.Layered.RegionC5SelectedReduction
import Elegant.Layered.RegionC5MixedFallback
import Lean

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

open RegionImpl

def R_ActiveBoundarySelectedNonexactLoopResidual (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ¬ R_AllComponentsFallbackR execution →
    ∀ out ∈ res.scene.routes,
      (out.fromId = out.toId ∧ R5_SelectedLoopR execution out false ∧
        ¬ R5_SelectedLoopR execution out true) →
      EmittedC5Boundary res.scene out

theorem r_activeBoundaryR_iff_selectedNonexactLoopResidual (exactIds : List String)
    (idSets : List (String × List String)) :
    R_ActiveBoundaryR exactIds idSets ↔
      R_ActiveBoundarySelectedNonexactLoopResidual exactIds idSets := by
  classical
  constructor
  · intro h inp o res execution hwf hfp hactive out hout _
    exact h execution hwf hfp hactive out hout
  · intro h inp o res execution hwf hfp hactive out hout
    change EmittedC5Boundary res.scene out
    by_cases hself : out.fromId = out.toId
    · by_cases hexact : R5_SelectedLoopR execution out true
      · exact regionC5SelectedExactLoop_boundary execution hwf hexact
      · obtain ⟨isExact, hselected⟩ := regionC5EmittedSelfLoop_selected execution hout hself
        have hnonexact : R5_SelectedLoopR execution out false := by
          cases isExact with
          | false => exact hselected
          | true => exact (hexact hselected).elim
        exact h execution hwf hfp hactive out hout ⟨hself, hnonexact, hexact⟩
    · exact regionC5OrdinaryRouteBoundary execution hwf hfp hout hself

theorem r_activeBoundaryR_reindex_iff_selectedNonexactLoopResidual (exactIds : List String)
    (idSets : List (String × List String)) :
    (∀ sub : Input, R_ActiveBoundaryR exactIds (reindexRegionSets idSets sub)) ↔
      (∀ sub : Input,
        R_ActiveBoundarySelectedNonexactLoopResidual exactIds (reindexRegionSets idSets sub)) := by
  constructor
  · intro h sub
    exact (r_activeBoundaryR_iff_selectedNonexactLoopResidual exactIds
      (reindexRegionSets idSets sub)).mp (h sub)
  · intro h sub
    exact (r_activeBoundaryR_iff_selectedNonexactLoopResidual exactIds
      (reindexRegionSets idSets sub)).mpr (h sub)

theorem flatC5B_layoutRIds_reindex_of_selectedNonexactLoopResidual (exactIds : List String)
    (idSets : List (String × List String))
    (h : ∀ sub : Input,
      R_ActiveBoundarySelectedNonexactLoopResidual exactIds (reindexRegionSets idSets sub)) :
    FlatC5B (fun sub o => layoutRIds exactIds (reindexRegionSets idSets sub) sub o) := by
  intro sub o res hwf hfp hok
  exact flatC5B_layoutRIds_activeOnly exactIds (reindexRegionSets idSets sub)
    ((r_activeBoundaryR_reindex_iff_selectedNonexactLoopResidual exactIds idSets).mpr h sub)
    hwf hfp hok

end Elegant.Layered.PipelineImpl

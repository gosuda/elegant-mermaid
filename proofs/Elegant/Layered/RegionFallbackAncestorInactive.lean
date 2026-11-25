import Elegant.Layered.RegionFallbackAncestorStrict
import Elegant.Layered.RegionBaseExecutedValidity

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- A selected component with no resolved allocation runs the exact candidate.
The selection equation is needed because a raw `componentRunR` with a `some`
spec keeps the region coordinate graph even if its resolution is `none`. -/
theorem componentRunR_exact_of_selected_inactive {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (e : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {spec' : Option RegionSpec} {cg : Graph} {run : Run}
    (hselected : R_ComponentSpecSelection e comp spec')
    (hrun : componentRunR e.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' e.graph comp candidate) e.measured
      (candidateOrder candidate) = .ok (cg, run))
    (hinactive : newComponentRegions spec' e.params inp
      (componentCandidateR spec' e.graph comp candidate) = .ok none) :
    cg = componentCandidate e.graph comp candidate ∧
      componentRunX e.params (exactDecls exactIds inp)
        (componentCandidate e.graph comp candidate) e.measured
        (candidateOrder candidate) = .ok run := by
  obtain ⟨regions, hregions, hspec⟩ := hselected
  have hresolved : newComponentRegions spec' e.params inp
      (componentCandidateR spec' e.graph comp candidate) = .ok regions := by
    rw [hspec]
    exact componentTrialR_selected_regions candidate hregions
  have hnone : regions = none := Except.ok.inj (hresolved.symm.trans hinactive)
  have hs : spec' = none := by simpa [hnone] using hspec
  rw [hs, componentCandidateR_none, componentRunR_none] at hrun
  cases hexact : componentRunX e.params (exactDecls exactIds inp)
      (componentCandidate e.graph comp candidate) e.measured (candidateOrder candidate) with
  | error err =>
    simp only [hexact, Except.map] at hrun
    cases hrun
  | ok actual =>
    simp only [hexact, Except.map] at hrun
    have hpair := Except.ok.inj hrun
    have hcg : cg = componentCandidate e.graph comp candidate := (congrArg Prod.fst hpair).symm
    have hr : run = actual := (congrArg Prod.snd hpair).symm
    subst run
    exact ⟨hcg, rfl⟩

/-- A selected inactive component's direct parent frame is strict, whether the
child is a plain node, a fixed/demoted group, or an ordinary group. -/
theorem regionSelectedInactiveFrameStrict {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {spec' : Option RegionSpec} {cg : Graph} {run : Run}
    (hselected : R_ComponentSpecSelection e comp spec')
    (hrun : componentRunR e.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' e.graph comp candidate) e.measured
      (candidateOrder candidate) = .ok (cg, run))
    (hinactive : newComponentRegions spec' e.params inp
      (componentCandidateR spec' e.graph comp candidate) = .ok none)
    {memberIndex key parentKey parentIndex : Nat} {child parent : ModelBox}
    (hkey : comp[memberIndex]? = some key) (hparentIndex : comp[parentIndex]? = some parentKey)
    (hchild : inp.boxes[key]? = some child) (hparent : inp.boxes[parentKey]? = some parent)
    (href : child.parent = parent.id) (hne : child.parent ≠ "") :
    (frameRect e.params cg run parentIndex).StrictInside
      (frameRect e.params cg run memberIndex) := by
  obtain ⟨rfl, hexact⟩ := componentRunR_exact_of_selected_inactive e hselected hrun hinactive
  let phases : ExactFramePrefix exactIds inp o :=
    { params := e.params
      lines := e.lines
      measured := e.measured
      graph0 := e.graph0
      graph := e.graph
      checked := e.checked
      lines_length := by
        have h := (mapM_getElem? _ _ _ e.lines_eq).1
        simpa only [List.length_zipIdx] using h
      graph0_eq := e.graph0_eq
      graph_eq := e.graph_eq }
  exact exactComponentDirectFrameStrict phases hwf hfp hcomp hexact hkey hparentIndex
    hchild hparent href hne

end Elegant.Layered.PipelineImpl


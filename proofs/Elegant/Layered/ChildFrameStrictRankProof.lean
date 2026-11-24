import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.DummyChainRankProof
import Elegant.Layered.BottomSyntheticRankProof
import Elegant.Layered.BottomNestedRankProof
import Elegant.Layered.GroupBottomBoundaryProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Executed top rank residual for a child group: every executed proper node
whose cluster path contains the child declaration ranks at or below the child
top marker. Discharges `ChildTopRankLe` via the closed
`groupTopSubtreeRankProper'`. -/
theorem childTopRankLe_executed {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {childIndex : Nat} {child : Node}
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2) :
    ChildTopRankLe (componentCandidate execution.graph comp candidate) run childIndex := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  intro q hq hcontains
  have hqget : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  have hi : q.2 < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hqget).1
  have hvcg : childIndex < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hchild).1
  have hchildGet : (componentCandidate execution.graph comp candidate).nodes.getD childIndex default = child := by
    simp only [List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  have hdeclEq : ((componentCandidate execution.graph comp candidate).nodes.getD childIndex default).decl = child.decl := by
    rw [hchildGet]
  have hget : run.proper.nodes.getD q.2 default = q.1 := by
    simp only [List.getD_eq_getElem?_getD, hqget, Option.getD_some]
  have hcontains' : (run.proper.nodes.getD q.2 default).node.clusterPath.contains child.decl = true := by
    rw [hget]
    have h := hcontains
    rw [hdeclEq] at h
    exact h
  exact groupTopSubtreeRankProper' execution.graph_eq hlines hwf hframed hcomp hrun
    hchild hchildGroup hvcg hi hcontains'

/-- Executed bottom rank residual for a child group: every executed proper node
whose cluster path contains the child declaration ranks (coordinate rank) at
or below the child's bottom marker. Discharges `ChildBottomRankLe` via the
closed `bottomMemberRankLe` with the proved synthetic and nested seams. -/
theorem childBottomRankLe_executed {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {childIndex : Nat} {child : Node}
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2) :
    ChildBottomRankLe (componentCandidate execution.graph comp candidate) run childIndex := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hchildGet : (componentCandidate execution.graph comp candidate).nodes.getD childIndex default = child := by
    simp only [List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  have hdeclEq : ((componentCandidate execution.graph comp candidate).nodes.getD childIndex default).decl = child.decl := by
    rw [hchildGet]
  intro cb hfind q hq hcontains
  have hfind' : ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find?
      fun entry => entry.1.border == 2 && entry.1.decl == child.decl) = some cb := by
    rw [hdeclEq] at hfind
    exact hfind
  have hcond := List.find?_some hfind'
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  obtain ⟨hbordCb, hdeclCb⟩ := hcond
  have hmem : cb ∈ (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
    List.mem_of_find?_eq_some hfind'
  have hvGet : (componentCandidate execution.graph comp candidate).nodes[cb.2]? = some cb.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hsynth : ∀ (P : Params) (graph : Graph), BottomSyntheticRankLe P graph :=
    bottomSyntheticRankLe bottomDummyRankLe
  have hnest : ∀ (P : Params) (graph : Graph), BottomNestedBottomRankLe P graph :=
    bottomNestedBottomRankLe
  exact bottomMemberRankLe execution.graph_eq hlines hwf hframed hcomp hrun
    hvGet hchild hbordCb hchildGroup hdeclCb hsynth hnest q hq hcontains

/-- Child group frame strictness with no rank residual: the child frame lies
strictly inside its parent frame. Same binders as
`SceneExecution.component_child_frame_strictInside'` minus `htop`/`hbot`, plus
the global `framedParents` admission the closed rank seams require. -/
theorem SceneExecution.component_child_frame_strictInside'' {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).StrictInside
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex) :=
  execution.component_child_frame_strictInside' hwf hcomp hrun hparent hparentGroup
    hchild hchildGroup hparentBox hchildBox hparentRef hne
    (childTopRankLe_executed execution hwf hframed hcomp hrun hchild hchildGroup)
    (childBottomRankLe_executed execution hwf hframed hcomp hrun hchild hchildGroup)

end Elegant.Layered.PipelineImpl

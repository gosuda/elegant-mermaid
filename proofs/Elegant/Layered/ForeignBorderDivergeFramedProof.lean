import Elegant.Layered.DivergeSeedExecutedProof
import Elegant.Layered.ForeignBorderDivergeStableProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Divergent side markers preserve their relative order in the returned layers
of a successful framed run without requiring agreement during sweeps.
Unframed runs, including paths through demoted ancestors, are not covered. -/
theorem foreignBorderDivergeStableFramed_holds {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph) (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {opts : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels opts = .ok run) :
    ∀ {l1 l2 : List Nat}, l1 ∈ run.layers → l2 ∈ run.layers →
    ∀ {a b a' b' : Nat} {na nb na' nb' : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      run.coordinateProper.nodes[a']? = some na' →
      run.coordinateProper.nodes[b']? = some nb' →
      (na'.node.border = -1 ∨ na'.node.border = 1) →
      (nb'.node.border = -1 ∨ nb'.node.border = 1) →
      na.node.clusterPath = na'.node.clusterPath →
      nb.node.clusterPath = nb'.node.clusterPath →
      Divergent na.node.clusterPath nb.node.clusterPath →
      ∀ {i j i' j' : Nat}, l1[i]? = some a → l1[j]? = some b →
        l2[i']? = some a' → l2[j']? = some b' →
        (i < j ↔ i' < j') := by
  intro l1 l2 hl1 hl2 a b a' b' na nb na' nb' hna hnb ha hb hna' hnb' ha' hb'
    hpathA hpathB hdiv i j i' j' hi hj hi' hj'
  refine foreignBorderDivergeStableSeparated_holds hgraph hcomp hrun hl1 hl2
    hna hnb ha hb hna' hnb' ha' hb' hpathA hpathB hdiv ?_ hi hj hi' hj'
  intro pref A B tailA tailB hA hB _
  exact componentRun_framed_marker_heads hgraph hlines hwf hframed hcomp hrun hna hnb ha hb hA hB

theorem foreignBorderDivergeStable_framed : ForeignBorderDivergeStable := by
  intro P inp o lines graph hgraph hlines hwf hframed comp hcomp candidate run labels opts hrun
  exact @foreignBorderDivergeStableFramed_holds P inp o lines graph hgraph hlines hwf hframed
    comp hcomp candidate run labels opts hrun

end Elegant.Layered.PipelineImpl

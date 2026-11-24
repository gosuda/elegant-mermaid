import Elegant.Layered.DivergeExecutedReplayProof
import Elegant.Layered.DivergeNormaliseAgreeProof
import Elegant.Layered.DivergeSeedExecutedProof
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem componentRun_divergeChainAgree {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph) (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {opts : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels opts = .ok run)
    (hsweep : ∀ (sweep : Nat) {L : List (List Nat)}, OrderImpl.Layering run.coordinateProper L →
      OrderImpl.LayersContiguous run.coordinateProper L → DivergeChainAgree run.coordinateProper L →
      DivergeChainAgree run.coordinateProper
        (OrderImpl.sweepLayers run.coordinateProper sweep L opts.key)) :
    DivergeChainAgree run.coordinateProper run.layers := by
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _⟩ := componentRun_spec hrun
  have hseed := divergeSeedExecuted_holds hgraph hlines hwf hframed hcomp hrun
  rw [← hlayers]
  exact orderWithBudget_divergeChainAgree (ord := ord) horder hseed hsweep
    (fun {L} hL ha => divergeChainAgree_transpose (L := L) hL ha)
    (fun {L} hL hc ha => divergeChainAgree_siblingNormalise (Y := L) hL hc ha)

end Elegant.Layered.PipelineImpl

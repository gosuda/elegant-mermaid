import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.CgShape
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactDivergeStableBridgeProof
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.Compound
import Elegant.Layered.Pipeline
import Elegant.SequencePlan

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Bottom conjunct of `XLEG_GroupMarkerOrder` for an executed exact run:
no border-`2` candidate node owns a self-loop edge. Derived from the
generalized `resid_bottomLoopEmpty` plus `measuredGraph_prepared_source`
raw border-zero classification, with no fixed/nonfixed case split. -/
theorem exactBottomNoLoopX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run) (orderOptions : OrderOptions)
    (hcomp : comp ∈ components execution.graph)
    (cg : Graph) (hcg : cg = componentCandidate execution.graph comp candidate)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured orderOptions = .ok run) :
    (∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt → nt.border = 2 →
      ¬ ∃ e_ ∈ cg.edges, e_.tail = t ∧ e_.head = t) := by
  intro t nt hnt hb2
  subst hcg
  have hnodes : (componentCandidate execution.graph comp candidate).nodes =
      comp.map (fun source => execution.graph.nodes.getD source default) := by
    rw [componentCandidate_nodes execution.graph comp candidate]
    rfl
  obtain ⟨j, hj, hjRec⟩ : ∃ j, comp[t]? = some j ∧
      execution.graph.nodes.getD j default = nt := by
    rw [hnodes, List.getElem?_map] at hnt
    obtain ⟨j, hj, hfj⟩ := Option.map_eq_some_iff.mp hnt
    exact ⟨j, hj, hfj⟩
  obtain ⟨hvt, hjVal⟩ := List.getElem?_eq_some_iff.mp hj
  have hjLenG : j < execution.graph.nodes.length := by
    apply Classical.byContradiction
    intro hcon
    have hnone : execution.graph.nodes[j]? = none := List.getElem?_eq_none (by omega)
    have hgetd : execution.graph.nodes.getD j default = default := by
      rw [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    rw [← hjRec, hgetd] at hb2
    have h0 : (default : Node).border = 0 := rfl
    omega
  have hjSome : execution.graph.nodes[j]? = some nt := by
    have h1 : execution.graph.nodes[j]? = some (execution.graph.nodes[j]'hjLenG) :=
      List.getElem?_eq_getElem hjLenG
    have h2 : execution.graph.nodes.getD j default =
        execution.graph.nodes[j]'hjLenG := by
      simp only [List.getD_eq_getElem?_getD, h1, Option.getD_some]
    rw [← hjRec, h2]
    exact h1
  obtain ⟨nd0, hnd0, _hdecl, hbnd, _hpath⟩ :=
    xdb_exactGraph_key execution.graph_eq hjSome
  have hb0 : nd0.border = 2 := hbnd.symm.trans hb2
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        Sequence.mapM_ok_length _ _ _ h
      _ = inp.boxes.length := List.length_zipIdx
  obtain ⟨nodes0, edges0, titles0, hprepared, hlen0', hmeta⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  rw [hprepared, Compound.prepare_nodes] at hnd0
  change (Compound.markNodes _ _ _ nodes0)[j]? = some nd0 at hnd0
  have hraw0 : ∀ (i : Nat) (n : Node), nodes0[i]? = some n → n.border = 0 :=
    fun i n hi => (hmeta i n hi).2
  have hjge : inp.boxes.length ≤ j := by
    apply Classical.byContradiction
    intro hlt
    have hlt' : j < inp.boxes.length := Nat.not_le.mp hlt
    have hjlen : j < nodes0.length := by omega
    have hprefix := Compound.markNodes_getElem?_prefix_border _ _ _ nodes0
      hjlen hnd0
    have hnodej : nodes0[j]? = some (nodes0[j]'hjlen) :=
      List.getElem?_eq_getElem hjlen
    have hbj : (nodes0[j]'hjlen).border = 0 := hraw0 j (nodes0[j]'hjlen) hnodej
    rcases hprefix with htop | hsrc
    · omega
    · rw [hbj] at hsrc
      omega
  have hloopEmpty : loopEdges
      (componentCandidate execution.graph comp candidate).edges t = [] := by
    refine resid_bottomLoopEmpty execution.graph0_eq
      (exactGraph_edges execution.graph_eq) comp candidate t hcomp hvt ?_
    have hgetD : comp.getD t 0 = comp[t]'hvt := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvt,
        Option.getD_some]
    rw [hgetD, hjVal]
    exact hjge
  intro hex
  obtain ⟨e_, heMem, heTail, heHead⟩ := hex
  have heIn : e_ ∈ loopEdges
      (componentCandidate execution.graph comp candidate).edges t := by
    exact List.mem_filter.mpr ⟨heMem, by simp [heTail, heHead]⟩
  rw [hloopEmpty] at heIn
  exact absurd heIn (by simp)

end PipelineImpl
end Layered
end Elegant

import Elegant.Layered.ExactGroupLoopFixedLeafGapProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- A vertically overlapping plain candidate box has a horizontal gap from the
footprint of a group self-loop on a successful well-formed framed run. -/
theorem xlem_groupOverlapForeignGap_plain (exactIds : List String)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    {cg : Graph} {k : Nat} {e : Edge} {v : Nat} {target : Node}
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidate execution.graph comp candidate)
    (hrun : componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run)
    (hedge : cg.edges[k]? = some e) (hself : e.tail = e.head)
    (hbdr : (cg.nodes.getD e.tail default).border = -2)
    (htarget : cg.nodes[v]? = some target) (hplain : target.border = 0) :
    let foot := loopFootprintExt cg run execution.measured e.tail
    let box := RouteImpl.boxRect run.proper run.xs run.ys v
    max foot.y box.y < min (foot.y + foot.h) (box.y + box.h) →
    foot.x + foot.w ≤ box.x ∨ box.x + box.w ≤ foot.x := by
  subst cg
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp candidate
    hcomp (sceneExecutionX_edges_bounded execution) (List.mem_of_getElem? hedge)
  obtain ⟨owner, howner⟩ : ∃ owner,
      (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some owner :=
    ⟨_, List.getElem?_eq_getElem hbnd.1⟩
  have hgroup : owner.border = -2 := by
    simpa only [List.getD_eq_getElem?_getD, howner, Option.getD_some] using hbdr
  have hv := componentRunX_original_nodes_covered hrun v (List.getElem?_eq_some_iff.mp htarget).1
  have htargetBorder : ((componentCandidate execution.graph comp candidate).nodes.getD
      v default).border ≠ -2 := by
    simpa only [List.getD_eq_getElem?_getD, htarget, Option.getD_some, hplain] using
      (by decide : (0 : Int) ≠ -2)
  have hframe := plain_frame_eq_boxRect execution.params _ run v hv htargetBorder
  dsimp only
  intro hyov
  rw [← hframe] at hyov ⊢
  exact componentRunX_groupLoop_footprint_horizontal_gap execution hwf hfp hcomp hrun
    hedge hself howner hgroup htarget hplain hyov

end Elegant.Layered.PipelineImpl

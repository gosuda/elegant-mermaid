import Elegant.Layered.FamilyAssemblyB
import Elegant.Layered.BorderStraightExecuted
import Elegant.Kinds.FlowchartValid

set_option autoImplicit false
set_option warningAsError true


namespace Elegant.Layered.PipelineImpl

theorem layered_foreign_boxes_clear {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) : Validator.C8a res.scene.layoutDump := by
  obtain ⟨hwf, hrec⟩ := layoutFamily_success h
  rw [layoutRecursive_eq_B] at hrec
  exact layoutRecursiveB_c8a layout baseSeams_of_layered.flatC8a
    baseSeams_of_layered.subInputB baseSeams_of_layered.stepC8a
    (inp.boxes.length + 1) inp o res hwf (layoutFamily_framed_parents h) hrec

theorem layered_frame_clearance_of_fixed_fit {inp : Input} {o : Options} {res : FamilyResult}
    (hfit : InputFixedFit inp o) (h : layoutFamily inp o = .ok res) :
    Validator.C8 res.scene.layoutDump := by
  obtain ⟨hwf, hrec⟩ := layoutFamily_success h
  rw [layoutRecursive_eq_B] at hrec
  exact ⟨layered_foreign_boxes_clear h,
    layoutRecursiveB_c8b layout baseSeams_of_layered.flatC8b
      baseSeams_of_layered.canvasMargins baseSeams_of_layered.subInputB
      baseSeams_of_layered.stepC8b (inp.boxes.length + 1) inp o res hwf
      (layoutFamily_framed_parents h) hfit hrec⟩

theorem layered_frame_clearance_admitted {inp : Input} {o : Options} {res : FamilyResult}
    (h : admit inp (layoutFamily inp o) = .ok res) : Validator.C8 res.scene.layoutDump := by
  obtain ⟨hadm, hrun⟩ := admit_ok h
  exact layered_frame_clearance_of_fixed_fit (layeredAdmissibleB_fit hadm o) hrun

theorem border_chain_straight_in_executed_span {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph) (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {decl low high : Nat} {lowNode highNode : ProperNode}
    (hlow : run.proper.nodes[low]? = some lowNode)
    (hhigh : run.proper.nodes[high]? = some highNode)
    (hlowDecl : lowNode.node.clusterPath.contains decl = true)
    (hhighDecl : highNode.node.clusterPath.contains decl = true)
    (hspan : (rk run.proper.rank low).toNat ≤ (rk run.proper.rank high).toNat) :
    ∃ leftX rightX : Int,
      ∀ rank : Nat, (rk run.proper.rank low).toNat ≤ rank →
        rank ≤ (rk run.proper.rank high).toNat →
        ∃ (left right : Nat) (leftNode rightNode : ProperNode),
          run.coordinateProper.nodes[left]? = some leftNode ∧
          leftNode.node.border = -1 ∧ leftNode.node.clusterPath.getLast? = some decl ∧
          rk run.coordinateProper.rank left = (rank : Int) ∧
          run.coordinateProper.nodes[right]? = some rightNode ∧
          rightNode.node.border = 1 ∧ rightNode.node.clusterPath.getLast? = some decl ∧
          rk run.coordinateProper.rank right = (rank : Int) ∧
          run.coordinateXs[left]! = leftX ∧ run.coordinateXs[right]! = rightX := by
  obtain ⟨l₀, r₀, _, _, hl₀, hls₀, hld₀, _, hr₀, hrs₀, hrd₀, _⟩ :=
    bracketMarkersAtRank' hgraph hlines hwf hframed hcomp hrun
      (rk run.proper.rank low).toNat hlow hlowDecl (Nat.le_refl _) hhigh hhighDecl hspan
  refine ⟨run.coordinateXs[l₀]!, run.coordinateXs[r₀]!, ?_⟩
  intro rank hlo hhi
  obtain ⟨l, r, ln, rn, hl, hls, hld, hlrank, hr, hrs, hrd, hrrank⟩ :=
    bracketMarkersAtRank' hgraph hlines hwf hframed hcomp hrun rank
      hlow hlowDecl hlo hhigh hhighDecl hhi
  exact ⟨l, r, ln, rn, hl, hls, hld, hlrank, hr, hrs, hrd, hrrank,
    border_chain_straight_executed hgraph hlines hwf hframed hcomp hrun
      (Or.inl rfl) hl hl₀ hls hls₀ hld hld₀,
    border_chain_straight_executed hgraph hlines hwf hframed hcomp hrun
      (Or.inr rfl) hr hr₀ hrs hrs₀ hrd hrd₀⟩

end Elegant.Layered.PipelineImpl

namespace Elegant.Kinds

theorem flowchart_layered_frame_clearance {m : Model} {res : Layered.FamilyResult}
    (h : Flowchart.layout m = .ok res) : Validator.C8 res.scene.layoutDump := by
  obtain ⟨raw, hadm, hrun, hdump⟩ := flowchart_layout_spec h
  rw [hdump]
  exact Layered.PipelineImpl.layered_frame_clearance_of_fixed_fit
    (Layered.layeredAdmissibleB_fit hadm m.options) hrun

end Elegant.Kinds

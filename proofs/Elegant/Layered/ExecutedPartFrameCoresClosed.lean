import Elegant.Layered.CaptionRunClearClosed
import Elegant.Layered.RouteRunClearClosed
import Elegant.Layered.DummyMarkerBracketProof
import Elegant.Layered.LoopFootprintGroupHullProof
import Elegant.Layered.RunLocalLoopFootprintProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Measured-only route transport: copy of `partRoute_of_run` with `labels` fixed to `execution.measured`, the only instantiation the pipeline performs (`execution_part_run` pins `measured` and `candidateOrder`). -/
private theorem partRoute_of_run_measured {inp : Input} {o : Options} {res : FamilyResult} (execution : SceneExecution inp o res) (hres : ∀ (comp : List Nat), comp ∈ components execution.graph → ∀ (candidate : Nat) (run : Run) (orderOptions : OrderOptions), componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run → RouteRunClear execution.params (componentCandidate execution.graph comp candidate) run execution.measured) : ∀ part ∈ execution.componentsAcc.parts, PartRouteLabelFrameClear inp part := by
  intro part hpart index rect pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨cindex, run, loops, _area, hcomp, hrun, heq⟩ := execution_part_run execution hpart
  have eL : part.2.labels = (placedLabels execution.params (componentCandidate execution.graph part.1 cindex) run execution.measured).map (fun q => (q.1, shiftRect (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 cindex) run execution.measured loops).minX) (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 cindex) run execution.measured loops).minY) q.2)) := by
    have h1 : part.2.labels = (placeComponent execution.params (componentCandidate execution.graph part.1 cindex) run 0 execution.measured loops).labels := by
      rw [heq]
    rw [h1]
    exact placeComponent_labels_eq
  have eR' : part.2.rects = (placeComponent execution.params (componentCandidate execution.graph part.1 cindex) run 0 execution.measured loops).rects := by
    rw [heq]
  rw [eL] at hmem
  obtain ⟨⟨k0, rect0⟩, h0mem, h0eq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at h0eq
  obtain ⟨rfl, hrect0⟩ := h0eq
  have hlen : part.2.rects.length = (componentCandidate execution.graph part.1 cindex).nodes.length := by
    rw [eR']
    exact placeComponent_rects_length _ _ _ _ _
  have hlt : pos < (componentCandidate execution.graph part.1 cindex).nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1
    omega
  have hframe := placeComponent_rect_get execution.params (componentCandidate execution.graph part.1 cindex) run execution.measured loops hlt
  rw [eR'] at hrect
  rw [hframe] at hrect
  have hg0 : shiftRect (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 cindex) run execution.measured loops).minX) (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 cindex) run execution.measured loops).minY) (frameRect execution.params (componentCandidate execution.graph part.1 cindex) run pos) = g := Option.some.inj hrect
  have hclear := hres part.1 hcomp cindex run (candidateOrder cindex) hrun k0 rect0 h0mem pos _ hlt rfl
  rw [←hg0, ←hrect0]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)

/-- Executed part-frame cores from the narrowed seams: the caption half closes over `hx` alone (`captionHalf_closed`), the route half closes over `hx`, the run-local loop footprint derived from the two footprint seams, the hull clearance derived from `hx` and the two cover facts, and the dummy bracket (`dummyMarkerBracket_of_run`). Both transports only ever instantiate `execution.measured`, so the measured route/caption halves suffice for the full `ExecutedPartFrameCores` conclusion. -/
theorem executedPartFrameCores_closed {inp : Input} {o : Options} {res : FamilyResult} (execution : SceneExecution inp o res) (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true) (hx : ForeignBorderChainXAligned) (htop : LoopFootprintTopSeparation inp o res) (hbeyond : LoopFootprintBeyondProper inp o res) (hright : ∀ (comp : List Nat), comp ∈ components execution.graph → ∀ (candidate : Nat) (run : Run) (orderOptions : OrderOptions), componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run → LoopHullRightCover execution.params (componentCandidate execution.graph comp candidate) run execution.measured) (hrightN : ∀ (comp : List Nat), comp ∈ components execution.graph → ∀ (candidate : Nat) (run : Run) (orderOptions : OrderOptions), componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run → LoopHullRightNeighborCover execution.params (componentCandidate execution.graph comp candidate) run execution.measured) : ExecutedPartFrameCores execution := by
  have hfoot : RunLocalLoopFootprint inp o res := runLocalLoopFootprint_executed hwf hframed htop hbeyond
  have hcap := captionHalf_closed execution hwf hframed hx
  have hroute : ∀ (comp : List Nat), comp ∈ components execution.graph → ∀ (candidate : Nat) (run : Run) (orderOptions : OrderOptions), componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run → RouteRunClear execution.params (componentCandidate execution.graph comp candidate) run execution.measured := by
    intro comp hcomp candidate run orderOptions hrun
    exact routeRunClear_closed execution hwf hframed hcomp hrun hx hfoot htop hbeyond (loopFootprintGroupHullClear_of_run execution hwf hframed hcomp hrun hx (hright comp hcomp candidate run orderOptions hrun) (hrightN comp hcomp candidate run orderOptions hrun)) (dummyMarkerBracket_of_run execution hwf hframed hcomp hrun hx)
  intro part hpart
  exact ⟨partRoute_of_run_measured execution hroute part hpart, partCaption_of_run_measured execution hcap part hpart⟩

end Elegant.Layered.PipelineImpl

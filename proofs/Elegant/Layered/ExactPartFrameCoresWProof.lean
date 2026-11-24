import Elegant.Layered.ExactPartFrameCoresProof
import Elegant.Layered.ExactCaptionRunClearWProof
import Elegant.Layered.ExactForwardClearWProof
import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.RouteRunClearClosed

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact part-frame cores, per-execution form (`X_ExecutedPartFrameCoresB8W`)

Packet 3 of `local://exact-global-premise-audit.md` (conversion plan, Packet 3).
W replay of `X_executedPartFrameCores_holds`
(`ExactPartFrameCoresProof.lean:316`) over the W run residuals. Supersedes the
non-W `X_executedPartFrameCores_holds` (whose premises `XF_CaptionRunClearX` /
`XF_RouteRunClearX` quantify over every execution with no admission guard).
Premise classification (each kept premise is a public named def over runs):
- `XF_CaptionRunClearXW` (Packet 2, imported) and `XF_RouteRunClearXW`
  (below) feed `X_executedPartFrameCoresW_holds`; each is run-level,
  strictly narrower than the part-level goal.
- `XF_RouteForwardClearXW` (Packet 1, imported) and the per-run
  `RouteNonforwardLabelClear` callback feed `XF_routeRunClearXW_holds`.
  Both use local admission premises and cover complementary edge cases.

Probe evidence: `proofs/wip/Probe/ExactPartFrameCoresTProbe.lean` evaluates the
non-W cores and both run premises on executed inputs (flat, nested, sane
fixed, wider-than-slot fixed, degenerate fixed). The probe samples those
inputs; the W nonforward callback is scoped to admitted executions. No
statement here takes a global admission premise. -/

/-- Exact mirror of the run-level route residual `RouteRunClear`, W form: the
`XF_RouteRunClearX` conclusion (`ExactPartFrameCoresProof.lean:92`) with local
admission premises directly after the execution binder. -/
def XF_RouteRunClearXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    RouteRunClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured

/-- X core residual, W form: mirror of `X_ExecutedPartFrameCoresB8`
(`ExactFlatC8b.lean:42`) with local admission premises directly after the
execution binder. -/
def X_ExecutedPartFrameCoresB8W (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true),
    ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part
/-- Exact route-run clearance combines W forward clearance with the self-loop
and reversed-label cases of `RouteNonforwardLabelClear` for the same admitted
execution. -/
theorem XF_routeRunClearXW_holds (exactIds : List String)
    (hFwdW : XF_RouteForwardClearXW exactIds)
    (hRrNonfwdX : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      (_ : WellFormed (inputModel inp o)) (_ : framedParents inp = true)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate)
        execution.measured orderOptions = .ok run →
      RouteNonforwardLabelClear execution.params
        (componentCandidate execution.graph comp candidate) run
        execution.measured) :
    XF_RouteRunClearXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  have hfwd := hFwdW execution hwf hfp hcomp hrun
  have hnon := hRrNonfwdX execution hwf hfp hcomp hrun
  have hinlined : RouteRunClearInlined execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured := by
    intro k rect hmem pos hpos
    obtain ⟨l₀, edge, e, hmem0, hidx, hfind, he, hdecl⟩ :=
      placed_mem_unpack hmem
    by_cases hfw : e.tail = e.head ∨ e.reversed = true
    · exact hnon k rect l₀ edge e hmem hmem0 hidx he hdecl hfw pos hpos
    · have hne : e.tail ≠ e.head := fun h => hfw (Or.inl h)
      have hnr : e.reversed = false := by
        cases heq : e.reversed with
        | true =>
          have hfalse : False := hfw (Or.inr heq)
          exact False.elim hfalse
        | false => rfl
      exact hfwd k rect l₀ edge e hmem hmem0 hidx he hdecl hne hnr pos hpos
  exact routeRunClear_of_inlined hinlined

/-! ## Exact placement shift equations (copies, prefix `xpfcw_`) -/

/-- Exact titles equation: copy of `xfpc_placeExact_titles_eq`. -/
private theorem xpfcw_placeExact_titles_eq (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).titles =
      (componentTitles P cg run).map (fun q =>
        (q.1, shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
          (-(placeBoundsX P cg run labels loops).minY) q.2)) := by
  unfold placeComponentExact placeBoundsX
  rfl

/-- Exact rect-count equation: copy of `xfpc_placeExact_rects_length`. -/
private theorem xpfcw_placeExact_rects_length (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).rects.length = cg.nodes.length := by
  unfold placeComponentExact
  dsimp only
  simp only [List.length_map, List.length_range]

/-- Exact rect-lookup equation: copy of `xfpc_placeExact_rect_get`. -/
private theorem xpfcw_placeExact_rect_get (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run 0 labels loops).rects[i]? =
      some (shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Exact labels equation: copy of `xfpc_placeExact_labels_eq`. -/
private theorem xpfcw_placeExact_labels_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} :
    (placeComponentExact P cg run 0 labels loops).labels =
      (placedLabels P cg run labels).map (fun q =>
        (q.1, shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
          (-(placeBoundsX P cg run labels loops).minY) q.2)) := rfl

/-- Exact executed parts carry their component and exact run: copy of
`xfpc_execution_part_runX`. -/
private theorem xpfcw_execution_part_runX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {part : List Nat × Part}
    (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ (index : Nat) (run : Run) (loops : List (Nat × LoopPlacement)) (area : Int),
      part.1 ∈ components execution.graph ∧
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph part.1 index) execution.measured
        (candidateOrder index) = .ok run ∧
      part.2 = { placeComponentExact execution.params
        (componentCandidate execution.graph part.1 index) run 0
        execution.measured loops with area := area } := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default, Array.replicate inp.routes.length [], Array.replicate inp.labels.length default, false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hm, hall⟩ := actual_components_parts_geometryX hempty execution.components_eq
  obtain ⟨index, _chosen, run, loops, area, _hi, _hc, _hv, hrun, _hl, heq⟩ :=
    hall part hpart
  refine ⟨index, run, loops, area, ?_, hrun, heq⟩
  rw [← hm]
  exact List.mem_map_of_mem hpart

/-- Exact caption transport, W form: copy of `xfpc_partCaption_of_runX` over
the W run residual (local admission threaded into `hres`). -/
private theorem xpfcw_partCaption_of_runX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hres : XF_CaptionRunClearXW exactIds) :
    ∀ part ∈ execution.componentsAcc.parts,
      PartCaptionFrameClear execution.params inp o execution.lines part := by
  intro part hpart i stored pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨index, run, loops, _area, hcomp, hrun, heq⟩ :=
    xpfcw_execution_part_runX execution hpart
  have eT : part.2.titles =
      (componentTitles execution.params
        (componentCandidate execution.graph part.1 index) run).map (fun q =>
        (q.1, shiftRect
          (0 - (placeBoundsX execution.params
            (componentCandidate execution.graph part.1 index) run
            execution.measured loops).minX)
          (-(placeBoundsX execution.params
            (componentCandidate execution.graph part.1 index) run
            execution.measured loops).minY) q.2)) := by
    have h1 : part.2.titles =
        (placeComponentExact execution.params
          (componentCandidate execution.graph part.1 index) run 0
          execution.measured loops).titles := by
      rw [heq]
    rw [h1]
    exact xpfcw_placeExact_titles_eq _ _ _ _ _
  have eR' : part.2.rects = (placeComponentExact execution.params
      (componentCandidate execution.graph part.1 index) run 0
      execution.measured loops).rects := by
    rw [heq]
  rw [eT] at hmem
  obtain ⟨⟨i0, stored0⟩, h0mem, h0eq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at h0eq
  obtain ⟨rfl, hstored⟩ := h0eq
  have hlen : part.2.rects.length =
      (componentCandidate execution.graph part.1 index).nodes.length := by
    rw [eR']
    exact xpfcw_placeExact_rects_length _ _ _ _ _
  have hlt : pos <
      (componentCandidate execution.graph part.1 index).nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1
    omega
  have hframe := xpfcw_placeExact_rect_get execution.params
    (componentCandidate execution.graph part.1 index) run execution.measured
    loops hlt
  rw [eR'] at hrect
  rw [hframe] at hrect
  have hg0 : shiftRect
      (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run pos) = g :=
    Option.some.inj hrect
  obtain ⟨top, htop, hborder, htitleIdx, _hw, _hh⟩ :=
    componentTitles_dimension_source execution.params
      (componentCandidate execution.graph part.1 index) run h0mem
  have hidx : i0 = top.2 := htitleIdx
  have hnode : (componentCandidate execution.graph part.1 index).nodes[i0]? =
      some top.1 := by
    rw [hidx]
    exact List.mem_zipIdx_iff_getElem?.mp htop
  have hclear := hres execution hwf hfp hcomp hrun i0 stored0 top.1 h0mem hnode hborder
    pos _ hlt rfl
  dsimp only
  rw [←hg0, ←hstored, captionResize_shift_comm]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)

/-- Exact route transport, W form: copy of `xfpc_partRoute_of_runX` over the
W run residual (local admission threaded into `hres`). -/
private theorem xpfcw_partRoute_of_runX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hres : XF_RouteRunClearXW exactIds) :
    ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part := by
  intro part hpart index rect pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨cindex, run, loops, _area, hcomp, hrun, heq⟩ :=
    xpfcw_execution_part_runX execution hpart
  have eL : part.2.labels =
      (placedLabels execution.params
        (componentCandidate execution.graph part.1 cindex) run
        execution.measured).map (fun q =>
        (q.1, shiftRect
          (0 - (placeBoundsX execution.params
            (componentCandidate execution.graph part.1 cindex) run
            execution.measured loops).minX)
          (-(placeBoundsX execution.params
            (componentCandidate execution.graph part.1 cindex) run
            execution.measured loops).minY) q.2)) := by
    have h1 : part.2.labels =
        (placeComponentExact execution.params
          (componentCandidate execution.graph part.1 cindex) run 0
          execution.measured loops).labels := by
      rw [heq]
    rw [h1]
    exact xpfcw_placeExact_labels_eq
  have eR' : part.2.rects = (placeComponentExact execution.params
      (componentCandidate execution.graph part.1 cindex) run 0
      execution.measured loops).rects := by
    rw [heq]
  rw [eL] at hmem
  obtain ⟨⟨k0, rect0⟩, h0mem, h0eq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at h0eq
  obtain ⟨rfl, hrect0⟩ := h0eq
  have hlen : part.2.rects.length =
      (componentCandidate execution.graph part.1 cindex).nodes.length := by
    rw [eR']
    exact xpfcw_placeExact_rects_length _ _ _ _ _
  have hlt : pos <
      (componentCandidate execution.graph part.1 cindex).nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1
    omega
  have hframe := xpfcw_placeExact_rect_get execution.params
    (componentCandidate execution.graph part.1 cindex) run execution.measured
    loops hlt
  rw [eR'] at hrect
  rw [hframe] at hrect
  have hg0 : shiftRect
      (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 cindex) run
        execution.measured loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 cindex) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 cindex) run pos) = g :=
    Option.some.inj hrect
  have hclear := hres execution hwf hfp hcomp hrun k0 rect0 h0mem pos _ hlt rfl
  rw [←hg0, ←hrect0]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)

/-- Exact executed part-frame cores, W form: replay of
`X_executedPartFrameCores_holds` (`ExactPartFrameCoresProof.lean:316`) over
the W run residuals. Supersedes `X_executedPartFrameCores_holds`. -/
theorem X_executedPartFrameCoresW_holds (exactIds : List String)
    (hcap : XF_CaptionRunClearXW exactIds)
    (hroute : XF_RouteRunClearXW exactIds) :
    X_ExecutedPartFrameCoresB8W exactIds := by
  intro inp o res execution hwf hfp part hpart
  exact ⟨xpfcw_partRoute_of_runX execution hwf hfp hroute part hpart,
    xpfcw_partCaption_of_runX execution hwf hfp hcap part hpart⟩


end PipelineImpl
end Layered
end Elegant

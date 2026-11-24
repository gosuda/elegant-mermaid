import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.Pipeline
import Elegant.Layered.PartFrameCoresProof
import Elegant.Layered.PartCaptionRunClearProof
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.ExactFlatC8b
import Elegant.Layered.LabelsClearance
import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact part-frame cores (`X_ExecutedPartFrameCoresB8`)

Goal: `X_executedPartFrameCores_holds`, the exact-pipeline replay of the plain
closed theorem `executedPartFrameCores_closed`
(`ExecutedPartFrameCoresClosed.lean:43`), whose conclusion is the named open
seam `ExecutedPartFrameCores` consumed by `frameLabels_executed`
(`FrameLabelsProof.lean:647`) and whose exact mirror `X_ExecutedPartFrameCoresB8`
(`ExactFlatC8b.lean:42`) is the hypothesis `hcores` of `flatC8bB_layoutX`.

Seam-level facts the closed plain proof consumes, with disposition:

* `ForeignBorderChainXAligned` (`ForeignBorderSpansProof.lean:140`): exact port
  exists as `X_ForeignBorderChainXAligned` (`ExactFlatC7CaptionScope.lean:58`);
  discharged into the two `XF_` premises below.
* `LoopFootprintTopSeparation` (`LoopFootprintResidualProof.lean:60`) and its
  general-order alias `LoopFootprintTopSeparationG`
  (`LoopFootprintGeneralOrder.lean:66`): no exact port; into the premises.
* `LoopFootprintBeyondProper` (`LoopFootprintResidualProof.lean:80`) and
  `LoopFootprintBeyondProperG` (`LoopFootprintGeneralOrder.lean:73`): same.
* `LoopHullRightCover` / `LoopHullRightNeighborCover`
  (`LoopFootprintGroupHullProof.lean:56,69`): no exact port; into the premises.
* Derived facts `RunLocalLoopFootprint` (via `runLocalLoopFootprint_executed`,
  `RunLocalLoopFootprintProof.lean:87`), `LoopFootprintGroupHullClear` (via
  `loopFootprintGroupHullClear_of_run`, `LoopFootprintGroupHullProof.lean:1366`),
  `DummyMarkerBracket` (via `dummyMarkerBracket_of_run`,
  `DummyMarkerBracketProof.lean:186`): into the premises.
* Per-run `CaptionRunClear` (via `captionHalf_closed`,
  `CaptionRunClearClosed.lean:351`, from `captionRunClear_closed` at :303):
  stated as premise `XF_CaptionRunClearX` (plain original named in its doc).
* Per-run `RouteRunClear` (via `routeRunClear_closed`,
  `RouteRunClearClosed.lean:30`): stated as premise `XF_RouteRunClearX`.
* Transports `partRoute_of_run_measured` (`ExecutedPartFrameCoresClosed.lean:12`)
  and `partCaption_of_run_measured` (`CaptionRunClearClosed.lean:369`):
  replayed outright here as `xfpc_partRoute_of_runX` / `xfpc_partCaption_of_runX`
  (generic shelf geometry: the exact placement shifts titles, labels, and
  frames by the same translation, so the plain shift argument is size-free).
* `frameLabels_executed` itself is not consumed: assembly stops at the cores;
  the packed/fallback levels belong to `flatC8bB_layoutX`.

Rank-axis note for discharging the two premises later: frame cores are built
from border markers and title copies, which the exact size hook leaves alone
(`sizeProperPortsX` keeps dummy, non-zero-border, and exact nodes:
`ExactPipeline.lean:55`; key fields survive `exactGraph` by
`exactGraph_node_key`, `ExactFlatFacts.lean:158`, and the x-interval by
`X_ForeignBorderChainXAligned`), while the reserve stage shifts whole ranks
(`X_ReserveBands_holds`, `ExactFlatC2.lean:955`; pre-reserve bands `X_pre_band`,
`ExactFlatC2.lean:668`, private; final bands `componentRunX_node_band`,
`ComponentRunGenGeometry.lean:626`).
-/

/-- Exact mirror of the run-level caption residual `CaptionRunClear`
(`PartFrameCoresProof.lean:110`) over `componentRunX`: every installed title
caption of one exact run, resized by `transportCapSize`, either misses every
frame position or lies strictly inside it. Plain counterpart: the `hcap`
hypothesis of `partCaption_of_run_measured` (`CaptionRunClearClosed.lean:369`),
as closed by `captionHalf_closed` (`CaptionRunClearClosed.lean:351`). This is a
single per-run fact, strictly narrower than the per-part goal. -/
def XF_CaptionRunClearX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionRunClear execution.params
      (componentCandidate execution.graph comp candidate) run
      (transportCapSize execution.params o execution.lines comp)

/-- Exact mirror of the run-level route residual `RouteRunClear`
(`PartFrameCoresProof.lean:129`) over `componentRunX`: every placed route label
of one exact run either misses every frame position or lies strictly inside it.
Plain counterpart: the `hres` hypothesis of `partRoute_of_run_measured`
(`ExecutedPartFrameCoresClosed.lean:12`), as closed by `routeRunClear_closed`
(`RouteRunClearClosed.lean:30`). Single per-run fact, narrower than the goal. -/
def XF_RouteRunClearX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    RouteRunClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured

/-! ## Exact placement shift equations (copies of the `placeComponent` facts) -/

/-- Exact titles equation: copy of `placeComponent_titles_eq`
(`PartFrameCoresProof.lean:69`) for `placeComponentExact`. -/
private theorem xfpc_placeExact_titles_eq (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).titles =
      (componentTitles P cg run).map (fun q =>
        (q.1, shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
          (-(placeBoundsX P cg run labels loops).minY) q.2)) := by
  unfold placeComponentExact placeBoundsX
  rfl

/-- Exact rect-count equation: copy of `placeComponent_rects_length`
(`PartFrameCoresProof.lean:81`) for `placeComponentExact`. -/
private theorem xfpc_placeExact_rects_length (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).rects.length = cg.nodes.length := by
  unfold placeComponentExact
  dsimp only
  simp only [List.length_map, List.length_range]

/-- Exact rect-lookup equation: copy of `placeComponent_rect_get`
(`PartFrameCoresProof.lean:90`) for `placeComponentExact`. -/
private theorem xfpc_placeExact_rect_get (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run 0 labels loops).rects[i]? =
      some (shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Exact labels equation: copy of `placeComponent_labels_eq`
(`LabelRunBridgeFacts.lean:784`) for `placeComponentExact`. -/
private theorem xfpc_placeExact_labels_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} :
    (placeComponentExact P cg run 0 labels loops).labels =
      (placedLabels P cg run labels).map (fun q =>
        (q.1, shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
          (-(placeBoundsX P cg run labels loops).minY) q.2)) := rfl

/-! ## Exact executed-part bridge and transports -/

/-- Exact executed parts carry their component and exact run: copy of
`execution_part_run` (`LabelRunBridgeFacts.lean:316`) over
`actual_components_parts_geometryX` (`ExactFlatFacts.lean:1222`). -/
private theorem xfpc_execution_part_runX {exactIds : List String} {inp : Input}
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

/-- Exact caption transport: copy of `partCaption_of_run_measured`
(`CaptionRunClearClosed.lean:369`) over `SceneExecutionX`. -/
private theorem xfpc_partCaption_of_runX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hres : XF_CaptionRunClearX exactIds) :
    ∀ part ∈ execution.componentsAcc.parts,
      PartCaptionFrameClear execution.params inp o execution.lines part := by
  intro part hpart i stored pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨index, run, loops, _area, hcomp, hrun, heq⟩ :=
    xfpc_execution_part_runX execution hpart
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
    exact xfpc_placeExact_titles_eq _ _ _ _ _
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
    exact xfpc_placeExact_rects_length _ _ _ _ _
  have hlt : pos <
      (componentCandidate execution.graph part.1 index).nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1
    omega
  have hframe := xfpc_placeExact_rect_get execution.params
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
  have hclear := hres execution hcomp hrun i0 stored0 top.1 h0mem hnode hborder
    pos _ hlt rfl
  dsimp only
  rw [←hg0, ←hstored, captionResize_shift_comm]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)

/-- Exact route transport: copy of `partRoute_of_run_measured`
(`ExecutedPartFrameCoresClosed.lean:12`) over `SceneExecutionX`. -/
private theorem xfpc_partRoute_of_runX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hres : XF_RouteRunClearX exactIds) :
    ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part := by
  intro part hpart index rect pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨cindex, run, loops, _area, hcomp, hrun, heq⟩ :=
    xfpc_execution_part_runX execution hpart
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
    exact xfpc_placeExact_labels_eq
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
    exact xfpc_placeExact_rects_length _ _ _ _ _
  have hlt : pos <
      (componentCandidate execution.graph part.1 cindex).nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1
    omega
  have hframe := xfpc_placeExact_rect_get execution.params
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
  have hclear := hres execution hcomp hrun k0 rect0 h0mem pos _ hlt rfl
  rw [←hg0, ←hrect0]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)

/-- Exact executed part-frame cores from the two narrowed exact seams: replay
of `executedPartFrameCores_measured` (`CaptionRunClearClosed.lean:453`) and of
`executedPartFrameCores_closed` (`ExecutedPartFrameCoresClosed.lean:43`) over
`SceneExecutionX`. -/
theorem X_executedPartFrameCores_holds (exactIds : List String)
    (hcap : XF_CaptionRunClearX exactIds)
    (hroute : XF_RouteRunClearX exactIds) :
    X_ExecutedPartFrameCoresB8 exactIds := by
  intro inp o res execution part hpart
  exact ⟨xfpc_partRoute_of_runX execution hroute part hpart,
    xfpc_partCaption_of_runX execution hcap part hpart⟩

end PipelineImpl
end Layered
end Elegant

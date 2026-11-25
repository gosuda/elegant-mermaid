import Elegant.Layered.ExactPartFrameCoresProof
import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.RouteRunClearClosed
import Elegant.Layered.Pipeline
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.PartFrameCoresProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact route-run clearance (`XF_RouteRunClearX`)

Replay of `routeRunClear_closed` (`RouteRunClearClosed.lean:30`) over
`componentRunX`: every placed route label of one exact run clears every frame
position of its component. The plain `hres` hypothesis of
`partRoute_of_run_measured` (`ExecutedPartFrameCoresClosed.lean:12`) becomes
the conclusion `XF_RouteRunClearX` (`ExactPartFrameCoresProof.lean:92`).

Plain lemmas on the path that read the plain run spec, with exact replacements:
* `componentRun_spec` (rankCoords, proxyYs, dummy positions) replaced by
  `componentRunX_spec` (`ExactFlatFacts.lean:284`).
* rank band construction (`rankCoordsWith`) replaced by `X_pre_band`
  (`ExactFlatC2.lean:668`, private), `X_ReserveBands_holds`
  (`ExactFlatC2.lean:955`), `componentRunX_node_band`
  (`ComponentRunGenGeometry.lean:626`), and
  `componentRunX_positions_disjoint`
  (`ComponentRunGenGeometry.lean:527`).
* proxy dummy transport replaced by `X_coordinateGraphX_dummy_at`
  (`ExactFlatC7Forward.lean:31`, private) and `X_proper_to_coord_node`
  (`ExactFlatC7Forward.lean:173`, private), via `exactGraph_node_key`
  (`ExactFlatFacts.lean:158`) under the `sizeProperPortsX` guard
  (`ExactPipeline.lean:55`); key fields survive by `ExactPartBounded.lean`.
* `forward_anchor_full` replaced by `X_forward_anchor_full`
  (`ExactFlatC7Forward.lean:84`, private) with `labelAnchorIndex_eq` (shared).
* forward/reversed/loop envelopes replaced by `XPlaced_envelope_forward`
  (`ExactFlatC7Placed.lean:64`), `XPlaced_envelope_reversed`
  (`ExactFlatC7Placed.lean:155`), `XPlaced_envelope_loop`
  (`ExactFlatC7Placed.lean:48`), and the loop containment copies in
  `ExactFlatC7Loop.lean`.
* label placement replaced by `x_routeLabelsPlaced_holds`
  (`ExactFlatC7Placed.lean:241`) for `X_RouteLabelsPlaced`.
* run-local separations replaced by `x_runLocalForwardSeparation_holds`
  (`ExactFlatC7Forward.lean:584`), `x_runLocalReversedSeparation_holds`
  (`ExactFlatC7Reversed.lean`), and `x_runLocalLoopSeparation_holds`
  (`ExactFlatC7Loop.lean:393`); the loop footprint stage stays as the open
  residual `X_RunLocalLoopFootprint` (`ExactFlatC7Loop.lean:41`).
* span seams replaced by `X_C8a_ForeignClusterRankSpans`
  (`ExactFlatC8a.lean:35`), `X_C8a_BracketMarkersAtRank`
  (`ExactFlatC8a.lean:120`), and `X_ForeignBorderChainXAligned`
  (`ExactFlatC7CaptionScope.lean:58`).

The two coarse premises below encapsulate all of the above seam facts in exact
form (each is a single fact over exact runs, strictly narrower than the goal:
forward-only and nonforward-only label clearance). They are weakenings of the
goal itself, so the probe for `XF_RouteRunClearX` in
`proofs/wip/Probe/ExactPartFrameCoresTProbe.lean` (premise(route) true on flat,
nested, sane fixed, and wider-than-slot fixed inputs) is evidence for both.
The pure dispatch (`placed_mem_unpack`, case split on edge form) and the bridge
`routeRunClear_of_inlined` transfer verbatim; no pipeline is unfolded and no
`coordinateGraphX` fact is fed to a plain lemma. -/

/-- Exact forward route clearance: placed labels of forward edges clear every
in-bounds frame position. Narrower than `XF_RouteRunClearX` (forward edges
only). -/
theorem XF_routeRunClearX_holds (exactIds : List String)
    (hRrFwdX : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate)
        execution.measured orderOptions = .ok run →
      ∀ (k : Nat) (rect : Rect) (l₀ : MeasuredLabel) (edge : Nat) (e : Edge),
      (k, rect) ∈ placedLabels execution.params
        (componentCandidate execution.graph comp candidate) run
        execution.measured →
      l₀ ∈ execution.measured → l₀.index = k →
      (componentCandidate execution.graph comp candidate).edges[edge]? = some e →
      e.decl = l₀.edge → e.tail ≠ e.head → e.reversed = false →
      ∀ (pos : Nat), pos <
        (componentCandidate execution.graph comp candidate).nodes.length →
      Disjoint (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos) rect ∨
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos).StrictInside rect)
    (hRrNonfwdX : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate)
        execution.measured orderOptions = .ok run →
      RouteNonforwardLabelClear execution.params
        (componentCandidate execution.graph comp candidate) run
        execution.measured) :
    XF_RouteRunClearX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  have hfwd := hRrFwdX execution hcomp hrun
  have hnon := hRrNonfwdX execution hcomp hrun
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

end PipelineImpl
end Layered
end Elegant

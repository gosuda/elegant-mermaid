import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.LoopFootprintFactsProof
import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.LoopFootprintGeneralOrder
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.RunLocalSeparationsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Reservation part of the loop footprint (candidate order): the loop band
fits in the owner frame. Bridge (a): `frameRect` ignores its `Params`
argument, so `execution.params` and `default` give definitionally equal rects. -/
theorem loopReservation_part {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (_orderOptions : OrderOptions) (cg : Graph) (_k : Nat) (e : Edge)
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidate execution.graph comp candidate)
    (hrun : componentRun execution.params cg execution.measured
      (candidateOrder candidate) = .ok run)
    (_hk : cg.edges[_k]? = some e)
    (_hloop : e.tail = e.head) :
    (loopSizes cg.edges execution.measured e.tail cg.slot).length *
        Loops.band cg.slot (loopSizes cg.edges execution.measured e.tail cg.slot) ≤
      (frameRect execution.params cg run e.tail).h := by
  subst hcg
  have hres := loopReservation_executed execution comp candidate run e.tail hcomp hrun
  unfold Elegant.Layered.PipelineImpl.LoopReservation at hres
  obtain ⟨_, hle⟩ := hres
  exact hle

/-- Separation part of the loop footprint (candidate order, plain foreign box):
the footprint misses the box. Bridge (b): for a foreign index below the
proper length whose candidate border is `0` (hence `≠ -2`), `frameRect`
takes the `nodeRect` branch and `plain_frame_eq_boxRect` rewrites it to
`boxRect`, so the `Disjoint` from `loopFootprintSeparation_executed'`
is exactly the goal. -/
theorem loopFootprintMisses_part {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (_orderOptions : OrderOptions) (cg : Graph) (_k : Nat) (e : Edge) (v : Nat)
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidate execution.graph comp candidate)
    (hrun : componentRun execution.params cg execution.measured
      (candidateOrder candidate) = .ok run)
    (_hk : cg.edges[_k]? = some e)
    (_hloop : e.tail = e.head)
    (hv : v < run.proper.nodes.length)
    (_hreal : RouteImpl.IsReal run.proper v)
    (_hscope0 : RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [])
    (_hscope1 : RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [])
    (htop : LoopFootprintTopSeparation inp o res)
    (hbeyond : LoopFootprintBeyondProper inp o res)
    (hbord : ((componentCandidate execution.graph comp candidate).nodes.getD v default).border = 0) :
    ¬ (loopFootprint cg run execution.measured e.tail).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  subst hcg
  have hsep := loopFootprintSeparation_executed' execution comp candidate run e.tail v
    hcomp hbord hrun htop hbeyond
  unfold Elegant.Layered.PipelineImpl.LoopFootprintSeparation at hsep
  have hbox : frameRect default (componentCandidate execution.graph comp candidate) run v =
      RouteImpl.boxRect run.proper run.xs run.ys v :=
    plain_frame_eq_boxRect default _ _ v hv (by omega)
  rw [← hbox]
  exact hsep

/-- Full loop footprint seam at any order options. Reservation comes from
`loopReservation_general` (bridge (a): `frameRect` ignores its `Params`
argument, so `execution.params` and `default` are definitionally equal).
Separation splits on the box index: an in-range plain box uses
`loopFootprintSeparation_general` with the `frameRect`-to-`boxRect` rewrite
(border `0 ≠ -2`); an in-range non-plain box has a zero-height box by bridge
(c) (`loopBoxZero_of_nonplain`, via the proved `LoopFootprintOtherBorder`:
`±2` borders, `titleF`-zeroed heights carried through the coordinate phases,
so `not_meetsInterior_of_box_zero_h` closes it); a beyond-candidate box in
the proper nodes uses the `BeyondProper` residual with the default-border
rewrite. The owner needs no case split: the general separation and residual
handle plain, top, bottom, and out-of-range owners internally. `hwf`/`hframed`
are retained for the seam shape; no step uses them. -/
theorem runLocalLoopFootprint_executed {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (htop : LoopFootprintTopSeparationG inp o res)
    (hbeyond : LoopFootprintBeyondProperG inp o res) :
    RunLocalLoopFootprint inp o res := by
  have _hwf := hwf
  have _hframed := hframed
  intro execution comp candidate run orderOptions cg k e v hcomp hcg hrun hk hloop hv
    hreal hscope0 hscope1
  subst hcg
  have hres := loopReservation_general execution comp candidate orderOptions run e.tail
    hcomp hrun
  unfold Elegant.Layered.PipelineImpl.LoopReservation at hres
  obtain ⟨-, hle⟩ := hres
  refine ⟨hle, ?_⟩
  by_cases hvlen : v < (componentCandidate execution.graph comp candidate).nodes.length
  · by_cases hbord0 : ((componentCandidate execution.graph comp candidate).nodes.getD v
        default).border = 0
    · have hsep := loopFootprintSeparation_general execution comp candidate orderOptions
        run e.tail v hcomp hbord0 hrun htop hbeyond
      unfold Elegant.Layered.PipelineImpl.LoopFootprintSeparation at hsep
      have hne : ((componentCandidate execution.graph comp candidate).nodes.getD v
          default).border ≠ -2 := by rw [hbord0]; decide
      have hbox : frameRect default (componentCandidate execution.graph comp candidate)
          run v = RouteImpl.boxRect run.proper run.xs run.ys v :=
        plain_frame_eq_boxRect default _ _ v hv hne
      rw [← hbox]
      exact hsep
    · have hzero := loopBoxZero_of_nonplain execution comp candidate orderOptions run v
        hcomp hrun hvlen hbord0
      exact not_meetsInterior_of_box_zero_h hzero
  · have hmem : (componentCandidate execution.graph comp candidate).edges[k]? = some e :=
      hk
    have hbd := sceneExecution_edges_bounded execution
    have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp candidate
      hcomp hbd (List.mem_of_getElem? hmem)
    have howner : e.tail < (componentCandidate execution.graph comp candidate).nodes.length :=
      hbnd.1
    have hle' : (componentCandidate execution.graph comp candidate).nodes.length ≤ v :=
      Nat.le_of_not_lt hvlen
    have hsep := hbeyond execution comp candidate run orderOptions e.tail v hcomp hrun
      howner hle' hv
    unfold Elegant.Layered.PipelineImpl.LoopFootprintSeparation at hsep
    have hnone : (componentCandidate execution.graph comp candidate).nodes[v]? = none :=
      List.getElem?_eq_none (by omega)
    have hget : (componentCandidate execution.graph comp candidate).nodes.getD v default =
        default := by
      rw [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    have hne : ((componentCandidate execution.graph comp candidate).nodes.getD v
        default).border ≠ -2 := by rw [hget]; decide
    have hbox : frameRect default (componentCandidate execution.graph comp candidate)
        run v = RouteImpl.boxRect run.proper run.xs run.ys v :=
      plain_frame_eq_boxRect default _ _ v hv hne
    rw [← hbox]
    exact hsep

end PipelineImpl
end Layered
end Elegant

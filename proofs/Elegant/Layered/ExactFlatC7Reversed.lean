import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.LabelsC7RunLocal

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-- Reversed-branch residual over the exact run: the label rect of a reversed
edge stays in its planned lane, right of every box. Replay of
`runLocalReversedSeparation` over `componentRunX_spec`: the lane x-bound does
not depend on the rank shift (`reserveExactRanks` shifts `run.ys`/`run.top`,
not `run.xs`/`run.lanes`), so the planned-lane bound transports unchanged. -/
theorem x_runLocalReversedSeparation_holds (exactIds : List String) :
    X_RunLocalReversedSeparation exactIds := by
  unfold X_RunLocalReversedSeparation
  intro inp o res execution comp candidate run orderOptions cg k e env v r
    hcomp hcg hrun hk hne hrev henv hv hreal _hscope₀ _hscope₁ hr
  have _hslot := componentRunX_slot_nonneg hrun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrLanes, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨_first, lane, _hfirst, hlane, henv_eq⟩ :=
    reversed_envelope_eq hne hrev henv
  have hmem : lane ∈ run.lanes.runs := List.mem_of_find?_eq_some hlane
  obtain ⟨_base, _, h1slot, hlr⟩ := RouteImpl.routeWithLanes_spec hrLanes
  rw [hlr] at hmem
  have hge := RouteImpl.plannedLane_right_strict (by omega : 0 ≤ execution.params.slot) hmem
  have hbound := RouteImpl.laneRight_bound run.proper run.xs hv
  have hrx : r.x = env.x := (stackRects_entry hr).1
  have henvx : env.x = lane.lane + cg.slot := by
    rw [henv_eq]
    rfl
  have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).x =
      RouteImpl.xAt run.xs v - Int.fdiv (RouteImpl.nodeW run.proper v) 2 :=
    boxRect_left _ _ _ _
  have hboxw : (RouteImpl.boxRect run.proper run.xs run.ys v).w =
      RouteImpl.nodeW run.proper v :=
    boxRect_w _ _ _ _
  have _hloop : 0 ≤ (run.proper.nodes.getD v default).node.loopExtent :=
    Nat.zero_le _
  have e2 : Int.fdiv (RouteImpl.nodeW run.proper v) 2 =
      RouteImpl.nodeW run.proper v / 2 := fdiv2_ediv _
  rw [hrx, henvx, hbox, hboxw, e2]
  rw [e2] at hbound
  omega

end PipelineImpl
end Layered
end Elegant

import Elegant.Layered.LaneEndsPinPhaseReroute

set_option autoImplicit false

/-! Executed-band fresh-ends closure for the reroute phase.

`lepePhaseRerouteExec_holds` (in `LaneEndsPinPhaseReroute`) reduces the
executed reroute phase to `lepeRerouteFreshEndsExec`: one rebuilt cross-band
route keeps its ends on the old frames. `findRoute` preserves its `routeEnds`
endpoints globally (`findRouteEndsPin_holds`), so the only remaining content
is that the `routeEnds` source and target themselves lie on the old frames.
`lepeRerouteEndsBdryExec` states exactly that for the executed band list;
`lepeRerouteFreshEndsExec_holds` adds the `findRoute` endpoint preservation.
Truth-first probe: `proofs/wip/Probe/LaneRerouteFreshEndsTProbe.lean` checks
the `routeEnds` boundary on the cross-lane input A (pinned `[(20,70),(20,180)]`,
routed `[(20,70),(15,70),(15,180),(20,180)]`) and the other four swimlane
inputs; an overflow-shift band list errors. -/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Narrow residual: the `routeEnds` source and target of one rebuilt
cross-band route land on the old frames, on executed runs only. Strictly
narrower than `lepeRerouteFreshEndsExec` (ends, not the searched polyline;
no `obs` or `findRoute` premise). -/
def lepeRerouteEndsBdryExec (boxes : List ModelBox) (o : Options) (s : Scene) : Prop :=
  ∀ (sp : Spacing) (_hsp : spacingOf o.profile = .ok sp)
    (_hnodupB : (s.boxes.map (·.id)).Nodup)
    (_hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
    {pinned : Scene}
    (_happ : applyPin (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s = .ok pinned)
    (_hC5 : Validator.C5 s.layoutDump)
    (_hEndsPin : FindRouteEndsPin)
    {r old : Route} (_hr : r ∈ pinned.routes) (_hold : old ∈ s.routes)
    {fi ti : Nat} {fb tb : Box}
    (_hfi : (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)).findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) = some fi)
    (_hti : (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)).findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) = some ti)
    (_hfb : pinned.boxes.find? (fun b => b.id == r.fromId) = some fb)
    (_htb : pinned.boxes.find? (fun b => b.id == r.toId) = some tb)
    {ends : RouteEnds}
    (_hends : routeEnds (Axis.ofDirection o.direction) sp (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) fb tb old.points = .ok ends),
  ∃ fbp tbp : Box,
    pinned.layoutDump.box? r.fromId = some fbp ∧ pinned.layoutDump.box? r.toId = some tbp ∧
    Validator.onBoundary ends.source (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) fbp) ∧
    Validator.onBoundary ends.target (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) tbp)

/-- The fresh-ends residual follows from the `routeEnds` boundary plus the
global `findRoute` endpoint preservation. -/
theorem lepeRerouteFreshEndsExec_holds {boxes : List ModelBox} {o : Options} {s : Scene}
    (hBdry : lepeRerouteEndsBdryExec boxes o s) : lepeRerouteFreshEndsExec boxes o s := by
  intro sp hsp hnodupB hModelClean pinned happ hC5 hEndsPin r old hr hold fi ti fb tb hfi hti hfb htb ends obs pts hends hobs hfind
  obtain ⟨fbp, tbp, hfbp, htbp, hbs, hbt⟩ :=
    hBdry sp hsp hnodupB hModelClean happ hC5 hEndsPin hr hold hfi hti hfb htb hends
  obtain ⟨hhead, hlast⟩ :=
    hEndsPin (Axis.ofDirection o.direction) sp (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) fb tb old.points ends obs (LayoutConst.rank_gap.get o.profile) pts hends hfind
  exact ⟨ends.source, ends.target, fbp, tbp, hhead, hlast, hfbp, htbp, hbs, hbt⟩

/-- The executed reroute phase, closed up to the narrow `routeEnds` boundary. -/
theorem lepePhaseRerouteExec_closed {boxes : List ModelBox} {o : Options} {s : Scene}
    (hBdry : lepeRerouteEndsBdryExec boxes o s) : lepePhaseRerouteExec boxes o s :=
  lepePhaseRerouteExec_holds (lepeRerouteFreshEndsExec_holds hBdry)

end LaneBands
end Layered
end Elegant

import Elegant.Layered.LaneEndsPinEnds
import Elegant.Layered.LaneEndsPinPhases
import Elegant.Layered.LaneBandsRouteClausesProof

set_option autoImplicit false

/-! Executed-band reroute phase for `pinBands_ends`.

`pinBands_ends_closed` (in `LaneEndsPinPhases`) still quantifies the reroute
phase over arbitrary band lists. That universal is vacuous off the executed
list (its `hbands` premise pins `bands` to `layBands`), but the shape is still
banned: no premise may quantify over arbitrary bands. This module states the
phase for the executed band list only and closes it up to one narrow residual.
Truth-first probes live in `proofs/wip/Probe/LanePhaseRerouteTProbe.lean`: the
executed list keeps ends on old frames on all five swimlane inputs (two lanes
with a cross-lane edge, a lane self-loop, a lane-frame-to-node edge, a nested
group in a lane, a loose node), while an overflow-shift band list errors. -/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Reroute phase fact for the executed band list only. Hypotheses are exactly
those `pinBands_ends_closed` has in scope; `axis` is the executed direction
and `bands` is the executed `layBands` output, never quantified. -/
def lepePhaseRerouteExec (boxes : List ModelBox) (o : Options) (s : Scene) : Prop :=
  ∀ (sp : Spacing) (_hsp : spacingOf o.profile = .ok sp)
    (_hnodupB : (s.boxes.map (·.id)).Nodup)
    (_hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
    (_hEndsPin : FindRouteEndsPin)
    {pinned routed : Scene}
    (_happ : applyPin (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s = .ok pinned)
    (_hEndsOld : EndsOnOld (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) pinned.layoutDump)
    (_hC5 : Validator.C5 s.layoutDump)
    (_hroute : rerouteBands (Axis.ofDirection o.direction) sp (LayoutConst.rank_gap.get o.profile) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) s.routes pinned = .ok routed),
  EndsOnOld (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) routed.layoutDump

/-- Narrow residual: the fresh ends of one rebuilt cross-band route land on
the old frames, on executed runs only. Strictly narrower than
`lepePhaseRerouteExec` (one route, not every routed route). The cross-lane
probe input exercises this path (`findIdx` values `0` and `1`, pinned points
differ from routed points, `endsOldBool` stays `true`). -/
def lepeRerouteFreshEndsExec (boxes : List ModelBox) (o : Options) (s : Scene) : Prop :=
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
    {ends : RouteEnds} {obs : List Obstacle} {pts : List Point}
    (_hends : routeEnds (Axis.ofDirection o.direction) sp (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) fb tb old.points = .ok ends)
    (_hobs : obs = ((pinned.boxes.filter (fun b => b.exclusive && b.id != r.fromId && b.id != r.toId)).map (fun b => obstacleOf (Axis.ofDirection o.direction) b.rect) ++ textObstacles (Axis.ofDirection o.direction) pinned))
    (_hfind : findRoute (Axis.ofDirection o.direction) ends obs (LayoutConst.rank_gap.get o.profile) [sp.slot, 0] = .ok pts),
  ∃ p q : Point, ∃ fbp tbp : Box,
    pts.head? = some p ∧ pts.getLast? = some q ∧
    pinned.layoutDump.box? r.fromId = some fbp ∧ pinned.layoutDump.box? r.toId = some tbp ∧
    Validator.onBoundary p (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) fbp) ∧
    Validator.onBoundary q (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) tbp)

/-- The executed reroute phase follows from the fresh-ends residual: kept
routes transport `hEndsOld` across unchanged boxes, fresh routes use the
residual. -/
theorem lepePhaseRerouteExec_holds {boxes : List ModelBox} {o : Options} {s : Scene}
    (hFresh : lepeRerouteFreshEndsExec boxes o s) : lepePhaseRerouteExec boxes o s := by
  intro sp hsp hnodupB hModelClean hEndsPin pinned routed happ hEndsOld hC5 hroute
  have hboxesEq : routed.boxes = pinned.boxes := (rerouteBands_frame hroute).1
  have hdumpEq : routed.layoutDump.boxes = pinned.layoutDump.boxes := hboxesEq
  intro r' hr'
  obtain ⟨r, hrmem, old, holdmem, hpair, hid, hfrom, hto, horthEq, hcase⟩ :=
    c4c5_reroute_mem _ _ _ _ _ _ _ _ hroute r' hr'
  rcases hcase with ⟨hptsEq, _⟩ | ⟨fi, ti, fb, tb, ends, obs, pts, hfi, hti, hfb, htb, hends, hobs, hfind, hptsPts⟩
  · obtain ⟨p, q, fbp, tbp, hp, hq, hfbp, htbp, hb1, hb2⟩ := hEndsOld r hrmem
    refine ⟨p, q, fbp, tbp, ?_, ?_, ?_, ?_, hb1, hb2⟩
    · rw [hptsEq]; exact hp
    · rw [hptsEq]; exact hq
    · unfold LayoutDump.box?
      rw [hdumpEq, hfrom]; exact hfbp
    · unfold LayoutDump.box?
      rw [hdumpEq, hto]; exact htbp
  · obtain ⟨p, q, fbp, tbp, hp, hq, hfbp, htbp, hb1, hb2⟩ :=
      hFresh sp hsp hnodupB hModelClean happ hC5 hEndsPin hrmem holdmem hfi hti hfb htb hends hobs hfind
    refine ⟨p, q, fbp, tbp, ?_, ?_, ?_, ?_, hb1, hb2⟩
    · rw [hptsPts]; exact hp
    · rw [hptsPts]; exact hq
    · unfold LayoutDump.box?
      rw [hdumpEq, hfrom]; exact hfbp
    · unfold LayoutDump.box?
      rw [hdumpEq, hto]; exact htbp

end LaneBands
end Layered
end Elegant

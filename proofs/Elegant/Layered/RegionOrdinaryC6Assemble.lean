import Elegant.Layered.RegionCrossCoordsMetadata
import Elegant.Layered.RegionOrdinaryC6Lanes

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl.RegionOrdinaryC6

open RegionImpl RouteImpl

/-- The allocation-side obligation for the selected finite reversed trunk. -/
def ReservedTrunkClear (P : Params) (rm : ComponentRegions) (cg : Graph)
    (labels : List MeasuredLabel) (run : Run) (original v : Nat) : Prop :=
  ∀ {p : Proper} {minimum : RegionConstraints} {ord : OrderResult}
      {reserved : List (Option Int)}
      (stages : RegionCrossAllocationStages P rm cg labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper)
      {lane : ReversedLane},
    run.lanes.runs.find? (fun lane => lane.original == original) = some lane →
    stages.allocation.lanes.getD original none = some lane.lane →
    VerticalTrunkClear (boxRect run.proper run.xs run.ys v) lane.lane
      (reverseRunMid P.slot run.top (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing
        lane.sourceGap lane.sourceSegment)
      (reverseRunMid P.slot run.top (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing
        lane.targetGap lane.targetSegment)

/-- Apply run-local geometry to the actual active router, classified by the
    chain's lane lookup, not by the global region-set list. Only the reserved
    lane needs an allocation-side separation proof. -/
theorem activeNativeMiss {P : Params} {exactIds : List String} {s : RegionSpec}
    {inp : Input} {cg cg' : Graph} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions} {run : Run}
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp cg labels orderOptions =
      .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm))
    (hfacts : CoordFacts run.proper run.layers run.xs run.ys run.top run.routing
      (min P.nodeGap P.clusterPad) (reservedRouteRankGap P run) P.slot)
    {native : EdgeRoute} (hnative : native ∈ run.routes) {first last v : Nat}
    (hfirst : (edgesOf run.proper native.original).head? = some first)
    (hlast : (edgesOf run.proper native.original).getLast? = some last)
    (hv : v < run.proper.nodes.length) (hreal : IsReal run.proper v)
    (hfrom : v ≠ (edgeAt run.proper first).tail) (hto : v ≠ (edgeAt run.proper last).head)
    (hreserved : ReservedTrunkClear P rm cg' labels run native.original v) :
    ¬ Polyline.hitsRect native.points (boxRect run.proper run.xs run.ys v) := by
  have hshape := componentRunR_properShape_someR rfc4CrossCoordsR_metadata_holds s rfl hrun
  obtain ⟨_, _, _, reserved, widths, ⟨allocation⟩, hmodes, hpoints⟩ :=
    activeExecutionLanes hrun hactive
  obtain ⟨hi, hroute⟩ := routePointsWithLanes_mem hpoints hnative
  have hc := hfacts
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  rw [← stages.hRouting] at hc
  rcases hmodes with ⟨_, hout⟩ | ⟨_, hR⟩
  · exact route_avoids_nodes hshape hout hpoints hc native hnative first last hfirst hlast
      v hv hreal hfrom hto
  cases hfind : run.lanes.runs.find? (fun lane => lane.original == native.original) with
  | none =>
    exact activeForward_nativeMiss hshape hR hc hfind hroute hi hfirst hlast hv hreal hfrom hto
  | some lane =>
    have hmember := List.mem_of_find?_eq_some hfind
    have hkey : lane.original = native.original := by
      simpa only [beq_iff_eq] using List.find?_some hfind
    obtain ⟨hs, ht, hsb, htb, hsr, htr, hsg, htg, hsx0, hsx1, htx0, htx1, htrun⟩ :=
      activeReverse_nodeFacts hR hmember (by rwa [hkey]) (by rwa [hkey])
    have htrunk : VerticalTrunkClear (boxRect run.proper run.xs run.ys v) lane.lane
        (reverseRunMid P.slot run.top (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing
          lane.sourceGap lane.sourceSegment)
        (reverseRunMid P.slot run.top (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing
          lane.targetGap lane.targetSegment) := by
      rcases activeLane_origin (y := run.ys) hR hmember with hr | ⟨_, hright⟩
      · apply hreserved allocation hfind
        rwa [← allocation.hLanes, ← hkey]
      · exact Or.inr (Or.inl (Int.le_of_lt (hright v hv)))
    obtain ⟨base, hb, _, hrouter⟩ := routeWithLanesR_spec hR
    have hmem : lane ∈ plannedLanesR P.slot run.proper base run.xs
        (cg'.edges.map (·.reversed)) widths reserved := by
      rw [hrouter] at hmember
      exact hmember
    obtain ⟨hrawS, hrawT⟩ := activeReverse_rawSegments hmem
    have hlen : base.gaps.length = run.layers.length - 1 := by
      rw [(route_spec hb).2.2.2.2.2.1]
      simp
    have hgap (k : Nat) (hk : k < base.gaps.length) :
        run.lanes.routing.gaps.getD k default = numberLaneGap (laneGapSegments run.proper base
          (cg'.edges.map (·.reversed))
          (plannedLanesR P.slot run.proper base run.xs (cg'.edges.map (·.reversed)) widths reserved) k) := by
      rw [hrouter]
      simp [assembleLaneRouting, List.getD_eq_getElem?_getD, hk]
    have hstep (k : Nat) (hk : k + 1 < run.layers.length) :
        run.top.getD k 0 + (run.layers.map (RouteImpl.layerHeight run.proper)).getD k 0 +
          reservedRouteRankGap P run k + P.slot * (run.lanes.routing.gaps.getD k default).slots ≤
          run.top.getD (k + 1) 0 := by
      have hk' : k < run.layers.length := by omega
      have hl := List.getElem?_eq_getElem hk'
      rw [heights_getD hl]
      rw [hc.band_step k run.layers[k] hl hk]
      omega
    have hsMid := activeReverse_mid_of_get (hgap _ (by omega)) hrawS hc.slot_pos
      (hc.half_slot_le _) (hstep _ hsg)
    have htMid := activeReverse_mid_of_get (hgap _ (by omega)) hrawT hc.slot_pos
      (hc.half_slot_le _) (hstep _ htg)
    have hgeo := geo_ok_of_layers (route_spec hb).1 (fun _ hk => activeGap_nonneg hR hk) hc
    exact activeReverse_nativeMiss hfind hroute hgeo hsb htb hv
      (by rwa [hs]) (by rwa [ht]) hsr htr htg ⟨hsx0, hsx1⟩ ⟨htx0, htx1⟩ hsMid htMid
      htrun htrunk

end Elegant.Layered.PipelineImpl.RegionOrdinaryC6

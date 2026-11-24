import Elegant.Layered.RegionC6ReservedTrunkGeometry
import Elegant.Layered.RegionC6TrunkPlainTransport
import Elegant.Layered.RegionReservedLaneStability
import Elegant.Layered.RegionActiveFrameLabels
import Elegant.Layered.RegionOrdinaryC6Assemble

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace Elegant.Layered.PipelineImpl.RegionOrdinaryC6

open RegionImpl RouteImpl

private theorem activeLane_reversed {slot : Int} {p : Proper} {layers : List (List Nat)}
    {xs : List Int} {flags : List Bool} {widths : List Int} {reserved : List (Option Int)}
    {router : LaneRouting} {lane : ReversedLane}
    (hr : routeWithLanesR slot p layers xs flags widths reserved = .ok router)
    (hl : lane ∈ router.runs) : flags.getD lane.original false = true := by
  obtain ⟨base, _, _, hplan⟩ := routeWithLanesR_spec hr
  rw [hplan] at hl
  change lane ∈ plannedLanesR slot p base xs flags widths reserved at hl
  obtain ⟨i, k, hm, rfl⟩ := rcbPlannedLanesR_mem hl
  have hlist : i ∈ laneOriginals p flags :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hm)
  unfold laneOriginals at hlist
  have hflags := (List.mem_filter.mp hlist).2
  exact (Bool.and_eq_true_iff.mp hflags).1

/-- Both the selected reversed trunk and its complete label width are reserved
away from every original plain box. -/
theorem selectedTrunk_labelBand_crossClear {P : Params} {exact : List Nat} {s : RegionSpec}
    {inp : Input} {o : Options} {candidate cg : Graph} {rm : ComponentRegions} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions}
    (hp : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P exact (some s) inp candidate labels order = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    {original v : Nat} {edge : Edge} {source : Node} {lane : ReversedLane}
    (hedge : cg.edges[original]? = some edge) (hnotLoop : edge.tail ≠ edge.head)
    (hv : cg.nodes[v]? = some source) (hplain : source.border = 0)
    (hfind : run.lanes.runs.find? (fun l => l.original == original) = some lane) :
    lane.lane + (P.slot + (stackSize cg.slot (routeLabels labels edge.decl)).width) ≤
        (boxRect run.proper run.xs run.ys v).x ∨
      (boxRect run.proper run.xs run.ys v).x + (boxRect run.proper run.xs run.ys v).w ≤ lane.lane := by
  obtain ⟨rs, ranks, budget, p₀, labeled, p, _, ord, _, reserved, _, _, _, _, trace⟩ :=
    componentRunR_stages hrun
  have hrs : rs = some rm := Except.ok.inj (trace.hRs.symm.trans hactive)
  rcases trace.hPlaced with ⟨hnone, _⟩ | ⟨rm', minimum, hsome, hm, hcross⟩
  · rw [hrs] at hnone
    cases hnone
  have he : rm' = rm := Option.some.inj (hsome.symm.trans hrs)
  subst rm'
  rw [← trace.hCoordProper] at hcross
  obtain ⟨st⟩ := crossCoordsR_allocation_stages hcross
  have hmin : constrainR rm P p = .ok minimum := by
    rcases trace.hMin with ⟨hnone, _⟩ | ⟨r, m, hr, hm', hc⟩
    · rw [hrs] at hnone
      cases hnone
    have he : r = rm := Option.some.inj (hr.symm.trans hrs)
    have hme : m = minimum := Option.some.inj (hm'.symm.trans hm)
    simpa only [he, hme] using hc
  have hrank : rankEquivalentR rm candidate = .ok (ranks, cg, budget) := by
    rcases trace.hRank with ⟨_, hnone, _⟩ | ⟨r, he, hr⟩
    · rw [hrs] at hnone
      cases hnone
    have h : r = rm := Option.some.inj (he.symm.trans hrs)
    simpa only [h] using hr
  have hchains : p.chains.length = cg.edges.length := by
    have hc : p.chains = labeled.chains := by rw [← trace.hCoord]; exact rcbCoordinateR_chains
    rw [hc, (Labels.addLabelNodes_metadata trace.hLabels).2.2.1]
    exact normalize_chains_length (p := p₀) trace.hNorm
  have hrouter : routeWithLanesR P.slot run.proper run.layers run.xs (cg.edges.map (·.reversed))
      (cg.edges.map fun ed => (stackSize cg.slot (routeLabels labels ed.decl)).width)
      reserved = .ok run.lanes := by
    rcases trace.hLanes with ⟨hempty, _⟩ | ⟨_, hroute⟩
    · have hlen := st.trunk_lane_table_length
      rw [List.nil_of_isEmpty hempty, List.length_nil, hchains] at hlen
      have hbound := (List.getElem?_eq_some_iff.mp hedge).1
      omega
    · simpa only [trace.hLabelWidths] using hroute
  have hmember := List.mem_of_find?_eq_some hfind
  have hkey : lane.original = original := by
    simpa only [beq_iff_eq] using List.find?_some hfind
  have hslot := componentRunR_slot_pos hrun
  have hparents := activeRegion_parent_count hactive
  obtain ⟨n, hn, hb, hproper, hx⟩ := actualPlainNode_record hrun hactive hrank trace.hNorm
    trace.hLabels trace.hCoord st hv hplain
  let owner := edgeOwnerOf rm st.groups rm.clusters.length edge.tail edge.head
  by_cases ho : owner < rm.clusters.length
  · have hflag := activeLane_reversed hrouter hmember
    rw [hkey, List.getD_eq_getElem?_getD, List.getElem?_map, hedge, Option.map_some,
      Option.getD_some] at hflag
    obtain ⟨_, laneX, _, htable, hband⟩ := st.reserved_trunk_lane_band hparents hmin hchains
      (by omega) ho hedge hnotLoop hflag (show edgeOwnerOf rm st.groups rm.clusters.length
        edge.tail edge.head = owner from rfl)
    have hres : reserved.getD lane.original none = some laneX := by
      rw [st.hLanes, hkey, htable]
    have hlane := routeWithLanesR_label_lane_origin hrouter hmember
    rw [hres] at hlane
    change lane.lane = laneX at hlane
    rw [← allocationWidths_exact st, ← hlane] at hband
    have hinset : 0 < regionInsetOf P := by
      have hpad := (checkedParams_sizing_nonneg hp).2.1
      have hb := checkedParams_clusterBorderW_ge_one hp
      unfold regionInsetOf
      omega
    have hownerPath := actualBranch_from_root st hparents hmin (Nat.le_of_lt ho)
    have hnodePath := actualBranch_from_root st hparents hmin (actualMember_group_bound st hn)
    have hbox := allocatedMember_crossHull st hparents hmin hn hb rfl
    apply laneCrossClear_of_bucketHull st hparents hmin hinset hslot ho hownerPath hnodePath _ hband
    simpa only [boxRect, xAt, nodeW, hproper, hx] using hbox
  · have hnone := st.trunk_lane_absent_of_nonlocal_owner hedge (Nat.le_of_not_gt ho)
    rcases activeLane_origin (y := run.ys) hrouter hmember with h | ⟨_, hout⟩
    · rw [hkey, hnone] at h
      cases h
    · exact Or.inr (Int.le_of_lt (hout v (List.getElem?_eq_some_iff.mp hproper).1))

theorem selectedTrunk_crossClear {P : Params} {exact : List Nat} {s : RegionSpec}
    {inp : Input} {o : Options} {candidate cg : Graph} {rm : ComponentRegions} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions}
    (hp : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P exact (some s) inp candidate labels order = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    {original v : Nat} {edge : Edge} {source : Node} {lane : ReversedLane}
    (hedge : cg.edges[original]? = some edge) (hnotLoop : edge.tail ≠ edge.head)
    (hv : cg.nodes[v]? = some source) (hplain : source.border = 0)
    (hfind : run.lanes.runs.find? (fun l => l.original == original) = some lane) :
    lane.lane ≤ (boxRect run.proper run.xs run.ys v).x ∨
      (boxRect run.proper run.xs run.ys v).x + (boxRect run.proper run.xs run.ys v).w ≤ lane.lane := by
  rcases selectedTrunk_labelBand_crossClear (o := o) hp hrun hactive hedge hnotLoop hv hplain hfind with
    h | h
  · have hslot := componentRunR_slot_pos hrun
    have hw : 0 ≤ (stackSize cg.slot (routeLabels labels edge.decl)).width := by
      rw [stackSize_width_eq]
      exact Labels.stackWidth_nonneg _
    exact Or.inl (by omega)
  · exact Or.inr h

/-- The original allocation-side seam for a successful active run and an original
non-loop edge. The inputs are executable evidence; neither the arbitrary stage
witness quantified by the seam nor its observed local table lookup is needed. -/
theorem reservedTrunkClear_of_selectedGraph {P : Params} {exact : List Nat} {s : RegionSpec}
    {inp : Input} {o : Options} {candidate cg : Graph} {rm : ComponentRegions} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions}
    (hp : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P exact (some s) inp candidate labels order = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    {original v : Nat} {edge : Edge} {source : Node}
    (hedge : cg.edges[original]? = some edge) (hnotLoop : edge.tail ≠ edge.head)
    (hv : cg.nodes[v]? = some source) (hplain : source.border = 0) :
    ReservedTrunkClear P rm cg labels run original v := by
  intro p minimum ord reserved st lane hfind _
  rcases selectedTrunk_crossClear (o := o) hp hrun hactive hedge hnotLoop hv hplain hfind with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- This consumes the original active-router seam after transporting scope to
the two endpoint indices. The remaining coordinate facts are the existing
stub/gap/target-run contract, not reserved-trunk clearance. -/
theorem activeNativeMiss_of_selectedGraph {P : Params} {exactIds : List String}
    {s : RegionSpec} {inp : Input} {o : Options} {candidate cg : Graph} {rm : ComponentRegions}
    {run : Run} {labels : List MeasuredLabel} {order : OrderOptions}
    (hp : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp candidate labels order =
      .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hfacts : CoordFacts run.proper run.layers run.xs run.ys run.top run.routing
      (min P.nodeGap P.clusterPad) (reservedRouteRankGap P run) P.slot)
    {native : EdgeRoute} {edge : Edge} {source : Node} {first last v : Nat}
    (hnative : native ∈ run.routes)
    (hedge : cg.edges[native.original]? = some edge) (hnotLoop : edge.tail ≠ edge.head)
    (hvSource : cg.nodes[v]? = some source) (hvPlain : source.border = 0)
    (hfirst : (edgesOf run.proper native.original).head? = some first)
    (hlast : (edgesOf run.proper native.original).getLast? = some last)
    (hv : v < run.proper.nodes.length) (hreal : IsReal run.proper v)
    (hfrom : v ≠ (edgeAt run.proper first).tail) (hto : v ≠ (edgeAt run.proper last).head) :
    ¬ Polyline.hitsRect native.points (boxRect run.proper run.xs run.ys v) :=
  activeNativeMiss hrun hactive hfacts hnative hfirst hlast hv hreal hfrom hto
    (reservedTrunkClear_of_selectedGraph (o := o) hp hrun hactive hedge hnotLoop hvSource hvPlain)

end Elegant.Layered.PipelineImpl.RegionOrdinaryC6

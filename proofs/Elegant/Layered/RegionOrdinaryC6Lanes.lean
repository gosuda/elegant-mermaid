import Elegant.Layered.RegionC5Boundary
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionActiveOrderProof
import Elegant.Layered.ForwardLane
import Elegant.Layered.LaneValidity
import Elegant.Layered.LaneMetadata
import Elegant.Layered.ExactReservedRouteCoordsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl.RegionOrdinaryC6

open RegionImpl RouteImpl

/-- Keep allocation, the router mode, and emitted points tied to the same
    intermediate reservation table. -/
theorem activeExecutionLanes {P : Params} {exact : List Nat} {s : RegionSpec}
    {inp : Input} {cg cg' : Graph} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions} {run : Run}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult)
      (reserved : List (Option Int)) (widths : List Int),
      Nonempty (RegionCrossAllocationStages P rm cg' labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper) ∧
      ((reserved.isEmpty = true ∧ routeWithLanes P.slot run.proper run.layers run.xs
        (cg'.edges.map (·.reversed)) widths = .ok run.lanes) ∨
       (reserved.isEmpty = false ∧ routeWithLanesR P.slot run.proper run.layers run.xs
        (cg'.edges.map (·.reversed)) widths reserved = .ok run.lanes)) ∧
      routePointsWithLanes P.slot run.proper run.layers run.xs run.ys run.top
        run.lanes = .ok run.routes := by
  obtain ⟨rs, _, _, _, _, p, _, ord, widths, reserved, placed, _, _, _, stages⟩ :=
    componentRunR_stages hrun
  have hrs : rs = some rm := Except.ok.inj (stages.hRs.symm.trans hactive)
  rcases stages.hPlaced with ⟨hnone, _⟩ | ⟨rm', minimum, hsome, _, hcross⟩
  · rw [hrs] at hnone
    cases hnone
  · have hrm : rm' = rm := Option.some.inj (hsome.symm.trans hrs)
    subst rm'
    rw [← stages.hCoordProper] at hcross
    exact ⟨p, minimum, ord, reserved, widths, crossCoordsR_allocation_stages hcross,
      stages.hLanes, stages.hRoutes⟩

/-- Rank reservation increases the actual base gap. This argument is shared by
    both region router modes and does not assume an exact-layout execution. -/
theorem executedBand_step {P : Params} {exactIds : List String} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run))
    {k : Nat} {layer : List Nat} (hlayer : run.layers[k]? = some layer)
    (hk : k + 1 < run.layers.length) :
    run.top.getD (k + 1) 0 = run.top.getD k 0 + RouteImpl.layerHeight run.proper layer +
      reservedRouteRankGap P run k + P.slot * (run.routing.gaps.getD k default).slots := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, q0, ⟨_, preTop⟩, ysMid, stages⟩ :=
    componentRunR_stages hrun
  have hry := stages.hYt
  obtain ⟨extra, shifts, _, hnn, hpref, hlenS, htop, _⟩ :=
    (runHooksShift_exact P exactIds inp cg' labels).shifts placed run.layers ysMid
      preTop run.ys run.top stages.hReserve
  have htopLen : preTop.length = run.layers.length := (CoordsImpl.rankCoordsWith_length hry).2
  obtain ⟨_, _, hslotsLen, _, _, htopPre, _⟩ := CoordsImpl.rankCoordsWith_spec hry
  have hslotLen : (run.lanes.routing.gaps.map (·.slots)).length + 1 = run.layers.length := by
    omega
  have hgap : k < run.lanes.routing.gaps.length := by
    simp only [List.length_map] at hslotLen
    omega
  have hslot : (run.lanes.routing.gaps.map (·.slots)).getD k 0 =
      (run.lanes.routing.gaps.getD k default).slots := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hgap]
  have hshiftPair : shifts.Pairwise (· ≤ ·) := by
    rw [hpref]
    exact reserveShift_prefix_pairwise extra hnn 0 [] (by simp) (by simp)
  have hshiftNext : shifts.getD k 0 ≤ shifts.getD (k + 1) 0 := by
    have hi : k < shifts.length := by omega
    have hj : k + 1 < shifts.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simp only [Option.getD_some]
    exact hshiftPair.rel_getElem_of_lt hi hj (by omega)
  have hpreStep := rankSteps_topsFrom_step P.rankGap P.slot placed run.layers
    (run.lanes.routing.gaps.map (·.slots)) 0 k hslotLen hk
  rw [← htopPre, hslot, stages.hRouting] at hpreStep
  have hnodes : run.proper.nodes = q0.nodes := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
  have hLH : RouteImpl.layerHeight run.proper layer = CoordsImpl.layerHeight placed layer := by
    have he : RouteImpl.layerHeight run.proper layer = RouteImpl.layerHeight q0 layer := by
      simp only [RouteImpl.layerHeight, RouteImpl.nodeH, hnodes]
    exact he.trans (layerHeight_proxy stages.hProxy layer)
  have hRG : CoordsImpl.rankGapAt P.rankGap run.proper run.layers k =
      CoordsImpl.rankGapAt P.rankGap placed run.layers k := by
    rw [← stages.hDrop]
    exact rankGapAt_proxy stages.hProxy _ _ _
  have hlower : run.top.getD k 0 + RouteImpl.layerHeight run.proper layer +
      CoordsImpl.rankGapAt P.rankGap run.proper run.layers k +
      P.slot * (run.routing.gaps.getD k default).slots ≤ run.top.getD (k + 1) 0 := by
    rw [hLH, hRG, htop k (by omega), htop (k + 1) (by omega)]
    have hh : (run.layers.map (CoordsImpl.layerHeight placed)).getD k 0 =
        CoordsImpl.layerHeight placed layer := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hlayer, Option.map_some,
        Option.getD_some]
    rw [hh] at hpreStep
    omega
  have hreserve : reservedRouteRankGap P run k =
      run.top.getD (k + 1) 0 - run.top.getD k 0 - RouteImpl.layerHeight run.proper layer -
        P.slot * (run.routing.gaps.getD k default).slots := by
    unfold reservedRouteRankGap
    rw [RouteImpl.heights_getD hlayer]
    exact Int.max_eq_right (by omega)
  rw [hreserve]
  omega


private theorem foldMax_nonneg (reversed : List Bool) (widths : List Int)
    (indices : List Nat) (seed : Int) (hseed : 0 ≤ seed) :
    0 ≤ indices.foldl (fun m i => if reversed.getD i false then max m (widths.getD i 0) else m)
      seed := by
  induction indices generalizing seed with
  | nil => exact hseed
  | cons i rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact Int.le_trans hseed (Int.le_max_left _ _)
    · exact hseed

private theorem fallbackCount_nonneg (reserved : List (Option Int)) (originals : List Nat)
    (seed : Int) (hseed : 0 ≤ seed) :
    0 ≤ originals.foldl (fun n oo => if (reserved.getD oo none).isNone then n + 1 else n)
      seed := by
  induction originals generalizing seed with
  | nil => exact hseed
  | cons o rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split <;> omega

/-- The active router itself can choose an outer lane. Only `some` means that
    this route used a coordinate from allocation, even when the list is nonempty. -/
theorem activeLane_origin {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y : List Int} {reversed : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {lr : LaneRouting} {lane : ReversedLane}
    (hr : routeWithLanesR slot p layers x reversed widths reserved = .ok lr)
    (hm : lane ∈ lr.runs) :
    reserved.getD lane.original none = some lane.lane ∨
      (reserved.getD lane.original none = none ∧
        ∀ v, v < p.nodes.length → (boxRect p x y v).x + (boxRect p x y v).w < lane.lane) := by
  obtain ⟨base, _, hslot, hlr⟩ := routeWithLanesR_spec hr
  rw [hlr] at hm
  change lane ∈ plannedLanesR slot p base x reversed widths reserved at hm
  obtain ⟨o, index, _, rfl⟩ := rcbPlannedLanesR_mem hm
  let originals := laneOriginals p reversed
  let maxLabel := (List.range reversed.length).foldl (fun m i =>
    if reversed.getD i false then max m (widths.getD i 0) else m) 0
  let fallback := (originals.take index).foldl (fun (n : Int) oo =>
    if (reserved.getD oo none).isNone then n + 1 else n) 0
  change reserved.getD o none = some (makeLaneR slot p base x reversed widths reserved
    originals o index).lane ∨ (reserved.getD o none = none ∧ _)
  have hcoord :
      (makeLaneR slot p base x reversed widths reserved originals o index).lane =
        (match reserved.getD o none with
        | some lx => lx
        | none => laneRight p x + slot + fallback * (2 * slot + maxLabel)) := rfl
  rw [hcoord]
  cases reserved.getD o none with
  | some lx => exact Or.inl rfl
  | none =>
    refine Or.inr ⟨rfl, ?_⟩
    intro v hv
    have hwide : 0 ≤ maxLabel := foldMax_nonneg reversed widths _ 0 (by decide)
    have hfall : 0 ≤ fallback := fallbackCount_nonneg reserved _ 0 (by decide)
    have hstride : 0 ≤ 2 * slot + maxLabel := by omega
    have hcost : 0 ≤ fallback * (2 * slot + maxLabel) := Int.mul_nonneg hfall hstride
    have hloop : (0 : Int) ≤ ((p.nodes.getD v default).node.loopExtent : Int) :=
      Int.natCast_nonneg _
    calc
      (boxRect p x y v).x + (boxRect p x y v).w ≤ laneRight p x := by
        dsimp only [boxRect]
        exact Int.le_trans (Int.le_add_of_nonneg_right hloop) (laneRight_bound p x hv)
      _ < laneRight p x + slot := Int.lt_add_of_pos_right _ (by omega)
      _ ≤ laneRight p x + slot + fallback * (2 * slot + maxLabel) :=
        Int.le_add_of_nonneg_right hcost

/-- Numbered rank gaps are nonnegative in the reserved router as well. This
    permits reusing `geo_ok_of_layers` once the actual coordinates are established. -/
theorem activeGap_nonneg {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x : List Int} {reversed : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {lr : LaneRouting}
    (hr : routeWithLanesR slot p layers x reversed widths reserved = .ok lr)
    {k : Nat} (hk : k + 1 < layers.length) : 0 ≤ (lr.routing.gaps.getD k default).slots := by
  obtain ⟨_, _, _, _, hlen, _, hgap⟩ := rcbRouteWithLanesR_geometry hr
  have hlt : k < lr.routing.gaps.length := by omega
  have hm : lr.routing.gaps[k] ∈ lr.routing.gaps := List.getElem_mem hlt
  obtain ⟨segs, hsegs⟩ := hgap lr.routing.gaps[k] hm
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, hsegs]
  exact numberLaneGap_nonneg segs

/-- Runtime `find?` classification for a nonempty proper chain, not a test
    on whether the region spec or the reservation list is nonempty. -/
theorem activeForward_reversed_false {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x : List Int} {reversed : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {lr : LaneRouting} {i : Nat}
    (hr : routeWithLanesR slot p layers x reversed widths reserved = .ok lr)
    (hi : i < p.chains.length) (hne : (edgesOf p i).isEmpty = false)
    (hf : lr.runs.find? (fun run => run.original == i) = none) :
    reversed.getD i false = false := by
  cases he : reversed.getD i false with
  | false => rfl
  | true =>
    obtain ⟨base, _, _, hlr⟩ := routeWithLanesR_spec hr
    obtain ⟨lane, hmem, horig⟩ := rcbPlannedLaneR_exists
      (slot := slot) (base := base) (x := x) (widths := widths) (reserved := reserved) hi he hne
    have hl : lane ∈ lr.runs := by rw [hlr]; exact hmem
    exact False.elim (List.find?_eq_none.mp hf lane hl (by simp [horig]))

def VerticalTrunkClear (box : Rect) (lane cs ct : Int) : Prop :=
  lane ≤ box.x ∨ box.x + box.w ≤ lane ∨
    max cs ct ≤ box.y ∨ box.y + box.h ≤ min cs ct

/-- Separation concerns the executed finite trunk, not the whole line x = lane. -/
theorem reversedSevenPoint_avoids_either {G : Geo} {n K source target v sg tg : Nat}
    (hG : G.Ok n K) (hs : source < n) (ht : target < n) (hv : v < n)
    (hvs : v ≠ source) (hvt : v ≠ target) (hpos : 0 < G.hv v)
    (hsr : G.rk source = sg + 1) (htr : G.rk target = tg) (htg : tg + 1 < K)
    {sx tx tr cs ct lane : Int}
    (hsx : G.left source ≤ sx ∧ sx ≤ G.left source + G.wid source)
    (htx : G.left target ≤ tx ∧ tx ≤ G.left target + G.wid target)
    (htrun : (G.bd target ≠ -2 ∧ tr = tx) ∨ (G.bd target = -2 ∧ tr = G.left target))
    (hcs0 : G.T sg + G.H sg ≤ cs) (hcs1 : cs ≤ G.T (sg + 1))
    (hct0 : G.T tg + G.H tg ≤ ct) (hct1 : ct ≤ G.T (tg + 1))
    (hlane : VerticalTrunkClear (G.rect v) lane cs ct) :
    Polyline.allSegsMiss
      [⟨sx, G.yv source⟩, ⟨sx, cs⟩, ⟨lane, cs⟩, ⟨lane, ct⟩, ⟨tr, ct⟩,
        ⟨tr, G.yv target + G.hv target⟩, ⟨tx, G.yv target + G.hv target⟩] (G.rect v) := by
  have hw := hG.wid_nn target ht
  have htrr : G.left target ≤ tr ∧ tr ≤ G.left target + G.wid target := by
    rcases htrun with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact htx
    · omega
  have hxr : (G.bd target ≠ -2 ∧ G.left target ≤ tr ∧ tr ≤ G.left target + G.wid target) ∨
      (G.bd target = -2 ∧ tr = G.left target) := by
    rcases htrun with ⟨hnt, _⟩ | h
    · exact Or.inl ⟨hnt, htrr⟩
    · exact Or.inr h
  have htrunk : Polyline.segMisses ⟨lane, cs⟩ ⟨lane, ct⟩ (G.rect v) := by
    rcases hlane with hl | hr | ha | hb
    · exact miss_left (by simpa using hl)
    · exact miss_right (by simpa using hr)
    · exact miss_above ha
    · exact miss_below hb
  exact ⟨upperStub_miss hG hs hv hvs hpos hsr hsx hcs0 hcs1,
    gapLine_miss hG (by have := hG.rk_lt source hs; omega) hv hcs0 hcs1,
    htrunk, gapLine_miss hG htg hv hct0 hct1,
    lowerStub_miss hG ht hv hvt hpos htr htg hxr hct0 hct1,
    bottomEdge_hseg_miss hG ht hv hvt hpos htrr htx, trivial⟩

/-- Apply the finite-trunk argument to the actual routed polyline,
    including its range check and adjacent-point deduplication. -/
theorem activeReverse_nativeMiss {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {lr : LaneRouting} {lane : ReversedLane} {native : EdgeRoute} {v : Nat}
    (hf : lr.runs.find? (fun lane => lane.original == native.original) = some lane)
    (he : laneRouteOf slot p y top (layers.map (RouteImpl.layerHeight p)) lr native.original = .ok native)
    (hG : (routeGeo p layers x y top).Ok p.nodes.length layers.length)
    (hs : lane.sourceNode < p.nodes.length) (ht : lane.targetNode < p.nodes.length)
    (hv : v < p.nodes.length) (hvs : v ≠ lane.sourceNode) (hvt : v ≠ lane.targetNode)
    (hsr : (rk p.rank lane.sourceNode).toNat = lane.sourceGap + 1)
    (htr : (rk p.rank lane.targetNode).toNat = lane.targetGap)
    (htg : lane.targetGap + 1 < layers.length)
    (hsx : (boxRect p x y lane.sourceNode).x ≤ lane.sourceX ∧
      lane.sourceX ≤ (boxRect p x y lane.sourceNode).x + (boxRect p x y lane.sourceNode).w)
    (htx : (boxRect p x y lane.targetNode).x ≤ lane.targetX ∧
      lane.targetX ≤ (boxRect p x y lane.targetNode).x + (boxRect p x y lane.targetNode).w)
    (hcs : top.getD lane.sourceGap 0 + (layers.map (RouteImpl.layerHeight p)).getD lane.sourceGap 0 ≤
        reverseRunMid slot top (layers.map (RouteImpl.layerHeight p)) lr.routing lane.sourceGap lane.sourceSegment ∧
      reverseRunMid slot top (layers.map (RouteImpl.layerHeight p)) lr.routing lane.sourceGap lane.sourceSegment ≤
        top.getD (lane.sourceGap + 1) 0)
    (hct : top.getD lane.targetGap 0 + (layers.map (RouteImpl.layerHeight p)).getD lane.targetGap 0 ≤
        reverseRunMid slot top (layers.map (RouteImpl.layerHeight p)) lr.routing lane.targetGap lane.targetSegment ∧
      reverseRunMid slot top (layers.map (RouteImpl.layerHeight p)) lr.routing lane.targetGap lane.targetSegment ≤
        top.getD (lane.targetGap + 1) 0)
    (htrun : (frameKind p lane.targetNode ≠ -2 ∧ lane.targetRun = lane.targetX) ∨
      (frameKind p lane.targetNode = -2 ∧
        lane.targetRun = xAt x lane.targetNode - Int.fdiv (nodeW p lane.targetNode) 2))
    (hlane : VerticalTrunkClear (boxRect p x y v) lane.lane
      (reverseRunMid slot top (layers.map (RouteImpl.layerHeight p)) lr.routing lane.sourceGap lane.sourceSegment)
      (reverseRunMid slot top (layers.map (RouteImpl.layerHeight p)) lr.routing lane.targetGap lane.targetSegment)) :
    ¬ Polyline.hitsRect native.points (boxRect p x y v) := by
  by_cases hvpos : 0 < nodeH p v
  · have hp : native.points = dedup (reversedPoints slot p y top
        (layers.map (RouteImpl.layerHeight p)) lr.routing lane) := by
      simp only [laneRouteOf, hf] at he
      split at he
      · exact (congrArg EdgeRoute.points (Except.ok.inj he)).symm
      · cases he
    rw [hp]
    apply Polyline.not_hits_of_allMiss
    rw [allSegsMiss_iff]
    apply pairsAll_dedup
    rw [← allSegsMiss_iff]
    have hy : tailPortY p y lane.targetNode = yAt y lane.targetNode + nodeH p lane.targetNode := by
      by_cases htop : frameKind p lane.targetNode = -2
      · have hflat : RouteImpl.nodeH p lane.targetNode = 0 :=
          hG.frame_flat lane.targetNode ht (Or.inl htop)
        rw [tailPortY, ite_eq_left htop, hflat, Int.add_zero]
      · rw [tailPortY, ite_eq_right htop]
    simp only [reversedPoints, hy]
    exact reversedSevenPoint_avoids_either (G := routeGeo p layers x y top)
      hG hs ht hv hvs hvt hvpos hsr htr htg hsx htx htrun hcs.1 hcs.2 hct.1 hct.2 hlane
  · intro hh
    exact hvpos hh.2.1

set_option maxHeartbeats 800000 in
/-- The actual retained forward segment pays for its numbered slot even when
    other segments in the gap are reserved reversed lanes. -/
theorem activeForward_midBounds {slot rankGap : Int} {p : Proper}
    {layers : List (List Nat)} {x top : List Int} {rev : List Bool}
    {widths : List Int} {reserved : List (Option Int)} {lr : LaneRouting}
    (hr : routeWithLanesR slot p layers x rev widths reserved = .ok lr)
    (hslot : 1 ≤ slot) (hhalf : Int.fdiv slot 2 ≤ rankGap) {i : Nat}
    (hi : i < p.edges.length) (hrev : rev.getD (edgeAt p i).original false = false)
    (hne : runOf lr.routing i ≠ lr.routing.targetX.getD i 0)
    (hstep : top.getD (gapOf p i) 0 + (layers.map (RouteImpl.layerHeight p)).getD (gapOf p i) 0 +
      rankGap + slot * (lr.routing.gaps.getD (gapOf p i) default).slots ≤
        top.getD (gapOf p i + 1) 0) :
    top.getD (gapOf p i) 0 + (layers.map (RouteImpl.layerHeight p)).getD (gapOf p i) 0 ≤
      midOf p slot top (layers.map (RouteImpl.layerHeight p)) lr.routing i ∧
    midOf p slot top (layers.map (RouteImpl.layerHeight p)) lr.routing i ≤
      top.getD (gapOf p i + 1) 0 := by
  obtain ⟨base, hb, _, rfl⟩ := routeWithLanesR_spec hr
  have hk := (route_segment_facts hb hi).1
  have hg : gapOf p i < base.gaps.length := by
    have he := (route_spec hb).2.2.2.2.2.1
    simp only [he, List.length_map, List.length_range]
    omega
  have hm := forward_retained (base := base)
    (runs := plannedLanesR slot p base x rev widths reserved) hi hrev
  apply lane_mid_bounds_of_retained (layers := layers) (top := top) (reversed := rev)
    (runs := plannedLanesR slot p base x rev widths reserved) hi hg hslot hhalf hstep hm
  let raw := laneGapSegments p base rev (plannedLanesR slot p base x rev widths reserved) (gapOf p i)
  have hex : ∃ s ∈ raw, s.edges.contains i = true := by
    obtain ⟨s, hs, he⟩ := hm
    exact ⟨s, hs, by simpa using he⟩
  have hj := List.findIdx_lt_length_of_exists hex
  have hf := List.findIdx?_eq_some_of_exists hex
  have hp := List.findIdx_getElem (w := hj)
  have ee : raw.getD (raw.findIdx fun s => s.edges.contains i) default =
      raw[raw.findIdx fun s => s.edges.contains i] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have he : i ∈ (raw.getD (raw.findIdx fun s => s.edges.contains i) default).edges := by
    rw [ee]; simpa using hp
  have hm' : raw.getD (raw.findIdx fun s => s.edges.contains i) default ∈ raw := by
    rw [ee]; exact List.getElem_mem hj
  have pr := retained_ports hb hm' he
  rw [hf]
  simp only [Option.getD_some]
  rw [segStraight_false, pr.1, pr.2]
  exact hne

theorem activeForward_pieceMiss {slot gap : Int} {rankGap : Nat → Int} {p : Proper}
    {layers : List (List Nat)} {x y top : List Int} {rev : List Bool}
    {widths : List Int} {reserved : List (Option Int)} {lr : LaneRouting}
    (hr : routeWithLanesR slot p layers x rev widths reserved = .ok lr)
    (hF : CoordFacts p layers x y top lr.routing gap rankGap slot) {v : Nat}
    (hv : v < p.nodes.length) (hvpos : 0 < nodeH p v) {i : Nat} (hi : i < p.edges.length)
    (hrev : rev.getD (edgeAt p i).original false = false)
    (hvt : (edgeAt p i).tail ≠ v) (hvh : (edgeAt p i).head ≠ v) {pc : List Point}
    (hpc : pieceOf p slot y top (layers.map (RouteImpl.layerHeight p)) lr.routing i = .ok pc) :
    pairsAll (fun P Q => Polyline.segMisses P Q (boxRect p x y v)) pc := by
  obtain ⟨base, hb, _, heq⟩ := routeWithLanesR_spec hr
  have hl := (route_spec hb).1
  have hG := geo_ok_of_layers hl (fun _ hk => activeGap_nonneg hr hk) hF
  obtain ⟨_, _, _, _, hedge⟩ := layersOk_spec hl
  obtain ⟨ht, hh, hrk⟩ := hedge i hi
  have pr := port_ranges hb hi
  have hs : lr.routing.sourceX = base.sourceX := by rw [heq]; rfl
  have htgt : lr.routing.targetX = base.targetX := by rw [heq]; rfl
  have hrunr : lr.routing.sourceRun = base.sourceRun := by rw [heq]; rfl
  have hrn : runOf lr.routing i = runOf base i := by unfold runOf; rw [hrunr]
  have hrun : (frameKind p (edgeAt p i).tail ≠ -2 ∧
        runOf lr.routing i = lr.routing.sourceX.getD i 0) ∨
      (frameKind p (edgeAt p i).tail = -2 ∧
        runOf lr.routing i = xAt x (edgeAt p i).tail -
          Int.fdiv (nodeW p (edgeAt p i).tail) 2) := by
    rw [hrn, hs]
    exact run_cases hb hi
  rw [← hs, ← htgt] at pr
  have hrk' : (routeGeo p layers x y top).rk (edgeAt p i).head =
      (routeGeo p layers x y top).rk (edgeAt p i).tail + 1 := by
    show (Elegant.Layered.rk p.rank (edgeAt p i).head).toNat =
      (Elegant.Layered.rk p.rank (edgeAt p i).tail).toNat + 1
    have hcov := (layersOk_spec hl).2.2.2.1
    obtain ⟨_, _, _, h0⟩ := hcov _ ht
    omega
  have hc := pieceOf_cases hpc
  apply piece_miss (G := routeGeo p layers x y top) hG ht hh hv hrk' (Ne.symm hvt)
    (Ne.symm hvh) hvpos (sx := lr.routing.sourceX.getD i 0) (run := runOf lr.routing i)
    (tx := lr.routing.targetX.getD i 0) ⟨pr.1, pr.2.1⟩ hrun ⟨pr.2.2.1, pr.2.2.2⟩
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · have hk := (route_segment_facts hb hi).1
    obtain ⟨l, hl'⟩ : ∃ l, layers[gapOf p i]? = some l :=
      ⟨layers[gapOf p i]'(by omega), List.getElem?_eq_getElem _⟩
    have hstep : top.getD (gapOf p i) 0 + (layers.map (RouteImpl.layerHeight p)).getD (gapOf p i) 0 +
        rankGap (gapOf p i) + slot * (lr.routing.gaps.getD (gapOf p i) default).slots ≤
        top.getD (gapOf p i + 1) 0 := by
      have hband := hF.band_step (gapOf p i) l hl' hk
      rw [RouteImpl.heights_getD hl']
      omega
    have hm := activeForward_midBounds hr hF.slot_pos (hF.half_slot_le _) hi hrev h2 hstep
    exact Or.inr ⟨midOf p slot top (layers.map (RouteImpl.layerHeight p)) lr.routing i, hm.1, hm.2, h1⟩

theorem activeForward_nativeMiss {slot gap : Int} {rankGap : Nat → Int} {p : Proper}
    {layers : List (List Nat)} {x y top : List Int} {rev : List Bool}
    {widths : List Int} {reserved : List (Option Int)} {lr : LaneRouting} {native : EdgeRoute}
    (hP : ProperShape p)
    (hr : routeWithLanesR slot p layers x rev widths reserved = .ok lr)
    (hF : CoordFacts p layers x y top lr.routing gap rankGap slot)
    (hf : lr.runs.find? (fun lane => lane.original == native.original) = none)
    (he : laneRouteOf slot p y top (layers.map (RouteImpl.layerHeight p)) lr native.original = .ok native)
    (hi : native.original < p.chains.length)
    {first last : Nat}
    (hfirst : (edgesOf p native.original).head? = some first)
    (hlast : (edgesOf p native.original).getLast? = some last)
    {v : Nat} (hv : v < p.nodes.length) (hreal : IsReal p v)
    (hv0 : v ≠ (edgeAt p first).tail) (hv1 : v ≠ (edgeAt p last).head) :
    ¬ Polyline.hitsRect native.points (boxRect p x y v) := by
  by_cases hvpos : 0 < nodeH p v
  · have hneChain : (edgesOf p native.original).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff]
      exact List.ne_nil_of_mem (RouteImpl.mem_of_head' hfirst)
    have hrev := activeForward_reversed_false hr hi hneChain hf
    have hne := chain_ne hreal (edgesOf p native.original) (hP _)
      (fun i' hi' => by
        rw [hfirst] at hi'
        have e := Option.some.inj hi'
        rw [← e]
        exact Ne.symm hv0)
      (fun i' hi' => by
        rw [hlast] at hi'
        have e := Option.some.inj hi'
        rw [← e]
        exact Ne.symm hv1)
    obtain ⟨base, hb, _, hlr⟩ := routeWithLanesR_spec hr
    have hl := (route_spec hb).1
    have hG := geo_ok_of_layers hl (fun _ hk => activeGap_nonneg hr hk) hF
    have hedge := (layersOk_spec hl).2.2.2.2
    simp only [laneRouteOf, hf] at he
    unfold routeOf at he
    split at he
    · simp at he
    · next pcs hpcs =>
      simp only [Except.ok.injEq] at he
      have hpts := congrArg EdgeRoute.points he
      rw [← hpts]
      dsimp only
      apply Polyline.not_hits_of_allMiss
      rw [allSegsMiss_iff]
      apply pairsAll_dedup
      refine pairsAll_flatten_of (fun P Q => Polyline.segMisses P Q (boxRect p x y v))
        (pieceStart p y lr.routing) (pieceEnd p y lr.routing) (ChainLink p) ?_
        (edgesOf p native.original) pcs ?_ (hP native.original)
      · intro i j hij
        obtain ⟨hi, hj, hhead, nd, hnd, hdum⟩ := hij
        have hd : (edgeAt p j).tail < p.nodes.length := (hedge j hj).1
        have hvd : v ≠ (edgeAt p j).tail := by
          intro heq
          have hfalse := hreal nd (by rw [heq]; exact hnd)
          rw [hfalse] at hdum
          exact absurd hdum (by decide)
        have pi := port_ranges hb hi
        have pj := port_ranges hb hj
        have hs : lr.routing.sourceX = base.sourceX := by rw [hlr]; rfl
        have ht : lr.routing.targetX = base.targetX := by rw [hlr]; rfl
        rw [hhead] at pi
        have hfk : frameKind p (edgeAt p j).tail = 0 := frameKind_of_chain ⟨nd, hnd, hdum⟩
        have hnt : (routeGeo p layers x y top).bd (edgeAt p j).tail ≠ -2 := by
          show frameKind p (edgeAt p j).tail ≠ -2
          rw [hfk]
          decide
        have hmiss := junction_miss (G := routeGeo p layers x y top) hG hd hv hvd hnt hvpos
          (tx := base.targetX.getD i 0) (sx := base.sourceX.getD j 0)
          ⟨pi.2.2.1, pi.2.2.2⟩ ⟨pj.1, pj.2.1⟩
        have hps : pieceStart p y lr.routing j =
            ⟨base.sourceX.getD j 0, (routeGeo p layers x y top).yv (edgeAt p j).tail +
              (routeGeo p layers x y top).hv (edgeAt p j).tail⟩ := by
          simp [pieceStart, routeGeo, hfk, hs]
        have hpe : pieceEnd p y lr.routing i =
            ⟨base.targetX.getD i 0, (routeGeo p layers x y top).yv (edgeAt p j).tail⟩ := by
          simp [pieceEnd, routeGeo, hhead, ht]
        rw [hps, hpe, boxRect]
        exact hmiss
      · exact Zipped.imp _ _ (fun i hi pc hpc =>
          have hm := Elegant.Layered.PipelineImpl.mem_edgesOf.mp hi
          ⟨(pieceOf_basic hpc).1, (pieceOf_basic hpc).2.1,
            activeForward_pieceMiss hr hF hv hvpos hm.1
              (by rw [hm.2]; exact hrev) (hne i hi).1 (hne i hi).2 hpc⟩)
          (mapOk_zipped _ _ _ hpcs)
  · intro hh
    exact hvpos hh.2.1


/-- Same reversed-lane port/rank data as in `laneRun_node_facts`: the parked
    x coordinate is irrelevant to these facts. -/
theorem activeReverse_nodeFacts {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x : List Int} {rev : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {lr : LaneRouting} {lane : ReversedLane}
    (hr : routeWithLanesR slot p layers x rev widths reserved = .ok lr)
    (hm : lane ∈ lr.runs) {first last : Nat}
    (hfirst : (edgesOf p lane.original).head? = some first)
    (hlast : (edgesOf p lane.original).getLast? = some last) :
    lane.sourceNode = (edgeAt p last).head ∧ lane.targetNode = (edgeAt p first).tail ∧
    lane.sourceNode < p.nodes.length ∧ lane.targetNode < p.nodes.length ∧
    (rk p.rank lane.sourceNode).toNat = lane.sourceGap + 1 ∧
    (rk p.rank lane.targetNode).toNat = lane.targetGap ∧
    lane.sourceGap + 1 < layers.length ∧ lane.targetGap + 1 < layers.length ∧
    leftOf p x lane.sourceNode ≤ lane.sourceX ∧
    lane.sourceX ≤ leftOf p x lane.sourceNode + nodeW p lane.sourceNode ∧
    leftOf p x lane.targetNode ≤ lane.targetX ∧
    lane.targetX ≤ leftOf p x lane.targetNode + nodeW p lane.targetNode ∧
    ((frameKind p lane.targetNode ≠ -2 ∧ lane.targetRun = lane.targetX) ∨
      (frameKind p lane.targetNode = -2 ∧ lane.targetRun = leftOf p x lane.targetNode)) := by
  obtain ⟨base, hb, _, hlr⟩ := routeWithLanesR_spec hr
  have hmem : lane ∈ plannedLanesR slot p base x rev widths reserved := by
    rw [hlr] at hm
    exact hm
  obtain ⟨hsx, htx, hs, ht, hsg, htg, htr⟩ := rcbPlannedLaneR_endpoints hmem hfirst hlast
  have hf := RouteImpl.mem_edgesOf (mem_of_head' hfirst)
  have hl := RouteImpl.mem_edgesOf (List.mem_of_getLast? hlast)
  obtain ⟨_, _, _, hcov, hedge⟩ := layersOk_spec (route_spec hb).1
  obtain ⟨hft, _, _⟩ := hedge first hf
  obtain ⟨hlt, hlh, hlrank⟩ := hedge last hl
  obtain ⟨_, _, _, hnonneg⟩ := hcov _ hlt
  have hsourceRank : (rk p.rank (edgeAt p last).head).toNat = gapOf p last + 1 := by
    unfold gapOf
    omega
  have htargetRank : (rk p.rank (edgeAt p first).tail).toNat = gapOf p first := rfl
  have hpf := port_ranges hb hf
  have hpl := port_ranges hb hl
  refine ⟨hs, ht, by rwa [hs], by rwa [ht], by rwa [hs, hsg], by rwa [ht, htg],
    by rw [hsg]; exact (route_segment_facts hb hl).1,
    by rw [htg]; exact (route_segment_facts hb hf).1,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hs, hsx, leftOf] using hpl.2.2.1
  · simpa only [hs, hsx, leftOf] using hpl.2.2.2
  · simpa only [ht, htx, leftOf] using hpf.1
  · simpa only [ht, htx, leftOf] using hpf.2.1
  · simpa only [ht, htx, htr, leftOf, runOf] using run_cases hb hf

private theorem kahn_straight_slot (n : Nat) (arc : Nat → Nat → Bool) (decl : Nat → Nat)
    (straight : Nat → Bool) (index : Nat) (hstraight : straight index = true)
    (fuel : Nat) (done : List Nat) (slots : Nat → Int) (hslot : slots index = -1) :
    kahn n arc decl straight fuel done slots index = -1 := by
  induction fuel generalizing done slots with
  | zero => exact hslot
  | succ fuel ih =>
    simp only [kahn]
    cases hp : kahnPick n arc decl done with
    | none => exact hslot
    | some v =>
      refine ih (v :: done) _ ?_
      by_cases he : index = v
      · subst v
        simp [kahnValue, hstraight]
      · simp [he, hslot]

/-- Both straight and nonstraight lane gap segments have a usable midline.
    The exact router can rule out straight lane segments by its outer-lane
    bound; the reserved router need not. -/
theorem activeReverse_mid_of_get {slot rankGap : Int} {top heights : List Int}
    {routing : Routing} {gap index : Nat} {segs : List RoutingSegment} {seg : RoutingSegment}
    (hgap : routing.gaps.getD gap default = numberLaneGap segs)
    (hget : segs[index]? = some seg)
    (hslot : 1 ≤ slot) (hhalf : Int.fdiv slot 2 ≤ rankGap)
    (hstep : top.getD gap 0 + heights.getD gap 0 + rankGap +
      slot * (routing.gaps.getD gap default).slots ≤ top.getD (gap + 1) 0) :
    top.getD gap 0 + heights.getD gap 0 ≤ reverseRunMid slot top heights routing gap index ∧
      reverseRunMid slot top heights routing gap index ≤ top.getD (gap + 1) 0 := by
  have hgetD : segs.getD index default = seg := by
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  cases hstraight : segStraight seg with
  | false =>
    have hne := segStraight_false.mp hstraight
    have hs := numberLaneGap_at_bounds hget hne
    exact reverseRunMid_bounds hslot hhalf (by rw [hgap]; exact hs.1)
      (by rw [hgap]; exact hs.2) hstep
  | true =>
    have hs : numberLaneSlots segs index = -1 := by
      unfold numberLaneSlots
      apply kahn_straight_slot
      · rw [hgetD]
        exact hstraight
      · rfl
    have hmid : reverseRunMid slot top heights routing gap index =
        top.getD gap 0 + heights.getD gap 0 + Int.fdiv slot 2 := by
      unfold reverseRunMid
      rw [hgap, numberLaneGap_at hget, hs] <;> simp
    have hhalfNN := Int.fdiv_nonneg (by omega : 0 ≤ slot) (by decide : 0 ≤ (2 : Int))
    have hnn : 0 ≤ (routing.gaps.getD gap default).slots := by
      rw [hgap]
      exact numberLaneGap_nonneg segs
    have hmul := Int.mul_nonneg (by omega : 0 ≤ slot) hnn
    rw [hmid]
    omega

private theorem plannedPrefixR_length (slot : Int) (p : Proper) (base : Routing)
    (x : List Int) (rev : List Bool) (widths : List Int) (reserved : List (Option Int))
    (originals xs : List Nat) (start gap : Nat) :
    ((xs.zipIdx start).map (fun q => makeLaneR slot p base x rev widths reserved
      originals q.1 q.2) |>.flatMap (fun lane => laneRunSegments p lane gap)).length =
        runGapCount p xs gap := by
  induction xs generalizing start with
  | nil => simp [runGapCount]
  | cons a xs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.flatMap_cons, List.length_append]
    rw [ih]
    simp only [laneRunSegments, makeLaneR, List.length_append]
    have hc := runGapCount_acc p xs gap
      ((0 + if gapOf p ((edgesOf p a).getLast?.getD 0) = gap then 1 else 0) +
        if gapOf p ((edgesOf p a).headD 0) = gap then 1 else 0)
    change runGapCount p (a :: xs) gap = _ at hc
    rw [hc]
    by_cases hs : gapOf p ((edgesOf p a).getLast?.getD 0) = gap <;>
      by_cases ht : gapOf p ((edgesOf p a).headD 0) = gap <;>
        simp only [hs, ht, ite_true, ite_false, List.length_cons, List.length_nil] <;> omega

/-- The stored source/target segment indices select exactly those entries of
    the executed reversed lane gap list, regardless of its parked coordinate. -/
theorem activeReverse_rawSegments {slot : Int} {p : Proper} {base : Routing} {x : List Int}
    {rev : List Bool} {widths : List Int} {reserved : List (Option Int)} {lane : ReversedLane}
    (hm : lane ∈ plannedLanesR slot p base x rev widths reserved) :
    (laneGapSegments p base rev (plannedLanesR slot p base x rev widths reserved)
      lane.sourceGap)[lane.sourceSegment]? =
        some (laneSegment p lane.original 0 lane.sourceX lane.lane) ∧
    (laneGapSegments p base rev (plannedLanesR slot p base x rev widths reserved)
      lane.targetGap)[lane.targetSegment]? =
        some (laneSegment p lane.original 1 lane.targetRun lane.lane) := by
  let originals := laneOriginals p rev
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hq
  have hib : i < originals.length := by simpa only [List.length_zipIdx] using hi
  rw [List.getElem_zipIdx] at hqi
  subst q
  let before := originals.take i
  let after := originals.drop (i + 1)
  let original := originals[i]'hib
  have ho : originals = before ++ original :: after := by
    symm
    change originals.take i ++ originals[i] :: originals.drop (i + 1) = originals
    rw [List.getElem_cons_drop hib, List.take_append_drop]
  have hbefore : before.length = i := by
    simp [before, List.length_take, Nat.min_eq_left (Nat.le_of_lt hib)]
  let make := fun q : Nat × Nat =>
    makeLaneR slot p base x rev widths reserved originals q.1 q.2
  let run := make (original, before.length)
  have hrun : lane = run := by
    simpa only [make, run, hbefore, original, Nat.zero_add] using heq.symm
  let pre := before.zipIdx.map make
  let post := (after.zipIdx (before.length + 1)).map make
  have hp : plannedLanesR slot p base x rev widths reserved = pre ++ run :: post := by
    change originals.zipIdx.map make = pre ++ run :: post
    have hz : originals.zipIdx = (before ++ original :: after).zipIdx :=
      congrArg (fun xs : List Nat => xs.zipIdx) ho
    rw [hz]
    simp [List.zipIdx_append, pre, post, run]
  have hcount (gap : Nat) :
      (pre.flatMap (fun r => laneRunSegments p r gap)).length =
        runGapCount p before gap :=
    plannedPrefixR_length slot p base x rev widths reserved originals before 0 gap
  have htOrig : originals.take before.length = before := by
    rw [ho]
    simp
  have hs : run.sourceSegment =
      (forwardGapSegments p base rev run.sourceGap ++
        pre.flatMap (fun r => laneRunSegments p r run.sourceGap)).length := by
    rw [List.length_append, hcount]
    simp only [run, make, makeLaneR, htOrig]
  have ht : run.targetSegment =
      (forwardGapSegments p base rev run.targetGap ++
        pre.flatMap (fun r => laneRunSegments p r run.targetGap)).length +
          if run.sourceGap = run.targetGap then 1 else 0 := by
    rw [List.length_append, hcount]
    simp only [run, make, makeLaneR, htOrig]
  rw [hrun, hp]
  simp only [laneGapSegments_split]
  constructor
  · rw [hs, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp [laneRunSegments]
  · rw [ht, List.append_assoc, List.getElem?_append_right (by omega)]
    by_cases he : run.sourceGap = run.targetGap <;> simp [laneRunSegments, he]


end Elegant.Layered.PipelineImpl.RegionOrdinaryC6

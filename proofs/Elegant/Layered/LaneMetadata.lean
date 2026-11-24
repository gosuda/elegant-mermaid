import Elegant.Layered.Route

set_option autoImplicit false

namespace Elegant.Layered.RouteImpl

def laneRunSegments (p : Proper) (run : ReversedLane) (gap : Nat) : List RoutingSegment :=
  (if run.sourceGap = gap then [laneSegment p run.original 0 run.sourceX run.lane] else []) ++
  (if run.targetGap = gap then [laneSegment p run.original 1 run.targetRun run.lane] else [])

theorem runGapCount_acc (p : Proper) (xs : List Nat) (gap n : Nat) :
    xs.foldl (fun n o =>
      n + (if gapOf p ((edgesOf p o).getLast?.getD 0) = gap then 1 else 0) +
        (if gapOf p ((edgesOf p o).headD 0) = gap then 1 else 0)) n =
      n + runGapCount p xs gap := by
  induction xs generalizing n with
  | nil => simp [runGapCount]
  | cons a xs ih =>
    change xs.foldl _ _ = n + xs.foldl _ _
    rw [ih, ih]
    simp only [Nat.zero_add, Nat.add_assoc]

theorem plannedPrefix_length (slot : Int) (p : Proper) (base : Routing) (x : List Int)
    (reversed : List Bool) (widths : List Int) (xs : List Nat) (start gap : Nat) :
    ((xs.zipIdx start).map (fun q => makeLane slot p base x reversed widths q.1 q.2) |>.flatMap
      (fun run => laneRunSegments p run gap)).length = runGapCount p xs gap := by
  induction xs generalizing start with
  | nil => simp [runGapCount]
  | cons a xs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.flatMap_cons, List.length_append]
    rw [ih]
    simp only [laneRunSegments, makeLane, List.length_append]
    change _ + runGapCount p xs gap = _
    have hc := runGapCount_acc p xs gap
      ((0 + if gapOf p ((edgesOf p a).getLast?.getD 0) = gap then 1 else 0) +
        if gapOf p ((edgesOf p a).headD 0) = gap then 1 else 0)
    change runGapCount p (a :: xs) gap = _ at hc
    rw [hc]
    by_cases hs : gapOf p ((edgesOf p a).getLast?.getD 0) = gap <;>
      by_cases ht : gapOf p ((edgesOf p a).headD 0) = gap <;>
        simp only [hs, ht, ite_true, ite_false, List.length_cons, List.length_nil] <;> omega

theorem laneGapSegments_split (p : Proper) (base : Routing) (reversed : List Bool)
    (before after : List ReversedLane) (run : ReversedLane) (gap : Nat) :
    laneGapSegments p base reversed (before ++ run :: after) gap =
      (forwardGapSegments p base reversed gap ++ before.flatMap (fun r => laneRunSegments p r gap)) ++
        laneRunSegments p run gap ++ after.flatMap (fun r => laneRunSegments p r gap) := by
  simp [laneGapSegments, laneRunSegments, List.flatMap_append, List.append_assoc]


theorem plannedLanes_split {slot : Int} {p : Proper} {base : Routing} {x : List Int}
    {reversed : List Bool} {widths : List Int} {run : ReversedLane}
    (hm : run ∈ plannedLanes slot p base x reversed widths) :
    ∃ before after o,
      laneOriginals p reversed = before ++ o :: after ∧
      run = makeLane slot p base x reversed widths o before.length := by
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hq
  have hlen : i < (laneOriginals p reversed).length := by simpa using hi
  rw [List.getElem_zipIdx] at hqi
  subst q
  refine ⟨(laneOriginals p reversed).take i, (laneOriginals p reversed).drop (i + 1),
    (laneOriginals p reversed)[i], ?_, ?_⟩
  · rw [List.getElem_cons_drop hlen, List.take_append_drop]
  · simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlen)] using heq.symm

theorem plannedLane_raw_segments {slot : Int} {p : Proper} {base : Routing} {x : List Int}
    {reversed : List Bool} {widths : List Int} {run : ReversedLane}
    (hm : run ∈ plannedLanes slot p base x reversed widths) :
    (laneGapSegments p base reversed (plannedLanes slot p base x reversed widths)
      run.sourceGap)[run.sourceSegment]? =
        some (laneSegment p run.original 0 run.sourceX run.lane) ∧
    (laneGapSegments p base reversed (plannedLanes slot p base x reversed widths)
      run.targetGap)[run.targetSegment]? =
        some (laneSegment p run.original 1 run.targetRun run.lane) := by
  obtain ⟨before, after, o, ho, rfl⟩ := plannedLanes_split hm
  let run := makeLane slot p base x reversed widths o before.length
  let pre := (before.zipIdx).map fun q => makeLane slot p base x reversed widths q.1 q.2
  let post := (after.zipIdx (before.length + 1)).map fun q =>
    makeLane slot p base x reversed widths q.1 q.2
  have hp : plannedLanes slot p base x reversed widths = pre ++ run :: post := by
    simp [plannedLanes, ho, List.zipIdx_append, pre, post, run]
  have hcount (gap : Nat) :
      (pre.flatMap (fun r => laneRunSegments p r gap)).length = runGapCount p before gap :=
    plannedPrefix_length slot p base x reversed widths before 0 gap
  have hs : run.sourceSegment =
      (forwardGapSegments p base reversed run.sourceGap ++
        pre.flatMap (fun r => laneRunSegments p r run.sourceGap)).length := by
    simp only [List.length_append, hcount]
    simp [run, makeLane, ho]
  have ht : run.targetSegment =
      (forwardGapSegments p base reversed run.targetGap ++
        pre.flatMap (fun r => laneRunSegments p r run.targetGap)).length +
          if run.sourceGap = run.targetGap then 1 else 0 := by
    simp only [List.length_append, hcount]
    simp [run, makeLane, ho]
  change (laneGapSegments p base reversed (plannedLanes slot p base x reversed widths)
    run.sourceGap)[run.sourceSegment]? = some (laneSegment p run.original 0 run.sourceX run.lane) ∧
    (laneGapSegments p base reversed (plannedLanes slot p base x reversed widths)
    run.targetGap)[run.targetSegment]? = some (laneSegment p run.original 1 run.targetRun run.lane)
  rw [hp]
  simp only [laneGapSegments_split]
  constructor
  · rw [hs, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp [laneRunSegments]
  · rw [ht, List.append_assoc, List.getElem?_append_right (by omega)]
    by_cases he : run.sourceGap = run.targetGap <;> simp [laneRunSegments, he]

theorem numberLaneGap_at {raw : List RoutingSegment} {i : Nat} {s : RoutingSegment}
    (hi : raw[i]? = some s) :
    (numberLaneGap raw).segments.getD i default =
      { s with slot := numberLaneSlots raw i } := by
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hi
  simp [numberLaneGap, List.getD_eq_getElem?_getD, he, hlt]

theorem numberLaneGap_at_bounds {raw : List RoutingSegment} {i : Nat} {s : RoutingSegment}
    (hi : raw[i]? = some s) (hne : s.sourceX ≠ s.targetX) :
    0 ≤ ((numberLaneGap raw).segments.getD i default).slot ∧
      ((numberLaneGap raw).segments.getD i default).slot + 1 ≤ (numberLaneGap raw).slots := by
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hi
  have hd : raw.getD i default = s := by
    simp [List.getD_eq_getElem?_getD, hi]
  have hb := numberLaneGap_slot_bounds hlt (by rw [hd]; simp [segStraight, hne])
  simpa only [numberLaneGap_at hi] using hb

theorem laneRun_gap_bounds {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x : List Int} {reversed : List Bool} {widths : List Int} {lr : LaneRouting}
    (hr : routeWithLanes slot p layers x reversed widths = .ok lr)
    {run : ReversedLane} (hm : run ∈ lr.runs) :
    run.sourceGap + 1 < layers.length ∧ run.targetGap + 1 < layers.length := by
  obtain ⟨hsv, _, hsr, _, htg, _⟩ := laneRun_node_facts hr hm
  obtain ⟨l, hl, _⟩ := (layersOk_spec (routeWithLanes_geometry hr).1).2.2.2.1 _ hsv
  have hi := List.getElem?_eq_some_iff.mp hl
  exact ⟨by rw [hsr] at hi; exact hi.1, htg⟩

theorem laneRun_slot_bounds {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x : List Int} {reversed : List Bool} {widths : List Int} {lr : LaneRouting}
    (hr : routeWithLanes slot p layers x reversed widths = .ok lr)
    {run : ReversedLane} (hm : run ∈ lr.runs) :
    (0 ≤ ((lr.routing.gaps.getD run.sourceGap default).segments.getD run.sourceSegment default).slot ∧
      ((lr.routing.gaps.getD run.sourceGap default).segments.getD run.sourceSegment default).slot + 1 ≤
        (lr.routing.gaps.getD run.sourceGap default).slots) ∧
    (0 ≤ ((lr.routing.gaps.getD run.targetGap default).segments.getD run.targetSegment default).slot ∧
      ((lr.routing.gaps.getD run.targetGap default).segments.getD run.targetSegment default).slot + 1 ≤
        (lr.routing.gaps.getD run.targetGap default).slots) := by
  have hg := laneRun_gap_bounds hr hm
  obtain ⟨hneSource, hneTarget⟩ := laneRun_port_ne_lane hr hm
  obtain ⟨base, hb, _, hlr⟩ := routeWithLanes_spec hr
  have hmem : run ∈ plannedLanes slot p base x reversed widths := by
    rw [hlr] at hm; exact hm
  have hraw := plannedLane_raw_segments hmem
  have hlen : base.gaps.length = layers.length - 1 := by
    rw [(route_spec hb).2.2.2.2.2.1]
    simp
  have hsource : run.sourceGap < base.gaps.length := by omega
  have htarget : run.targetGap < base.gaps.length := by omega
  have hget (gap : Nat) (hgap : gap < base.gaps.length) :
      lr.routing.gaps.getD gap default =
        numberLaneGap (laneGapSegments p base reversed
          (plannedLanes slot p base x reversed widths) gap) := by
    rw [hlr]
    simp [assembleLaneRouting, List.getD_eq_getElem?_getD, hgap]
  rw [hget _ hsource, hget _ htarget]
  exact ⟨numberLaneGap_at_bounds hraw.1 hneSource,
    numberLaneGap_at_bounds hraw.2 hneTarget⟩

theorem laneRun_mid_bounds {slot : Int} {rankGap : Nat → Int} {p : Proper}
    {layers : List (List Nat)} {x top : List Int} {reversed : List Bool}
    {widths : List Int} {lr : LaneRouting}
    (hr : routeWithLanes slot p layers x reversed widths = .ok lr)
    (hslot : 1 ≤ slot) (hhalf : ∀ k, Int.fdiv slot 2 ≤ rankGap k)
    (hstep : ∀ k, k + 1 < layers.length →
      top.getD k 0 + (layers.map (layerHeight p)).getD k 0 + rankGap k +
        slot * (lr.routing.gaps.getD k default).slots ≤ top.getD (k + 1) 0)
    {run : ReversedLane} (hm : run ∈ lr.runs) :
    (top.getD run.sourceGap 0 + (layers.map (layerHeight p)).getD run.sourceGap 0 ≤
      reverseRunMid slot top (layers.map (layerHeight p)) lr.routing run.sourceGap run.sourceSegment ∧
      reverseRunMid slot top (layers.map (layerHeight p)) lr.routing run.sourceGap run.sourceSegment ≤
        top.getD (run.sourceGap + 1) 0) ∧
    (top.getD run.targetGap 0 + (layers.map (layerHeight p)).getD run.targetGap 0 ≤
      reverseRunMid slot top (layers.map (layerHeight p)) lr.routing run.targetGap run.targetSegment ∧
      reverseRunMid slot top (layers.map (layerHeight p)) lr.routing run.targetGap run.targetSegment ≤
        top.getD (run.targetGap + 1) 0) := by
  have hg := laneRun_gap_bounds hr hm
  have hslots := laneRun_slot_bounds hr hm
  exact ⟨reverseRunMid_bounds hslot (hhalf run.sourceGap) hslots.1.1 hslots.1.2
      (hstep _ hg.1),
    reverseRunMid_bounds hslot (hhalf run.targetGap) hslots.2.1 hslots.2.2
      (hstep _ hg.2)⟩

theorem laneRun_numbered_segments {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x : List Int} {reversed : List Bool} {widths : List Int} {lr : LaneRouting}
    (hr : routeWithLanes slot p layers x reversed widths = .ok lr)
    {run : ReversedLane} (hm : run ∈ lr.runs) :
    ∃ base, route p layers x = .ok base ∧
      let raw := laneGapSegments p base reversed (plannedLanes slot p base x reversed widths)
      (lr.routing.gaps.getD run.sourceGap default).segments.getD run.sourceSegment default =
        { laneSegment p run.original 0 run.sourceX run.lane with
          slot := numberLaneSlots (raw run.sourceGap) run.sourceSegment } ∧
      (lr.routing.gaps.getD run.targetGap default).segments.getD run.targetSegment default =
        { laneSegment p run.original 1 run.targetRun run.lane with
          slot := numberLaneSlots (raw run.targetGap) run.targetSegment } := by
  have hg := laneRun_gap_bounds hr hm
  obtain ⟨base, hb, _, hlr⟩ := routeWithLanes_spec hr
  have hmem : run ∈ plannedLanes slot p base x reversed widths := by
    rw [hlr] at hm; exact hm
  have hraw := plannedLane_raw_segments hmem
  have hlen : base.gaps.length = layers.length - 1 := by
    rw [(route_spec hb).2.2.2.2.2.1]
    simp
  have hget (k : Nat) (hk : k + 1 < layers.length) :
      lr.routing.gaps.getD k default =
        numberLaneGap (laneGapSegments p base reversed
          (plannedLanes slot p base x reversed widths) k) := by
    have hlt : k < base.gaps.length := by omega
    rw [hlr]
    simp [assembleLaneRouting, List.getD_eq_getElem?_getD, hlt]
  refine ⟨base, hb, ?_⟩
  dsimp only
  rw [hget _ hg.1, hget _ hg.2]
  exact ⟨numberLaneGap_at hraw.1, numberLaneGap_at hraw.2⟩

end Elegant.Layered.RouteImpl

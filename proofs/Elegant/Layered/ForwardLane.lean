import Elegant.Layered.Route

set_option autoImplicit false

namespace Elegant.Layered.RouteImpl

 theorem lane_selected_numbered {p : Proper} {base : Routing} {reversed : List Bool}
    {runs : List ReversedLane} {i : Nat} (hi : i < p.edges.length)
    (hg : gapOf p i < base.gaps.length)
    (hm : ∃ s ∈ laneGapSegments p base reversed runs (gapOf p i), i ∈ s.edges) :
    let raw := laneGapSegments p base reversed runs (gapOf p i)
    let j := (raw.findIdx? fun s => s.edges.contains i).getD 0
    j < raw.length ∧
      ((assembleLaneRouting p base reversed runs).routing.gaps.getD (gapOf p i) default).segments.getD
        ((assembleLaneRouting p base reversed runs).routing.segment.getD i 0) default =
          { raw.getD j default with slot := numberLaneSlots raw j } := by
  dsimp only
  let raw := laneGapSegments p base reversed runs (gapOf p i)
  have hex : ∃ s ∈ raw, (s.edges.contains i) = true := by
    obtain ⟨s, hs, he⟩ := hm
    exact ⟨s, hs, by simpa using he⟩
  have hf := List.findIdx?_eq_some_of_exists hex
  have hj := List.findIdx_lt_length_of_exists hex
  have hseg : (assembleLaneRouting p base reversed runs).routing.segment.getD i 0 =
      (raw.findIdx? fun s => s.edges.contains i).getD 0 :=
    getD_map_range _ _ _ hi _
  have hgap : (assembleLaneRouting p base reversed runs).routing.gaps.getD (gapOf p i) default =
      numberLaneGap raw := getD_map_range _ _ _ hg _
  change (raw.findIdx? fun s => s.edges.contains i).getD 0 < raw.length ∧ _
  rw [hf]
  simp only [Option.getD_some]
  refine ⟨hj, ?_⟩
  rw [hseg, hgap, hf]
  simp only [Option.getD_some, numberLaneGap]
  exact getD_map_range _ _ _ hj _

 theorem lane_mid_bounds_of_retained {slot gap : Int} {rankGap : Nat → Int} {p : Proper}
    {layers : List (List Nat)} {x y top : List Int} {base : Routing}
    {reversed : List Bool} {runs : List ReversedLane} {i : Nat}
    (hi : i < p.edges.length) (hg : gapOf p i < base.gaps.length)
    (hk : gapOf p i + 1 < layers.length)
    (hF : CoordFacts p layers x y top (assembleLaneRouting p base reversed runs).routing
      gap rankGap slot)
    (hm : ∃ s ∈ laneGapSegments p base reversed runs (gapOf p i), i ∈ s.edges)
    (hs : segStraight ((laneGapSegments p base reversed runs (gapOf p i)).getD
      (((laneGapSegments p base reversed runs (gapOf p i)).findIdx?
        fun s => s.edges.contains i).getD 0) default) = false) :
    top.getD (gapOf p i) 0 + (layers.map (layerHeight p)).getD (gapOf p i) 0 ≤
      midOf p slot top (layers.map (layerHeight p))
        (assembleLaneRouting p base reversed runs).routing i ∧
    midOf p slot top (layers.map (layerHeight p))
      (assembleLaneRouting p base reversed runs).routing i ≤ top.getD (gapOf p i + 1) 0 := by
  obtain ⟨hj, he⟩ := lane_selected_numbered hi hg hm
  have bounds := numberLaneGap_slot_bounds hj hs
  have hgap : (assembleLaneRouting p base reversed runs).routing.gaps.getD (gapOf p i) default =
      numberLaneGap (laneGapSegments p base reversed runs (gapOf p i)) :=
    getD_map_range _ _ _ hg _
  obtain ⟨l, hl⟩ : ∃ l, layers[gapOf p i]? = some l :=
    ⟨layers[gapOf p i]'(by omega), List.getElem?_eq_getElem _⟩
  have step := hF.band_step (gapOf p i) l hl hk
  have heights := heights_getD (p := p) hl
  have key := reverseRunMid_bounds (top := top) (heights := layers.map (layerHeight p))
    (r := (assembleLaneRouting p base reversed runs).routing) (gap := gapOf p i)
    (index := (assembleLaneRouting p base reversed runs).routing.segment.getD i 0)
    hF.slot_pos (hF.half_slot_le (gapOf p i))
    (by rw [he]; exact bounds.1)
    (by rw [he, hgap]; exact bounds.2)
    (by rw [heights]; exact step)
  exact key

end Elegant.Layered.RouteImpl

namespace Elegant.Layered.RouteImpl

theorem forward_retained {p : Proper} {base : Routing} {rev : List Bool}
    {runs : List ReversedLane} {i : Nat} (hi : i < p.edges.length)
    (hr : reversedEdge rev p i = false) :
    ∃ s ∈ laneGapSegments p base rev runs (gapOf p i), i ∈ s.edges := by
  let s := buildSegment p base.sourceRun base.targetX (gapOf p i) (segKey p i)
  have he : i ∈ s.edges := by simp [s, buildSegment, gapEdges, hi]
  have hm : s ∈ gapSegments p base.sourceRun base.targetX (gapOf p i) := by
    apply List.mem_map.mpr
    refine ⟨segKey p i, ?_, rfl⟩
    simp only [gapKeys, List.mem_eraseDups, List.mem_map]
    exact ⟨i, by simp [gapEdges, hi], rfl⟩
  have hf : i ∈ s.edges.filter (fun j => !reversedEdge rev p j) := by simp [he, hr]
  refine ⟨{s with
    edges := s.edges.filter (fun j => !reversedEdge rev p j)
    decl := minDecl ((s.edges.filter (fun j => !reversedEdge rev p j)).map
      (fun j => (edgeAt p j).decl))}, ?_, hf⟩
  apply List.mem_append_left
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨s, hm, rfl⟩, ?_⟩
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff]
  exact List.ne_nil_of_mem hf

end Elegant.Layered.RouteImpl

namespace Elegant.Layered.RouteImpl

theorem retained_ports {p : Proper} {base : Routing} {rev : List Bool}
    {runs : List ReversedLane} {x : List Int} {layers : List (List Nat)}
    (hb : route p layers x = .ok base) {i : Nat} {s : RoutingSegment}
    (hm : s ∈ laneGapSegments p base rev runs (gapOf p i)) (he : i ∈ s.edges) :
    s.sourceX = base.sourceRun.getD i 0 ∧ s.targetX = base.targetX.getD i 0 := by
  unfold laneGapSegments at hm
  rcases List.mem_append.mp hm with hf | hl
  · unfold forwardGapSegments at hf
    obtain ⟨sm, hmem, hs⟩ := List.mem_map.mp (List.mem_filter.mp hf).1
    subst s
    obtain ⟨k, hk, hsm⟩ := List.mem_map.mp hmem
    subst sm
    have hei := (List.mem_filter.mp he).1
    have hki : segKey p i = k := by
      simpa [buildSegment] using (List.mem_filter.mp hei).2
    have hi : i < p.edges.length := by
      have h := (List.mem_filter.mp hei).1
      exact List.mem_range.mp (List.mem_filter.mp h).1
    subst k
    exact buildSegment_ports (route_keyConst hb).2.2 (route_keyConst hb).2.1 hi
  · simp only [List.mem_flatMap, List.mem_append] at hl
    obtain ⟨run, _, hs⟩ := hl
    rcases hs with hs | hs <;> split at hs <;> simp_all [laneSegment]

end Elegant.Layered.RouteImpl

namespace Elegant.Layered.RouteImpl

theorem forward_mid_bounds {slot gap : Int} {rankGap : Nat → Int} {p : Proper}
    {layers : List (List Nat)} {x y top : List Int} {rev : List Bool}
    {widths : List Int} {lr : LaneRouting}
    (hr : routeWithLanes slot p layers x rev widths = .ok lr)
    (hF : CoordFacts p layers x y top lr.routing gap rankGap slot) {i : Nat}
    (hi : i < p.edges.length) (hrev : rev.getD (edgeAt p i).original false = false)
    (hne : runOf lr.routing i ≠ lr.routing.targetX.getD i 0) :
    top.getD (gapOf p i) 0 + (layers.map (layerHeight p)).getD (gapOf p i) 0 ≤
      midOf p slot top (layers.map (layerHeight p)) lr.routing i ∧
    midOf p slot top (layers.map (layerHeight p)) lr.routing i ≤
      top.getD (gapOf p i + 1) 0 := by
  obtain ⟨base, hb, _, rfl⟩ := routeWithLanes_spec hr
  have hk := (route_segment_facts hb hi).1
  have hg : gapOf p i < base.gaps.length := by
    have he := (route_spec hb).2.2.2.2.2.1
    simp only [he, List.length_map, List.length_range]
    omega
  have hm := forward_retained (base := base)
    (runs := plannedLanes slot p base x rev widths) hi hrev
  apply lane_mid_bounds_of_retained hi hg hk hF hm
  let raw := laneGapSegments p base rev (plannedLanes slot p base x rev widths) (gapOf p i)
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

end Elegant.Layered.RouteImpl

namespace Elegant.Layered.RouteImpl

theorem forward_piece_pairs {slot gap : Int} {rankGap : Nat → Int} {p : Proper}
    {layers : List (List Nat)} {x y top : List Int} {rev : List Bool}
    {widths : List Int} {lr : LaneRouting}
    (hr : routeWithLanes slot p layers x rev widths = .ok lr)
    (hF : CoordFacts p layers x y top lr.routing gap rankGap slot) {v : Nat}
    (hv : v < p.nodes.length) (hvpos : 0 < nodeH p v) {i : Nat} (hi : i < p.edges.length)
    (hrev : rev.getD (edgeAt p i).original false = false)
    (hvt : (edgeAt p i).tail ≠ v) (hvh : (edgeAt p i).head ≠ v) {pc : List Point}
    (hpc : pieceOf p slot y top (layers.map (layerHeight p)) lr.routing i = .ok pc) :
    pairsAll (fun P Q => Polyline.segMisses P Q (boxRect p x y v)) pc := by
  have hG := geo_ok_withLanes hr hF
  obtain ⟨base, hb, _, heq⟩ := routeWithLanes_spec hr
  obtain ⟨hl, _, _, _, hp, _⟩ := route_spec hb
  obtain ⟨_, _, _, hcov, hedge⟩ := layersOk_spec hl
  obtain ⟨ht, hh, hrk⟩ := hedge i hi
  obtain ⟨_, _, _, h0⟩ := hcov _ ht
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
    omega
  have hc := pieceOf_cases hpc
  apply piece_miss (G := routeGeo p layers x y top) hG ht hh hv hrk' (Ne.symm hvt)
    (Ne.symm hvh) hvpos (sx := lr.routing.sourceX.getD i 0) (run := runOf lr.routing i)
    (tx := lr.routing.targetX.getD i 0) ⟨pr.1, pr.2.1⟩ hrun ⟨pr.2.2.1, pr.2.2.2⟩
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨midOf p slot top (layers.map (layerHeight p)) lr.routing i,
      (forward_mid_bounds hr hF hi hrev h2).1,
      (forward_mid_bounds hr hF hi hrev h2).2, h1⟩

end Elegant.Layered.RouteImpl

namespace Elegant.Layered.RouteImpl

theorem forward_gap_valid {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x : List Int} {rev : List Bool} {widths : List Int} {lr : LaneRouting}
    (hr : routeWithLanes slot p layers x rev widths = .ok lr)
    {i : Nat} (hi : i < p.edges.length) : gapOf p i + 1 < layers.length := by
  obtain ⟨base, hb, _, _⟩ := routeWithLanes_spec hr
  exact (route_segment_facts hb hi).1

end Elegant.Layered.RouteImpl

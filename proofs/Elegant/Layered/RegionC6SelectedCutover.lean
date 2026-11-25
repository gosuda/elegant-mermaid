import Elegant.Layered.RegionC5ActiveSelected
import Elegant.Layered.RegionC6SelectedTrunk
import Elegant.Layered.RegionC6SelectedTransport
import Elegant.Layered.RegionDifferentLayerClearance
import Elegant.Layered.ExactBottomBracketVacancyProof

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Elegant.Layered.PipelineImpl.RegionOrdinaryC6

open RegionImpl RouteImpl

private theorem fallbackBracket_of_exactSuccess {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res exactRes : FamilyResult} (e : SceneExecutionR exactIds idSets inp o res)
    (hexact : layoutX exactIds inp o = .ok exactRes)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {part : List Nat × Part} {c : Nat} (s : R6_SelectedLoopPartR e c part)
    (hx : componentRunX e.params (exactDecls exactIds inp)
      (componentCandidate e.graph part.1 s.candidate) e.measured
      (candidateOrder s.candidate) = .ok s.run) : ExactBottomBracketVacant s.run := by
  obtain ⟨x⟩ := layoutX_sceneExecution hexact
  have hp : x.params = e.params := Except.ok.inj (x.checked.symm.trans e.checked)
  have hm : x.metric = e.metric := Except.ok.inj (x.metric_eq.symm.trans e.metric_eq)
  have hl : x.lines = e.lines := by
    have h := x.lines_eq
    rw [hp, hm] at h
    exact Except.ok.inj (h.symm.trans e.lines_eq)
  have hmeas : x.measured = e.measured := by
    have h := x.measured_eq
    rw [hp, hm] at h
    exact Except.ok.inj (h.symm.trans e.measured_eq)
  have hg0 : x.graph0 = e.graph0 := by
    have h := x.graph0_eq
    rw [hp, hl] at h
    exact Except.ok.inj (h.symm.trans e.graph0_eq)
  have hg : x.graph = e.graph := by
    have h := x.graph_eq
    rw [hp, hmeas, hg0] at h
    exact Except.ok.inj (h.symm.trans e.graph_eq)
  have hc : part.1 ∈ components x.graph := by rw [hg]; exact s.hComp
  apply sceneExecutionX_bottomBracketVacant x hwf hfp hc (candidate := s.candidate)
    (orderOptions := candidateOrder s.candidate)
  simpa only [hp, hmeas, hg] using hx

abbrev ActiveCoordFacts (P : Params) (run : Run) : Prop :=
  CoordFacts run.proper run.layers run.xs run.ys run.top run.routing
    (min P.nodeGap P.clusterPad) (reservedRouteRankGap P run) P.slot

/-- Endpoint legs and junctions of emitted pieces. A bent piece's horizontal
rank-gap segment is handled from the executed band bounds. -/
def ActiveForwardPieces (P : Params) (run : Run) (original v : Nat) : Prop :=
  let indices := edgesOf run.proper original
  let rect := boxRect run.proper run.xs run.ys v
  let r := run.lanes.routing
  (∀ {i : Nat} {points : List Point}, i ∈ indices →
    pieceOf run.proper P.slot run.ys run.top (run.layers.map (RouteImpl.layerHeight run.proper))
      r i = .ok points →
    let source := pieceStart run.proper run.ys r i
    let target := pieceEnd run.proper run.ys r i
    let cross := runOf r i
    let start : Point := ⟨cross, source.y⟩
    let mid := midOf run.proper P.slot run.top (run.layers.map (RouteImpl.layerHeight run.proper)) r i
    Polyline.segMisses source start rect ∧
    (cross = r.targetX.getD i 0 → Polyline.segMisses start target rect) ∧
    (cross ≠ r.targetX.getD i 0 →
      Polyline.segMisses start ⟨cross, mid⟩ rect ∧
      Polyline.segMisses ⟨r.targetX.getD i 0, mid⟩ target rect)) ∧
  (∀ {a b : Nat}, a ∈ indices → b ∈ indices → ChainLink run.proper a b →
    Polyline.segMisses (pieceEnd run.proper run.ys r a) (pieceStart run.proper run.ys r b) rect)

private theorem chainRel_restrict {R : Nat → Nat → Prop} (all : List Nat) :
    ∀ (xs : List Nat), (∀ i ∈ xs, i ∈ all) → chainRel R xs →
      chainRel (fun a b => R a b ∧ a ∈ all ∧ b ∈ all) xs
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: rest, hsub, h =>
    ⟨⟨h.1, hsub a List.mem_cons_self, hsub b (List.mem_cons_of_mem _ List.mem_cons_self)⟩,
      chainRel_restrict all (b :: rest) (fun i hi => hsub i (List.mem_cons_of_mem _ hi)) h.2⟩

private theorem activeForward_miss_of_pieces {P : Params} {run : Run} {native : EdgeRoute}
    {v : Nat} (hshape : ProperShape run.proper)
    (hfind : run.lanes.runs.find? (fun l => l.original == native.original) = none)
    (hroute : laneRouteOf P.slot run.proper run.ys run.top
      (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes native.original = .ok native)
    (hgapClear : ∀ {i : Nat}, i ∈ edgesOf run.proper native.original →
      runOf run.lanes.routing i ≠ run.lanes.routing.targetX.getD i 0 →
      let mid := midOf run.proper P.slot run.top (run.layers.map (RouteImpl.layerHeight run.proper))
        run.lanes.routing i
      Polyline.segMisses ⟨runOf run.lanes.routing i, mid⟩
        ⟨run.lanes.routing.targetX.getD i 0, mid⟩ (boxRect run.proper run.xs run.ys v))
    (hclear : ActiveForwardPieces P run native.original v) :
    ¬ Polyline.hitsRect native.points (boxRect run.proper run.xs run.ys v) := by
  simp only [laneRouteOf, hfind] at hroute
  unfold routeOf at hroute
  split at hroute
  · simp at hroute
  · next pcs hpcs =>
    have hpts := congrArg EdgeRoute.points (Except.ok.inj hroute)
    rw [← hpts]
    apply Polyline.not_hits_of_allMiss
    rw [allSegsMiss_iff]
    apply pairsAll_dedup
    refine pairsAll_flatten_of _ (pieceStart run.proper run.ys run.lanes.routing)
      (pieceEnd run.proper run.ys run.lanes.routing)
      (fun a b => ChainLink run.proper a b ∧ a ∈ edgesOf run.proper native.original ∧
        b ∈ edgesOf run.proper native.original) (fun _ _ h => hclear.2 h.2.1 h.2.2 h.1)
      _ pcs ?_ (chainRel_restrict _ _ (fun _ h => h) (hshape native.original))
    refine Zipped.imp _ _ ?_ (mapOk_zipped _ _ _ hpcs)
    intro i hi pc hpc
    refine ⟨(pieceOf_basic hpc).1, (pieceOf_basic hpc).2.1, ?_⟩
    have hlegs := hclear.1 hi hpc
    rcases pieceOf_cases hpc with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · exact ⟨hlegs.1, hlegs.2.1 hx, trivial⟩
    · exact ⟨hlegs.1, (hlegs.2.2 hx).1, hgapClear hi hx, (hlegs.2.2 hx).2, trivial⟩

private def reverseMid (P : Params) (run : Run) (gap index : Nat) : Int :=
  reverseRunMid P.slot run.top (run.layers.map (RouteImpl.layerHeight run.proper))
    run.lanes.routing gap index

/-- Three endpoint legs of the actual seven points. Neither horizontal rank-gap segment
nor the vertical trunk is a remaining premise. A top-marker leg uses `tailPortY`, not
`yAt + nodeH`, since active placement can reserve a nonzero marker height. -/
def ActiveReverseStubs (P : Params) (run : Run) (lane : ReversedLane) (v : Nat) : Prop :=
  let rect := boxRect run.proper run.xs run.ys v
  let cs := reverseMid P run lane.sourceGap lane.sourceSegment
  let ct := reverseMid P run lane.targetGap lane.targetSegment
  let ty := tailPortY run.proper run.ys lane.targetNode
  Polyline.segMisses ⟨lane.sourceX, yAt run.ys lane.sourceNode⟩ ⟨lane.sourceX, cs⟩ rect ∧
    Polyline.segMisses ⟨lane.targetRun, ct⟩ ⟨lane.targetRun, ty⟩ rect ∧
    Polyline.segMisses ⟨lane.targetRun, ty⟩ ⟨lane.targetX, ty⟩ rect

def ActiveReverseSameRankStubs (P : Params) (run : Run) (lane : ReversedLane)
    (v : Nat) : Prop :=
  let rank := (rk run.proper.rank v).toNat
  let rect := boxRect run.proper run.xs run.ys v
  let cs := reverseMid P run lane.sourceGap lane.sourceSegment
  let ct := reverseMid P run lane.targetGap lane.targetSegment
  let ty := tailPortY run.proper run.ys lane.targetNode
  (rank = lane.sourceGap + 1 →
    Polyline.segMisses ⟨lane.sourceX, yAt run.ys lane.sourceNode⟩ ⟨lane.sourceX, cs⟩ rect) ∧
  (rank = lane.targetGap →
    Polyline.segMisses ⟨lane.targetRun, ct⟩ ⟨lane.targetRun, ty⟩ rect ∧
    Polyline.segMisses ⟨lane.targetRun, ty⟩ ⟨lane.targetX, ty⟩ rect)

private theorem activeGapMiss {P : Params} {exactIds : List String} {spec : Option RegionSpec}
    {inp : Input} {candidate cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {order : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp candidate labels order = .ok (cg, run))
    {v : Nat} {node : Node} (hv : v < run.proper.nodes.length)
    (hnode : cg.nodes[v]? = some node) (hplain : node.border = 0)
    {gap : Nat} (hg : gap + 1 < run.layers.length) {mid a b : Int}
    (hlo : run.top.getD gap 0 + (run.layers.map (RouteImpl.layerHeight run.proper)).getD gap 0 ≤ mid)
    (hhi : mid ≤ run.top.getD (gap + 1) 0) :
    Polyline.segMisses ⟨a, mid⟩ ⟨b, mid⟩ (boxRect run.proper run.xs run.ys v) := by
  have bands := componentRunR_plain_rank_bands (exactIds := exactIds) hrun
  let rank := (rk run.proper.rank v).toNat
  obtain ⟨row, hrow, _, hboxLo, hboxHi⟩ := bands.1 hnode hplain
  change run.layers[rank]? = some row at hrow
  change run.top.getD rank 0 ≤ _ at hboxLo
  change _ ≤ run.top.getD rank 0 + _ at hboxHi
  have hborder : (cg.nodes.getD v default).border ≠ -2 := by
    rw [List.getD_eq_getElem?_getD, hnode, Option.getD_some, hplain]
    decide
  have hrect := plain_frame_eq_boxRect P cg run v hv hborder
  rw [hrect] at hboxLo hboxHi
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, q0, _, _, stages⟩ := componentRunR_stages hrun
  have hheight (l : List Nat) : RouteImpl.layerHeight run.proper l =
      CoordsImpl.layerHeight run.coordinateProper l := by
    rw [stages.hCoordProper]
    have hn : run.proper.nodes = q0.nodes := by rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
    have he : RouteImpl.layerHeight run.proper l = RouteImpl.layerHeight q0 l := by
      simp only [RouteImpl.layerHeight, RouteImpl.nodeH, hn]
    exact he.trans (layerHeight_proxy stages.hProxy l)
  have hg0 : gap < run.layers.length := by omega
  have hgap := List.getElem?_eq_getElem hg0
  have hnext := List.getElem?_eq_getElem hg
  rw [heights_getD hgap, hheight] at hlo
  by_cases hr : rank ≤ gap
  · apply miss_below
    change _ ≤ min mid mid
    rcases Nat.lt_or_eq_of_le hr with hr | hr
    · have hs := bands.2 hr hrow hgap
      have hn := CoordsImpl.layerHeight_nonneg run.coordinateProper run.layers[gap]
      omega
    · rw [hr] at hrow hboxHi
      have he := Option.some.inj (hrow.symm.trans hgap)
      rw [he] at hboxHi
      omega
  · apply miss_above
    change max mid mid ≤ _
    rcases Nat.lt_or_eq_of_le (show gap + 1 ≤ rank by omega) with hr | hr
    · have hs := bands.2 hr hnext hrow
      have hn := CoordsImpl.layerHeight_nonneg run.coordinateProper run.layers[gap + 1]
      omega
    · rw [← hr] at hboxLo
      omega

private theorem reservedMidStep {P : Params} {exactIds : List String} {spec : Option RegionSpec}
    {inp : Input} {candidate cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {order : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp candidate labels order =
      .ok (cg, run))
    {k : Nat} (hk : k + 1 < run.layers.length) :
    run.top.getD k 0 + (run.layers.map (RouteImpl.layerHeight run.proper)).getD k 0 +
      reservedRouteRankGap P run k + P.slot * (run.lanes.routing.gaps.getD k default).slots ≤
      run.top.getD (k + 1) 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  have hget := List.getElem?_eq_getElem (show k < run.layers.length by omega)
  rw [heights_getD hget, stages.hRouting]
  exact Int.le_of_eq (executedBand_step (exactIds := exactIds) hrun hget hk).symm

private theorem halfSlot_reserved {P : Params} (hp : P.Valid) (run : Run) (k : Nat) :
    Int.fdiv P.slot 2 ≤ reservedRouteRankGap P run k := by
  obtain ⟨_, hrank, _, hhalf⟩ := hp
  exact Int.le_trans (CoordsImpl.half_slot_le_rankGapAt hrank hhalf run.proper run.layers k)
    (Int.le_max_left _ _)

private theorem activeReverse_executedMids {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions} {reserved : List (Option Int)}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp candidate labels order =
      .ok (cg, run))
    (hrouter : routeWithLanesR P.slot run.proper run.layers run.xs (cg.edges.map (·.reversed))
      (cg.edges.map fun ed => (stackSize cg.slot (routeLabels labels ed.decl)).width)
      reserved = .ok run.lanes)
    (hp : P.Valid) {lane : ReversedLane} (hm : lane ∈ run.lanes.runs)
    (hsg : lane.sourceGap + 1 < run.layers.length)
    (htg : lane.targetGap + 1 < run.layers.length) :
    let heights := run.layers.map (RouteImpl.layerHeight run.proper)
    (run.top.getD lane.sourceGap 0 + heights.getD lane.sourceGap 0 ≤
        reverseMid P run lane.sourceGap lane.sourceSegment ∧
      reverseMid P run lane.sourceGap lane.sourceSegment ≤ run.top.getD (lane.sourceGap + 1) 0) ∧
    (run.top.getD lane.targetGap 0 + heights.getD lane.targetGap 0 ≤
        reverseMid P run lane.targetGap lane.targetSegment ∧
      reverseMid P run lane.targetGap lane.targetSegment ≤ run.top.getD (lane.targetGap + 1) 0) := by
  let flags := cg.edges.map (·.reversed)
  let widths := cg.edges.map fun ed => (stackSize cg.slot (routeLabels labels ed.decl)).width
  obtain ⟨base, hb, _, hr⟩ := routeWithLanesR_spec hrouter
  have hmem : lane ∈ plannedLanesR P.slot run.proper base run.xs flags widths reserved := by
    rw [hr] at hm
    exact hm
  obtain ⟨hsrc, htgt⟩ := activeReverse_rawSegments hmem
  have hlen : base.gaps.length = run.layers.length - 1 := by
    rw [(route_spec hb).2.2.2.2.2.1, List.length_map, List.length_range]
  have hentry (k : Nat) (hk : k < base.gaps.length) :
      run.lanes.routing.gaps.getD k default = numberLaneGap (laneGapSegments run.proper base
        flags (plannedLanesR P.slot run.proper base run.xs flags widths reserved) k) := by
    rw [hr]
    simp only [assembleLaneRouting, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some, flags, widths]
  exact ⟨activeReverse_mid_of_get (hentry lane.sourceGap (by omega)) hsrc hp.2.2.1
      (gap := lane.sourceGap) (index := lane.sourceSegment)
      (halfSlot_reserved hp _ _) (reservedMidStep (exactIds := exactIds) hrun hsg),
    activeReverse_mid_of_get (hentry lane.targetGap (by omega)) htgt hp.2.2.1
      (gap := lane.targetGap) (index := lane.targetSegment)
      (halfSlot_reserved hp _ _) (reservedMidStep (exactIds := exactIds) hrun htg)⟩

private theorem activeReverse_miss_of_stubs {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    {s : R6_SelectedLoopPartR e c part} {i j : Nat} {pts : List Point} {rect : Rect}
    (n : SelectedOrdinaryPair s i j pts rect) {spec : RegionSpec} {rm : ComponentRegions}
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some spec) inp
      (componentCandidateR (some spec) e.graph part.1 s.candidate) e.measured
      (candidateOrder s.candidate) = .ok (s.cg, s.run))
    (hactive : newComponentRegions (some spec) e.params inp
      (componentCandidateR (some spec) e.graph part.1 s.candidate) = .ok (some rm))
    {reserved : List (Option Int)}
    (hrouter : routeWithLanesR e.params.slot s.run.proper s.run.layers s.run.xs
      (s.cg.edges.map (·.reversed))
      (s.cg.edges.map fun ed => (stackSize s.cg.slot (routeLabels e.measured ed.decl)).width)
      reserved = .ok s.run.lanes)
    {lane : ReversedLane}
    (hfind : s.run.lanes.runs.find? (fun l => l.original == n.native.original) = some lane)
    (hclear : ActiveReverseStubs e.params s.run lane j) :
    ¬ Polyline.hitsRect n.native.points (boxRect s.run.proper s.run.xs s.run.ys j) := by
  let run := s.run
  let P := e.params
  have hedge : s.cg.edges[n.native.original]? = some n.edge := by rw [n.original]; exact n.edgeAt
  have hcross := selectedTrunk_crossClear (o := o) e.checked hrun hactive hedge n.nonloop
    n.nodeAt n.plain hfind
  have hm := List.mem_of_find?_eq_some hfind
  have hlane : lane.original = n.native.original := by
    simpa only [beq_iff_eq] using List.find?_some hfind
  have hfirst : (edgesOf s.run.proper lane.original).head? = some n.first := by
    rw [hlane]
    exact n.firstAt
  have hlast : (edgesOf s.run.proper lane.original).getLast? = some n.last := by
    rw [hlane]
    exact n.lastAt
  obtain ⟨_, _, _, _, _, _, hsg, htg, _⟩ := activeReverse_nodeFacts hrouter hm hfirst hlast
  obtain ⟨hsMid, htMid⟩ :=
    activeReverse_executedMids (exactIds := exactIds) hrun hrouter (checkedParams_valid e.checked)
      hm hsg htg
  have hsGap := activeGapMiss (exactIds := exactIds) hrun n.bound n.nodeAt n.plain hsg
    (a := lane.sourceX) (b := lane.lane) hsMid.1 hsMid.2
  have htGap := activeGapMiss (exactIds := exactIds) hrun n.bound n.nodeAt n.plain htg
    (a := lane.lane) (b := lane.targetRun) htMid.1 htMid.2
  have htrunk : Polyline.segMisses
      ⟨lane.lane, reverseMid P run lane.sourceGap lane.sourceSegment⟩
      ⟨lane.lane, reverseMid P run lane.targetGap lane.targetSegment⟩
      (boxRect run.proper run.xs run.ys j) := by
    rcases hcross with h | h
    · exact miss_left (by simpa using h)
    · exact miss_right (by simpa using h)
  have hpoints := (routePointsWithLanes_mem (componentRunR_routes_eqR hrun)
    (List.mem_of_getElem? n.nativeAt)).2
  have hp : n.native.points = dedup (reversedPoints P.slot run.proper run.ys run.top
      (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing lane) := by
    simp only [laneRouteOf, hfind] at hpoints
    split at hpoints
    · exact (congrArg EdgeRoute.points (Except.ok.inj hpoints)).symm
    · cases hpoints
  rw [hp]
  apply Polyline.not_hits_of_allMiss
  rw [allSegsMiss_iff]
  apply pairsAll_dedup
  exact ⟨hclear.1, hsGap, htrunk, htGap, hclear.2.1, hclear.2.2, trivial⟩

private theorem executedY_ge_rankTop {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp candidate labels order = .ok (cg, run))
    (hlayers : layersOk run.proper run.layers = true) {v : Nat} (hv : v < run.proper.nodes.length) :
    run.top.getD (rk run.proper.rank v).toNat 0 ≤ yAt run.ys v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, q0, ⟨y, top⟩, ysMid, stages⟩ :=
    componentRunR_stages hrun
  let k := (rk run.proper.rank v).toNat
  have hnodes : run.proper.nodes = q0.nodes := by rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
  obtain ⟨_, hrank', hlen, _, _, _⟩ := proxyWidths_rel stages.hProxy
  have hrank : run.proper.rank = placed.rank := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_rank]
    exact hrank'
  have hvPlaced : v < placed.nodes.length := by simpa only [hnodes, hlen] using hv
  have hcoord : placed.nodes[v]? = some placed.nodes[v] := List.getElem?_eq_getElem hvPlaced
  obtain ⟨row, hrow, hmem, hnonneg⟩ := (layersOk_spec hlayers).2.2.2.1 v hv
  change run.layers[k]? = some row at hrow
  have hr : rk placed.rank v = (k : Int) := by
    rw [← hrank]
    exact (Int.toNat_of_nonneg hnonneg).symm
  obtain ⟨hyLen, htopLen⟩ := CoordsImpl.rankCoordsWith_length stages.hYt
  have hmidLen : ysMid.length = placed.nodes.length := by
    rw [← stages.hYsMid]
    simpa only [proxyYs, List.length_map, List.length_zipIdx] using hyLen
  have haxis := CoordsImpl.rankAxis_node_in_band stages.hYt hrow hmem hvPlaced hr
  have hbefore := proxyYs_getD placed run.layers top y hcoord (by rwa [hyLen])
  rw [stages.hYsMid, ← hrank] at hbefore
  have hbeforeLow : top.getD k 0 ≤ ysMid.getD v 0 := by
    rw [hbefore]
    split
    · exact Int.le_refl _
    · split
      · have hh := CoordsImpl.layerHeight_nonneg placed (run.layers.getD k [])
        change top.getD k 0 ≤ top.getD k 0 +
          CoordsImpl.layerHeight placed (run.layers.getD k [])
        omega
      · exact haxis.1
  obtain ⟨_, shifts, _, _, _, _, htop, hy⟩ :=
    (runHooksShift_exact P exactIds inp cg labels).shifts placed run.layers ysMid top
      run.ys run.top stages.hReserve
  have hY := hy v (by rwa [hmidLen])
  change run.ys.getD v 0 = ysMid.getD v 0 + shifts.getD (rk placed.rank v).toNat 0 at hY
  rw [← hrank] at hY
  change run.ys.getD v 0 = ysMid.getD v 0 + shifts.getD k 0 at hY
  have hk : k < top.length := by
    rw [htopLen]
    exact (List.getElem?_eq_some_iff.mp hrow).1
  change run.top.getD k 0 ≤ run.ys.getD v 0
  rw [htop k hk, hY]
  exact Int.add_le_add_right hbeforeLow _

/-- Each reversed stub is confined to its endpoint rank and the adjacent gap.
Only a victim on that stub's own endpoint rank needs cross-axis information. -/
theorem activeReverseStubMisses_of_differentRanks {P : Params} {exactIds : List String}
    {spec : RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {rm : ComponentRegions} {labels : List MeasuredLabel} {order : OrderOptions}
    {reserved : List (Option Int)}
    (hrun : componentRunR P (exactDecls exactIds inp) (some spec) inp candidate labels order =
      .ok (cg, run))
    (hactive : newComponentRegions (some spec) P inp candidate = .ok (some rm))
    (hrouter : routeWithLanesR P.slot run.proper run.layers run.xs (cg.edges.map (·.reversed))
      (cg.edges.map fun ed => (stackSize cg.slot (routeLabels labels ed.decl)).width)
      reserved = .ok run.lanes)
    (hp : P.Valid) {lane : ReversedLane} (hm : lane ∈ run.lanes.runs)
    {first last : Nat} (hfirst : (edgesOf run.proper lane.original).head? = some first)
    (hlast : (edgesOf run.proper lane.original).getLast? = some last)
    {v : Nat} {node : Node} (hv : v < run.proper.nodes.length)
    (hnode : cg.nodes[v]? = some node) (hplain : node.border = 0) :
    let rank := (rk run.proper.rank v).toNat
    let rect := boxRect run.proper run.xs run.ys v
    let cs := reverseMid P run lane.sourceGap lane.sourceSegment
    let ct := reverseMid P run lane.targetGap lane.targetSegment
    let ty := tailPortY run.proper run.ys lane.targetNode
    (rank ≠ lane.sourceGap + 1 →
      Polyline.segMisses ⟨lane.sourceX, yAt run.ys lane.sourceNode⟩ ⟨lane.sourceX, cs⟩ rect) ∧
    (rank ≠ lane.targetGap →
      Polyline.segMisses ⟨lane.targetRun, ct⟩ ⟨lane.targetRun, ty⟩ rect ∧
      Polyline.segMisses ⟨lane.targetRun, ty⟩ ⟨lane.targetX, ty⟩ rect) := by
  let rank := (rk run.proper.rank v).toNat
  let rect := boxRect run.proper run.xs run.ys v
  let top (k : Nat) := run.top.getD k 0
  let height (k : Nat) := CoordsImpl.layerHeight run.coordinateProper (run.layers.getD k [])
  obtain ⟨_, _, hs, ht, hsr, htr, hsg, htg, _⟩ := activeReverse_nodeFacts hrouter hm hfirst hlast
  obtain ⟨⟨hcslo, hcshi⟩, ⟨hctlo, hcthi⟩⟩ :=
    activeReverse_executedMids (exactIds := exactIds) hrun hrouter hp hm hsg htg
  obtain ⟨_, hb, _, _⟩ := routeWithLanesR_spec hrouter
  have hlayers := (route_spec hb).1
  have hsizes := (layersOk_spec hlayers).2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, q0, _, _, stages⟩ := componentRunR_stages hrun
  have hheight (k : Nat) (hk : k < run.layers.length) :
      (run.layers.map (RouteImpl.layerHeight run.proper)).getD k 0 = height k := by
    have hget := List.getElem?_eq_getElem hk
    have hnodes : run.proper.nodes = q0.nodes := by rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
    have he : RouteImpl.layerHeight run.proper run.layers[k] =
        RouteImpl.layerHeight q0 run.layers[k] := by
      simp only [RouteImpl.layerHeight, RouteImpl.nodeH, hnodes]
    unfold height
    rw [heights_getD hget, List.getD_eq_getElem?_getD, hget, Option.getD_some, stages.hCoordProper]
    exact he.trans (layerHeight_proxy stages.hProxy _)
  rw [hheight lane.sourceGap (by omega)] at hcslo
  rw [hheight lane.targetGap (by omega)] at hctlo
  obtain ⟨row, hrow, _, hvlo, hvhi⟩ :=
    (componentRunR_plain_rank_bands (exactIds := exactIds) hrun).1 hnode hplain
  have hborder : (cg.nodes.getD v default).border ≠ -2 := by
    rw [List.getD_eq_getElem?_getD, hnode, Option.getD_some, hplain]
    decide
  rw [plain_frame_eq_boxRect P cg run v hv hborder] at hvlo hvhi
  change run.layers[rank]? = some row at hrow
  have hrowD : run.layers.getD rank [] = row := by
    rw [List.getD_eq_getElem?_getD, hrow, Option.getD_some]
  have hvr := (List.getElem?_eq_some_iff.mp hrow).1
  change top rank ≤ rect.y at hvlo
  have hvbot : rect.y + rect.h ≤ top rank + height rank := by
    unfold height
    rw [hrowD]
    exact hvhi
  have hsep {a b : Nat} (hab : a < b) (hbl : b < run.layers.length) :
      top a + height a ≤ top b :=
    (componentRunR_boundaryRankBands (exactIds := exactIds) hrun).2 hab hbl
  have hnonneg (k : Nat) : 0 ≤ height k :=
    CoordsImpl.layerHeight_nonneg run.coordinateProper (run.layers.getD k [])
  have hprior {k : Nat} (hlt : rank < k) (hk : k < run.layers.length) :
      rect.y + rect.h ≤ top k := Int.le_trans hvbot (hsep hlt hk)
  have hpriorBand {k : Nat} (hle : rank ≤ k) (hk : k < run.layers.length) :
      rect.y + rect.h ≤ top k + height k := by
    rcases Nat.lt_or_eq_of_le hle with hlt | he
    · exact Int.le_trans (hprior hlt hk) (Int.le_add_of_nonneg_right (hnonneg k))
    · rw [← he]
      exact hvbot
  have hafterBand {k : Nat} (hlt : k < rank) : top k + height k ≤ rect.y :=
    Int.le_trans (hsep hlt hvr) hvlo
  have hafterTop {k : Nat} (hle : k ≤ rank) : top k ≤ rect.y := by
    rcases Nat.lt_or_eq_of_le hle with hlt | he
    · exact Int.le_trans (Int.le_add_of_nonneg_right (hnonneg k)) (hafterBand hlt)
    · rw [he]
      exact hvlo
  have hsyLo := executedY_ge_rankTop (exactIds := exactIds) hrun hlayers hs
  have hsyHi := componentRunR_active_node_rank_upper (exactIds := exactIds) hrun hactive hs
  have htyLo := executedY_ge_rankTop (exactIds := exactIds) hrun hlayers ht
  have htyHi := componentRunR_active_node_rank_upper (exactIds := exactIds) hrun hactive ht
  rw [hsr] at hsyLo hsyHi
  rw [htr] at htyLo htyHi
  have hsle : yAt run.ys lane.sourceNode ≤ top (lane.sourceGap + 1) +
      height (lane.sourceGap + 1) :=
    Int.le_trans (Int.le_add_of_nonneg_right (hsizes _ hs).2) hsyHi
  have htge : top lane.targetGap ≤ tailPortY run.proper run.ys lane.targetNode := by
    unfold tailPortY
    split
    · exact htyLo
    · exact Int.le_trans htyLo (Int.le_add_of_nonneg_right (hsizes _ ht).2)
  have htle : tailPortY run.proper run.ys lane.targetNode ≤
      top lane.targetGap + height lane.targetGap :=
    Int.le_trans (tailPortY_le_bottom (p := run.proper) (y := run.ys)
      (v := lane.targetNode) (hsizes _ ht).2) htyHi
  constructor
  · intro hne
    rcases Nat.lt_or_gt_of_ne hne with hlo | hhi
    · have hcs := Int.le_trans (hpriorBand (k := lane.sourceGap) (by omega) (by omega)) hcslo
      exact miss_below (Int.le_min.mpr ⟨Int.le_trans (hprior hlo hsg) hsyLo, hcs⟩)
    · exact miss_above (Int.max_le.mpr ⟨Int.le_trans hsle (hafterBand hhi),
        Int.le_trans hcshi (hafterTop (Nat.le_of_lt hhi))⟩)
  · intro hne
    rcases Nat.lt_or_gt_of_ne hne with hlo | hhi
    · have hty := Int.le_trans (hprior hlo (by omega)) htge
      have hct := Int.le_trans (hpriorBand (Nat.le_of_lt hlo) (by omega)) hctlo
      exact ⟨miss_below (Int.le_min.mpr ⟨hct, hty⟩), miss_below (Int.le_min.mpr ⟨hty, hty⟩)⟩
    · have hty := Int.le_trans htle (hafterBand hhi)
      have hct := Int.le_trans hcthi (hafterTop (k := lane.targetGap + 1) (by omega))
      exact ⟨miss_above (Int.max_le.mpr ⟨hct, hty⟩), miss_above (Int.max_le.mpr ⟨hty, hty⟩)⟩

theorem selectedActiveReverseStubs_of_sameRank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    {s : R6_SelectedLoopPartR e c part} {i v : Nat} {pts : List Point} {rect : Rect}
    (n : SelectedOrdinaryPair s i v pts rect) {spec : RegionSpec} {rm : ComponentRegions}
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some spec) inp
      (componentCandidateR (some spec) e.graph part.1 s.candidate) e.measured
      (candidateOrder s.candidate) = .ok (s.cg, s.run))
    (hactive : newComponentRegions (some spec) e.params inp
      (componentCandidateR (some spec) e.graph part.1 s.candidate) = .ok (some rm))
    {reserved : List (Option Int)}
    (hrouter : routeWithLanesR e.params.slot s.run.proper s.run.layers s.run.xs
      (s.cg.edges.map (·.reversed))
      (s.cg.edges.map fun ed => (stackSize s.cg.slot (routeLabels e.measured ed.decl)).width)
      reserved = .ok s.run.lanes)
    {lane : ReversedLane}
    (hfind : s.run.lanes.runs.find? (fun l => l.original == n.native.original) = some lane)
    (hsame : ActiveReverseSameRankStubs e.params s.run lane v) :
    ActiveReverseStubs e.params s.run lane v := by
  have hlane : lane.original = n.native.original := by
    simpa only [beq_iff_eq] using List.find?_some hfind
  have hfirst : (edgesOf s.run.proper lane.original).head? = some n.first := by
    rw [hlane]
    exact n.firstAt
  have hlast : (edgesOf s.run.proper lane.original).getLast? = some n.last := by
    rw [hlane]
    exact n.lastAt
  have hdiff := activeReverseStubMisses_of_differentRanks (exactIds := exactIds) hrun hactive
    hrouter (checkedParams_valid e.checked) (List.mem_of_find?_eq_some hfind)
    hfirst hlast n.bound n.nodeAt n.plain
  constructor
  · by_cases h : (rk s.run.proper.rank v).toNat = lane.sourceGap + 1
    · exact hsame.1 h
    · exact hdiff.1 h
  · by_cases h : (rk s.run.proper.rank v).toNat = lane.targetGap
    · exact hsame.2 h
    · exact hdiff.2 h

/-- Every actual segment starts in a rank strictly after the victim's rank. -/
def VictimBeforeForwardPieces (run : Run) (original v : Nat) : Prop :=
  ∀ i ∈ edgesOf run.proper original, (rk run.proper.rank v).toNat < gapOf run.proper i

theorem victimBeforeForwardPieces_iff_first {run : Run} {original v first : Nat}
    (hshape : ProperShape run.proper) (hlayers : layersOk run.proper run.layers = true)
    (hfirst : (edgesOf run.proper original).head? = some first) :
    VictimBeforeForwardPieces run original v ↔
      (rk run.proper.rank v).toNat < gapOf run.proper first := by
  constructor
  · intro h
    exact h first (List.mem_of_head? hfirst)
  · intro h i hi
    have hp := chain_pairwise (gapOf run.proper) (fun _ _ h => chain_gap_lt hlayers h)
      (edgesOf run.proper original) (hshape original)
    obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hfirst
    rw [hrest] at hp hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact h
    · exact Nat.lt_trans h ((List.pairwise_cons.mp hp).1 _ hi)

/-- A victim before the whole oriented chain misses all endpoint legs and all junctions.
The port lower bound uses the actual top-marker port, even if its marker has positive height. -/
theorem activeForwardPieces_of_victimBefore {P : Params} {exactIds : List String}
    {spec : RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions} {reserved : List (Option Int)}
    (hrun : componentRunR P (exactDecls exactIds inp) (some spec) inp candidate labels order =
      .ok (cg, run))
    (hrouter : routeWithLanesR P.slot run.proper run.layers run.xs (cg.edges.map (·.reversed))
      (cg.edges.map fun ed => (stackSize cg.slot (routeLabels labels ed.decl)).width)
      reserved = .ok run.lanes)
    (hp : P.Valid) {native : EdgeRoute} (hnative : native ∈ run.routes)
    (hchain : (edgesOf run.proper native.original).isEmpty = false)
    (hlane : run.lanes.runs.find? (fun l => l.original == native.original) = none)
    {v : Nat} {node : Node} (hv : v < run.proper.nodes.length)
    (hnode : cg.nodes[v]? = some node) (hplain : node.border = 0)
    (hprior : VictimBeforeForwardPieces run native.original v) :
    ActiveForwardPieces P run native.original v := by
  let r := run.lanes.routing
  let heights := run.layers.map (RouteImpl.layerHeight run.proper)
  let rect := boxRect run.proper run.xs run.ys v
  let rank := (rk run.proper.rank v).toNat
  obtain ⟨base, hb, hslot, _⟩ := routeWithLanesR_spec hrouter
  have hlayers := (route_spec hb).1
  obtain ⟨_, hsizes, _, hcover, hedge⟩ := layersOk_spec hlayers
  have hroute := (routePointsWithLanes_mem (componentRunR_routes_eqR hrun) hnative).1
  have hrev := activeForward_reversed_false hrouter hroute hchain hlane
  have hborder : (cg.nodes.getD v default).border ≠ -2 := by
    rw [List.getD_eq_getElem?_getD, hnode, Option.getD_some, hplain]
    decide
  obtain ⟨hboxes, hsep⟩ := componentRunR_plain_rank_bands (exactIds := exactIds) hrun
  obtain ⟨row, hrow, _, _, hboxHi⟩ := hboxes hnode hplain
  change run.layers[rank]? = some row at hrow
  rw [plain_frame_eq_boxRect P cg run v hv hborder] at hboxHi
  change rect.y + rect.h ≤ run.top.getD rank 0 + _ at hboxHi
  have hbefore {k : Nat} (hk : k < run.layers.length) (hlt : rank < k) :
      rect.y + rect.h ≤ run.top.getD k 0 :=
    Int.le_trans hboxHi (hsep hlt hrow (List.getElem?_eq_getElem hk))
  have hstartEnd {i : Nat} (hi : i ∈ edgesOf run.proper native.original) :
      rect.y + rect.h ≤ (pieceStart run.proper run.ys r i).y ∧
      rect.y + rect.h ≤ (pieceEnd run.proper run.ys r i).y := by
    have hib := RouteImpl.mem_edgesOf hi
    obtain ⟨ht, hh, hstep⟩ := hedge i hib
    obtain ⟨_, _, _, htn⟩ := hcover _ ht
    have hhead : (rk run.proper.rank (edgeAt run.proper i).head).toNat =
        gapOf run.proper i + 1 := by
      unfold gapOf
      omega
    have hk := (route_segment_facts hb hib).1
    have hlt := hprior i hi
    have hloT := executedY_ge_rankTop (exactIds := exactIds) hrun hlayers ht
    have hloH := executedY_ge_rankTop (exactIds := exactIds) hrun hlayers hh
    change run.top.getD (gapOf run.proper i) 0 ≤ _ at hloT
    rw [hhead] at hloH
    constructor
    · have htail := Int.le_trans (hbefore (by omega) hlt) hloT
      have hnn := (hsizes _ ht).2
      change rect.y + rect.h ≤ tailPortY run.proper run.ys (edgeAt run.proper i).tail
      unfold tailPortY
      split <;> omega
    · exact Int.le_trans (hbefore hk (by omega)) hloH
  constructor
  · intro i points hi _
    obtain ⟨hs, he⟩ := hstartEnd hi
    refine ⟨miss_below (Int.le_min.mpr ⟨hs, hs⟩), ?_, ?_⟩
    · intro _
      exact miss_below (Int.le_min.mpr ⟨hs, he⟩)
    · intro hne
      have hm := Elegant.Layered.PipelineImpl.mem_edgesOf.mp hi
      have hk := (route_segment_facts hb hm.1).1
      have hj : gapOf run.proper i < run.layers.length := by omega
      have hrow := List.getElem?_eq_getElem hj
      have hstep := executedBand_step (exactIds := exactIds) hrun hrow hk
      have hstep' : run.top.getD (gapOf run.proper i) 0 + heights.getD (gapOf run.proper i) 0 +
          reservedRouteRankGap P run (gapOf run.proper i) +
          P.slot * (r.gaps.getD (gapOf run.proper i) default).slots ≤
          run.top.getD (gapOf run.proper i + 1) 0 := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
        change run.top.getD (gapOf run.proper i) 0 +
          (run.layers.map (RouteImpl.layerHeight run.proper)).getD (gapOf run.proper i) 0 +
          reservedRouteRankGap P run (gapOf run.proper i) +
          P.slot * (run.lanes.routing.gaps.getD (gapOf run.proper i) default).slots ≤
          run.top.getD (gapOf run.proper i + 1) 0
        rw [heights_getD (p := run.proper) hrow, stages.hRouting]
        exact Int.le_of_eq hstep.symm
      have hhalf := CoordsImpl.half_slot_le_rankGapAt hp.2.1 hp.2.2.2
        run.proper run.layers (gapOf run.proper i)
      have hhalf' : Int.fdiv P.slot 2 ≤ reservedRouteRankGap P run (gapOf run.proper i) :=
        Int.le_trans hhalf (Int.le_max_left _ _)
      have hmid := activeForward_midBounds hrouter hslot hhalf' hm.1
        (by rw [hm.2]; exact hrev) hne hstep'
      have hnn := RouteImpl.layerHeight_nonneg run.proper (run.layers[gapOf run.proper i]'hj)
      have hheight : 0 ≤ heights.getD (gapOf run.proper i) 0 := by
        change 0 ≤ (run.layers.map (RouteImpl.layerHeight run.proper)).getD (gapOf run.proper i) 0
        rw [heights_getD hrow]
        exact hnn
      have hband := hbefore hj (hprior i hi)
      have hmidLow : rect.y + rect.h ≤ midOf run.proper P.slot run.top heights r i := by
        have hmLow := hmid.1
        change run.top.getD (gapOf run.proper i) 0 + heights.getD (gapOf run.proper i) 0 ≤
          midOf run.proper P.slot run.top heights r i at hmLow
        omega
      exact ⟨miss_below (Int.le_min.mpr ⟨hs, hmidLow⟩),
        miss_below (Int.le_min.mpr ⟨hmidLow, he⟩)⟩
  · intro a b ha hb _
    have he := (hstartEnd ha).2
    have hs := (hstartEnd hb).1
    exact miss_below (Int.le_min.mpr ⟨he, hs⟩)

/-- Selected-run instance of the rank-before partition of the C6 residual. -/
theorem selectedActiveForwardPieces_of_victimBefore {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    {s : R6_SelectedLoopPartR e c part} {i v : Nat} {pts : List Point} {rect : Rect}
    (n : SelectedOrdinaryPair s i v pts rect) {spec : RegionSpec} (hused : s.used = some spec)
    (hlane : s.run.lanes.runs.find? (fun l => l.original == n.native.original) = none)
    (hprior : VictimBeforeForwardPieces s.run n.native.original v) :
    ActiveForwardPieces e.params s.run n.native.original v := by
  rcases s.dispatch n.edgeAt with ⟨hnone, _, _⟩ | ⟨found, _, reserved, hfound, _, _, _, hrouter⟩
  · rw [hused] at hnone
    cases hnone
  · have hrun := s.hRun
    rw [hfound] at hrun
    have hchain : (edgesOf s.run.proper n.native.original).isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem (RouteImpl.mem_of_head' n.firstAt))
    exact activeForwardPieces_of_victimBefore (exactIds := exactIds) hrun hrouter
      (checkedParams_valid e.checked) (List.mem_of_getElem? n.nativeAt) hchain hlane
      n.bound n.nodeAt n.plain hprior

/-- Every segment of the actual chain ends at a rank strictly before the victim. -/
def VictimAfterForwardPieces (run : Run) (original v : Nat) : Prop :=
  ∀ i ∈ edgesOf run.proper original, gapOf run.proper i + 1 < (rk run.proper.rank v).toNat

/-- After the chain, the executed endpoint and numbered-slot heights are all
at or before the top of the victim's band. This covers straight legs, bent
legs and the joins between pieces even when an active top marker is raised. -/
theorem selectedActiveForwardPieces_of_victimAfter {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    {s : R6_SelectedLoopPartR e c part} {i v : Nat} {pts : List Point} {rect : Rect}
    (n : SelectedOrdinaryPair s i v pts rect) {spec : RegionSpec} (hused : s.used = some spec)
    (hlane : s.run.lanes.runs.find? (fun l => l.original == n.native.original) = none)
    (hafter : VictimAfterForwardPieces s.run n.native.original v) :
    ActiveForwardPieces e.params s.run n.native.original v := by
  rcases s.dispatch n.edgeAt with
    ⟨hnone, _, _⟩ | ⟨_, _, _, hfound, hactive, _, _, hrouter⟩
  · rw [hused] at hnone
    cases hnone
  let run := s.run
  let r := run.lanes.routing
  let rank := (rk run.proper.rank v).toNat
  let box := boxRect run.proper run.xs run.ys v
  have hrun := s.hRun
  rw [hfound] at hrun hactive
  obtain ⟨base, hb, hslot, _⟩ := routeWithLanesR_spec hrouter
  obtain ⟨_, hsizes, _, hcover, hedge⟩ :=
    layersOk_spec (p := run.proper) (layers := run.layers) (route_spec hb).1
  have hnative := (routePointsWithLanes_mem (componentRunR_routes_eqR hrun)
    (List.mem_of_getElem? n.nativeAt)).1
  have hchain : (edgesOf run.proper n.native.original).isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem (RouteImpl.mem_of_head' n.firstAt))
  have hrev := activeForward_reversed_false hrouter hnative hchain hlane
  have hbplain : (s.cg.nodes.getD v default).border ≠ -2 := by
    rw [List.getD_eq_getElem?_getD, n.nodeAt, Option.getD_some, n.plain]
    decide
  obtain ⟨hboxes, hsep⟩ := componentRunR_plain_rank_bands (exactIds := exactIds) hrun
  obtain ⟨row, hrow, _, hboxLo, _⟩ := hboxes n.nodeAt n.plain
  change run.layers[rank]? = some row at hrow
  rw [plain_frame_eq_boxRect e.params s.cg run v n.bound hbplain] at hboxLo
  change run.top.getD rank 0 ≤ box.y at hboxLo
  have hboxAfter {k : Nat} {layer : List Nat} (hk : run.layers[k]? = some layer)
      (hlt : k < rank) :
      run.top.getD k 0 + CoordsImpl.layerHeight run.coordinateProper layer ≤ box.y :=
    Int.le_trans (hsep hlt hk hrow) hboxLo
  have hportUpper {u : Nat} (hu : u < run.proper.nodes.length)
      (hprior : (rk run.proper.rank u).toNat < rank) :
      yAt run.ys u + nodeH run.proper u ≤ box.y := by
    obtain ⟨layer, hlu, _, _⟩ := hcover u hu
    have hget : run.layers.getD (rk run.proper.rank u).toNat [] = layer := by
      rw [List.getD_eq_getElem?_getD, hlu, Option.getD_some]
    have huUpper := componentRunR_active_node_rank_upper (exactIds := exactIds) hrun hactive hu
    rw [hget] at huUpper
    exact Int.le_trans huUpper (hboxAfter hlu hprior)
  have hports {k : Nat} (hk : k ∈ edgesOf run.proper n.native.original) :
      (pieceStart run.proper run.ys r k).y ≤ box.y ∧
      (pieceEnd run.proper run.ys r k).y ≤ box.y := by
    obtain ⟨ht, hh, hstep⟩ := hedge k (RouteImpl.mem_edgesOf hk)
    obtain ⟨_, _, _, hnn⟩ := hcover _ ht
    have hhead : (rk run.proper.rank (edgeAt run.proper k).head).toNat =
        gapOf run.proper k + 1 := by
      calc
        _ = (rk run.proper.rank (edgeAt run.proper k).tail + 1).toNat :=
          congrArg Int.toNat hstep
        _ = _ := Int.toNat_add hnn Int.one_nonneg
    have hlt : gapOf run.proper k + 1 < rank := hafter k hk
    have htail : (rk run.proper.rank (edgeAt run.proper k).tail).toNat < rank :=
      Nat.lt_of_succ_lt hlt
    have htPort := Int.le_trans (tailPortY_le_bottom (hsizes _ ht).2) (hportUpper ht htail)
    have hhPort := hportUpper hh (by rw [hhead]; exact hlt)
    exact ⟨htPort, Int.le_trans (Int.le_add_of_nonneg_right (hsizes _ hh).2) hhPort⟩
  constructor
  · intro k points hk _
    obtain ⟨hs, he⟩ := hports hk
    refine ⟨miss_above (Int.max_le.mpr ⟨hs, hs⟩), ?_, ?_⟩
    · intro _
      exact miss_above (Int.max_le.mpr ⟨hs, he⟩)
    · intro hne
      have hm := Elegant.Layered.PipelineImpl.mem_edgesOf.mp hk
      have hgap := (route_segment_facts hb hm.1).1
      have hmid := activeForward_midBounds hrouter hslot
        (halfSlot_reserved (checkedParams_valid e.checked) run (gapOf run.proper k))
        hm.1 (by rw [hm.2]; exact hrev) hne (reservedMidStep (exactIds := exactIds) hrun hgap)
      have hrow' := List.getElem?_eq_getElem hgap
      have hband := hboxAfter hrow' (hafter k hk)
      have hheight := CoordsImpl.layerHeight_nonneg run.coordinateProper
        run.layers[gapOf run.proper k + 1]
      have hmidUpper : midOf run.proper e.params.slot run.top
          (run.layers.map (RouteImpl.layerHeight run.proper)) r k ≤ box.y := by
        calc
          _ ≤ run.top.getD (gapOf run.proper k + 1) 0 := hmid.2
          _ ≤ _ := Int.le_trans (Int.le_add_of_nonneg_right hheight) hband
      exact ⟨miss_above (Int.max_le.mpr ⟨hs, hmidUpper⟩),
        miss_above (Int.max_le.mpr ⟨hmidUpper, he⟩)⟩
  · intro a b ha hb _
    exact miss_above (Int.max_le.mpr ⟨(hports ha).2, (hports hb).1⟩)

private abbrev middleRank (run : Run) (v : Nat) : Nat := (rk run.proper.rank v).toNat

private abbrev middleRect (run : Run) (v : Nat) : Rect :=
  boxRect run.proper run.xs run.ys v

private def middlePlain (run : Run) (v : Nat) : Prop :=
  ∃ nd, run.proper.nodes[v]? = some nd ∧ nd.node.border = 0

def ForwardAnchorsAtVictimRank (cg : Graph) (run : Run) (original v : Nat) : Prop :=
  ∀ {k}, k ∈ edgesOf run.proper original →
    let tail := (edgeAt run.proper k).tail
    let head := (edgeAt run.proper k).head
    (middleRank run tail = middleRank run v →
      middlePlain run tail ∨ ∃ nd, cg.nodes[tail]? = some nd ∧ nd.border = 2) ∧
    (middleRank run head = middleRank run v →
      middlePlain run head ∨ ∃ nd, cg.nodes[head]? = some nd ∧ nd.border = -2)

private def middleXGap (a b : Rect) : Prop :=
  a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x

private def middleInX (b : Rect) (x : Int) : Prop := b.x ≤ x ∧ x ≤ b.x + b.w

private theorem middleMissX {a b : Rect} {p q : Point}
    (h : middleXGap a b) (hp : middleInX a p.x) (hq : middleInX a q.x) :
    Polyline.segMisses p q b := by
  rcases h with h | h
  · exact miss_left (Int.max_le.mpr ⟨Int.le_trans hp.2 h, Int.le_trans hq.2 h⟩)
  · exact miss_right (Int.le_min.mpr ⟨Int.le_trans h hp.1, Int.le_trans h hq.1⟩)

private theorem middleActivePlainRowGap {P : Params} {exactIds : List String}
    {spec : RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions} {rm : ComponentRegions} {o : Options}
    (hp : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P (exactDecls exactIds inp) (some spec) inp candidate labels order =
      .ok (cg, run))
    (hactive : newComponentRegions (some spec) P inp candidate = .ok (some rm))
    {row : List Nat} (hrow : row ∈ run.layers) {a b : Nat} (har : a ∈ row) (hbr : b ∈ row)
    (hne : a ≠ b) (ha : middlePlain run a) (hb : middlePlain run b) :
    middleXGap (middleRect run a) (middleRect run b) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, q0, _, _, trace⟩ := componentRunR_stages hrun
  have hproxy : proxyWidths run.coordinateProper run.coordinateXs = .ok (q0, run.xs) := by
    rw [trace.hCoordProper]
    exact trace.hProxy
  have hn : run.proper.nodes = q0.nodes := by rw [← trace.hDrop, OrderImpl.dropSynthetic_nodes]
  obtain ⟨_, _, hlen, _, hrecords, hsame⟩ := proxyWidths_rel hproxy
  have hcoord {v : Nat} {n : ProperNode} (hv : run.proper.nodes[v]? = some n)
      (hb : n.node.border = 0) : run.coordinateProper.nodes[v]? = some n := by
    rw [hn] at hv
    have hv' : v < run.coordinateProper.nodes.length := by
      rw [← hlen]
      exact (List.getElem?_eq_some_iff.mp hv).1
    have hs : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
      List.getElem?_eq_getElem hv'
    obtain ⟨m, hm, _, hmb, _⟩ := hrecords v _ hs
    have he := Option.some.inj (hm.symm.trans hv)
    have hz : run.coordinateProper.nodes[v].node.border = 0 := hmb.symm.trans
      ((congrArg (fun nd : ProperNode => nd.node.border) he).trans hb)
    have hnot : ¬ (run.coordinateProper.nodes[v].node.border = -2 ∨
        run.coordinateProper.nodes[v].node.border = 2) := by simp [hz]
    have hout := (hsame v _ hs hnot).1
    rw [Option.some.inj (hout.symm.trans hv)] at hs
    exact hs
  obtain ⟨na, hna, hba⟩ := ha
  obtain ⟨nb, hnb, hbb⟩ := hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp har
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hbr
  obtain ⟨p, minimum, _, _, st, hmin, hcenters⟩ :=
    componentRunR_active_plain_centers_with_minimum hrun hactive
  obtain ⟨prea, _, hxa⟩ := hcenters hrow hi (hcoord hna hba) hba
  obtain ⟨preb, _, hxb⟩ := hcenters hrow hj (hcoord hnb hbb) hbb
  have hparent := activeRegion_parent_count hactive
  let ga := st.groups.getD a 0
  let gb := st.groups.getD b 0
  by_cases hg : ga = gb
  · obtain ⟨_, moveA⟩ := actualMember_shift st hparent hmin prea hba (show _ = ga from rfl)
    obtain ⟨_, moveB⟩ := actualMember_shift st hparent hmin preb hbb (show _ = ga from hg.symm)
    have hgap := (CoordsImpl.crossCoordsClusterWith_spec st.hCross)
    have hgap' : 1 ≤ min P.nodeGap P.clusterPad := Int.le_min.mpr ⟨hgap.1, hgap.2.1⟩
    have hij : i ≠ j := by
      intro h
      rw [h] at hi
      exact hne (Option.some.inj (hi.symm.trans hj))
    have half (w : Int) : Int.fdiv w 2 = w / 2 := Int.fdiv_eq_ediv_of_nonneg w (by decide)
    have extendedHalf (w e : Int) : Int.fdiv (w + 2 * e) 2 = w / 2 + e := by
      rw [half, Int.mul_comm 2 e]
      exact Int.add_mul_ediv_right w e (by decide)
    have haLoop : (0 : Int) ≤ na.node.loopExtent := Int.natCast_nonneg _
    have hbLoop : (0 : Int) ≤ nb.node.loopExtent := Int.natCast_nonneg _
    unfold middleXGap
    simp only [middleRect, boxRect, xAt, nodeW, hna, hnb, hxa, hxb, moveA, moveB, half]
    rcases Nat.lt_or_gt_of_ne hij with hij | hji
    · have hs := crossCoordsClusterWith_plain_order st.hCross hrow hij hi hj prea hba
      simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, prea, preb, extendedHalf] at hs
      exact Or.inl (by omega)
    · have hs := crossCoordsClusterWith_plain_order st.hCross hrow hji hj hi preb hbb
      simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, prea, preb, extendedHalf] at hs
      exact Or.inr (by omega)
  · have hpad := (checkedParams_sizing_nonneg hp).2.1
    have hborder := checkedParams_clusterBorderW_ge_one hp
    have hinset : 0 ≤ regionInsetOf P := by unfold regionInsetOf; omega
    have hslot : 0 ≤ P.slot := Int.le_trans (by decide : (0 : Int) ≤ 1)
      (componentRunR_slot_pos hrun)
    have hs := activeDifferentBuckets_gap st hactive hmin hinset hslot
      (actualMember_group_bound st prea) (actualMember_group_bound st preb) hg
    have hA := allocatedMember_crossHull st hparent hmin prea hba (show _ = ga from rfl)
    have hB := allocatedMember_crossHull st hparent hmin preb hbb (show _ = gb from rfl)
    unfold middleXGap
    simp only [middleRect, boxRect, xAt, nodeW, hna, hnb, hxa, hxb]
    rcases hs with hs | hs
    · exact Or.inl (Int.le_trans hA.2 (Int.le_trans hs hB.1))
    · exact Or.inr (Int.le_trans hB.2 (Int.le_trans hs hA.1))

set_option maxHeartbeats 4000000 in
theorem selectedActiveForwardPieces_of_anchorsAtVictimRank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    {s : R6_SelectedLoopPartR e c part} {i v : Nat} {pts : List Point} {rect : Rect}
    (n : SelectedOrdinaryPair s i v pts rect) {spec : RegionSpec} (hused : s.used = some spec)
    (hlane : s.run.lanes.runs.find? (fun l => l.original == n.native.original) = none)
    (hanchors : ForwardAnchorsAtVictimRank s.cg s.run n.native.original v) :
    ActiveForwardPieces e.params s.run n.native.original v := by
  rcases s.dispatch n.edgeAt with
    ⟨hnone, _, _⟩ | ⟨_, _, _, hfound, hactive, _, _, hrouter⟩
  · rw [hused] at hnone
    cases hnone
  let run := s.run
  let p := run.proper
  let r := run.lanes.routing
  let rank := middleRank run v
  let box := middleRect run v
  let heights := run.layers.map (RouteImpl.layerHeight p)
  have hrun := s.hRun
  rw [hfound] at hrun hactive
  obtain ⟨base, hb, hslot, hroute⟩ := routeWithLanesR_spec hrouter
  have hlayers := (route_spec hb).1
  obtain ⟨_, hsizes, _, hcover, hedge⟩ := layersOk_spec hlayers
  have hshape := componentRunR_properShape_someR rfc4CrossCoordsR_metadata_holds _ rfl hrun
  have hforeign := chain_ne n.real _ (hshape n.native.original)
    (fun _ hx => by rw [Option.some.inj (hx.symm.trans n.firstAt)]; exact n.foreignFirst.symm)
    (fun _ hx => by rw [Option.some.inj (hx.symm.trans n.lastAt)]; exact n.foreignLast.symm)
  have hnative := (routePointsWithLanes_mem (componentRunR_routes_eqR hrun)
    (List.mem_of_getElem? n.nativeAt)).1
  have hchain : (edgesOf run.proper n.native.original).isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem (List.mem_of_head? n.firstAt))
  have hrev := activeForward_reversed_false hrouter hnative hchain hlane
  have hsx : r.sourceX = base.sourceX := by change run.lanes.routing.sourceX = _; rw [hroute]; rfl
  have htx : r.targetX = base.targetX := by change run.lanes.routing.targetX = _; rw [hroute]; rfl
  have hrx : r.sourceRun = base.sourceRun := by
    change run.lanes.routing.sourceRun = _
    rw [hroute]
    rfl
  have hborder : (s.cg.nodes.getD v default).border ≠ -2 := by
    rw [List.getD_eq_getElem?_getD, n.nodeAt, Option.getD_some, n.plain]
    decide
  obtain ⟨hboxes, hsep⟩ := componentRunR_plain_rank_bands (exactIds := exactIds) hrun
  obtain ⟨row, hrow, hvrow, hboxLo, hboxHi⟩ := hboxes n.nodeAt n.plain
  change run.layers[rank]? = some row at hrow
  rw [plain_frame_eq_boxRect e.params s.cg run v n.bound hborder] at hboxLo hboxHi
  change run.top.getD rank 0 ≤ box.y at hboxLo
  change box.y + box.h ≤ run.top.getD rank 0 +
    CoordsImpl.layerHeight run.coordinateProper row at hboxHi
  obtain ⟨_, plainRecords⟩ := componentRunR_region_plain_cross_geometry hrun
  obtain ⟨nd, _, hvproper, ndBorder, _⟩ := plainRecords n.nodeAt n.plain
  have hvPlain : middlePlain run v := ⟨nd, hvproper, ndBorder⟩
  have hvX {u : Nat} (hu : u < p.nodes.length) (hne : u ≠ v)
      (hr : middleRank run u = rank) (hpl : middlePlain run u) :
      middleXGap (middleRect run u) box := by
    obtain ⟨other, ho, hurow, _⟩ := hcover u hu
    change run.layers[middleRank run u]? = some other at ho
    rw [hr, hrow] at ho
    exact middleActivePlainRowGap (o := o) e.checked hrun hactive
      (List.mem_of_getElem? hrow) ((Option.some.inj ho).symm ▸ hurow) hvrow hne hpl hvPlain
  obtain ⟨hphysical, -⟩ := componentRunR_boundaryRankBands (exactIds := exactIds) hrun
  have topEntry {u : Nat} {marker : Node} (hm : s.cg.nodes[u]? = some marker)
      (hb : marker.border = -2) (hr : middleRank run u = rank) :
      yAt run.ys u ≤ box.y := by
    obtain ⟨coord, _, hc, _, _, _, hcBorder, _, _, _, _⟩ :=
      componentRunR_active_marker_records hrun hactive hm (Or.inl hb)
    have htop := hcBorder.trans hb
    have hflat : coord.node.border = 2 → coord.node.h = 0 := by
      rw [htop]
      intro he
      cases he
    have hy := (hphysical hc hflat).2.2.1 htop
    change yAt run.ys u = run.top.getD (middleRank run u) 0 at hy
    rw [hr] at hy
    exact Int.le_trans (Int.le_of_eq hy) hboxLo
  have bottomExit {u : Nat} {marker : Node} (hm : s.cg.nodes[u]? = some marker)
      (hb : marker.border = 2) (hr : middleRank run u = rank) :
      tailPortY p run.ys u = yAt run.ys u ∧ box.y + box.h ≤ yAt run.ys u := by
    obtain ⟨coord, actual, hc, ha, _, had, hcBorder, haBorder, _, _, hflat⟩ :=
      componentRunR_active_marker_records hrun hactive hm (Or.inr hb)
    obtain ⟨hcFlat, haFlat⟩ := hflat hb
    have hy := (hphysical hc (fun _ => hcFlat)).2.2.2 (hcBorder.trans hb)
    change yAt run.ys u = run.top.getD (middleRank run u) 0 +
      CoordsImpl.layerHeight run.coordinateProper (run.layers.getD (middleRank run u) []) at hy
    rw [hr] at hy
    have hrowD : run.layers.getD rank [] = row := by
      rw [List.getD_eq_getElem?_getD, hrow, Option.getD_some]
    rw [hrowD] at hy
    have ha' : run.proper.nodes[u]? = some actual := ha
    have hk : frameKind p u = 2 := by simp [p, frameKind, ha', had, haBorder, hb]
    have hh : nodeH p u = 0 := by simp [p, nodeH, ha', haFlat]
    exact ⟨by simp [tailPortY, hk, hh], Int.le_trans hboxHi (Int.le_of_eq hy.symm)⟩
  have hafter {k : Nat} {row' : List Nat} (hk : run.layers[k]? = some row')
      (hlt : k < rank) :
      run.top.getD k 0 + CoordsImpl.layerHeight run.coordinateProper row' ≤ box.y :=
    Int.le_trans (hsep hlt hk hrow) hboxLo
  have hbefore {k : Nat} {row' : List Nat} (hk : run.layers[k]? = some row')
      (hlt : rank < k) : box.y + box.h ≤ run.top.getD k 0 :=
    Int.le_trans hboxHi (hsep hlt hrow hk)
  have hnodeY {u : Nat} (hu : u < p.nodes.length) :
      (middleRank run u < rank → yAt run.ys u + nodeH p u ≤ box.y) ∧
      (rank < middleRank run u → box.y + box.h ≤ yAt run.ys u) := by
    obtain ⟨l, hl, _, _⟩ := hcover u hu
    change run.layers[middleRank run u]? = some l at hl
    have huUpper := componentRunR_active_node_rank_upper (exactIds := exactIds) hrun hactive hu
    have huLower := executedY_ge_rankTop (exactIds := exactIds) hrun hlayers hu
    have hget : run.layers.getD (middleRank run u) [] = l := by
      rw [List.getD_eq_getElem?_getD, hl, Option.getD_some]
    change yAt run.ys u + nodeH p u ≤ run.top.getD (middleRank run u) 0 +
      CoordsImpl.layerHeight run.coordinateProper (run.layers.getD (middleRank run u) []) at huUpper
    rw [hget] at huUpper
    exact ⟨fun h => Int.le_trans huUpper (hafter hl h),
      fun h => Int.le_trans (hbefore hl h) huLower⟩
  have hstarts {k : Nat} (hk : k < p.edges.length) :
      (gapOf p k < rank → (pieceStart p run.ys r k).y ≤ box.y) ∧
      (rank < gapOf p k → box.y + box.h ≤ (pieceStart p run.ys r k).y) := by
    have ht := (hedge k hk).1
    obtain ⟨hup, hlo⟩ := hnodeY ht
    have hh := (hsizes _ ht).2
    constructor
    · intro h
      exact Int.le_trans (tailPortY_le_bottom hh) (hup h)
    · intro h
      have h' := hlo h
      change box.y + box.h ≤ tailPortY p run.ys (edgeAt p k).tail
      unfold tailPortY
      split
      · omega
      · exact Int.le_trans h' (Int.le_add_of_nonneg_right hh)
  have hheadRank {k : Nat} (hk : k < p.edges.length) :
      middleRank run (edgeAt p k).head = gapOf p k + 1 := by
    obtain ⟨ht, _, hstep⟩ := hedge k hk
    obtain ⟨_, _, _, hnn⟩ := hcover _ ht
    change (rk p.rank (edgeAt p k).head).toNat =
      (rk p.rank (edgeAt p k).tail).toNat + 1
    exact (congrArg Int.toNat hstep).trans (Int.toNat_add hnn Int.one_nonneg)
  have hends {k : Nat} (hk : k < p.edges.length) :
      (gapOf p k + 1 < rank → (pieceEnd p run.ys r k).y ≤ box.y) ∧
      (rank < gapOf p k + 1 → box.y + box.h ≤ (pieceEnd p run.ys r k).y) := by
    have hh := (hedge k hk).2.1
    obtain ⟨hup, hlo⟩ := hnodeY hh
    rw [hheadRank hk] at hup hlo
    have hnh := (hsizes _ hh).2
    exact ⟨fun h => Int.le_trans (Int.le_add_of_nonneg_right hnh) (hup h), hlo⟩
  have hport {k : Nat} (hk : k < p.edges.length) :
      middleInX (middleRect run (edgeAt p k).tail) (pieceStart p run.ys r k).x ∧
      middleInX (middleRect run (edgeAt p k).tail) (runOf r k) ∧
      middleInX (middleRect run (edgeAt p k).head) (r.targetX.getD k 0) := by
    have hp := port_ranges hb hk
    have hrunX := run_ranges hb hk
    have hro : runOf r k = runOf base k := by unfold runOf; rw [hrx]
    exact ⟨by simpa only [middleInX, middleRect, boxRect, pieceStart, hsx] using
      And.intro hp.1 hp.2.1,
      by simpa only [middleInX, middleRect, boxRect, hro] using hrunX,
      by simpa only [middleInX, middleRect, boxRect, htx] using hp.2.2⟩
  have hmid {k : Nat} (hk : k ∈ edgesOf p n.native.original)
      (hne : runOf r k ≠ r.targetX.getD k 0) :
      (gapOf p k < rank → midOf p e.params.slot run.top heights r k ≤ box.y) ∧
      (rank < gapOf p k + 1 → box.y + box.h ≤ midOf p e.params.slot run.top heights r k) := by
    have hm := Elegant.Layered.PipelineImpl.mem_edgesOf.mp hk
    have next := (route_segment_facts hb hm.1).1
    have prev : gapOf p k < run.layers.length := Nat.lt_of_succ_lt next
    have hprev := List.getElem?_eq_getElem prev
    have hnext := List.getElem?_eq_getElem next
    have hm' := activeForward_midBounds hrouter hslot
      (halfSlot_reserved (checkedParams_valid e.checked) run (gapOf p k)) hm.1
      (by rw [hm.2]; exact hrev) hne (reservedMidStep (exactIds := exactIds) hrun next)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, q0, _, _, st⟩ := componentRunR_stages hrun
    have hheight (l : List Nat) : RouteImpl.layerHeight p l =
        CoordsImpl.layerHeight run.coordinateProper l := by
      have hn : run.proper.nodes = q0.nodes := by rw [← st.hDrop, OrderImpl.dropSynthetic_nodes]
      change RouteImpl.layerHeight run.proper _ = _
      rw [st.hCoordProper]
      have he : RouteImpl.layerHeight run.proper l = RouteImpl.layerHeight q0 l := by
        have hnh : RouteImpl.nodeH run.proper = RouteImpl.nodeH q0 := by
          funext v
          simp only [RouteImpl.nodeH, hn]
        simp only [RouteImpl.layerHeight, hnh]
      exact he.trans (layerHeight_proxy st.hProxy _)
    constructor
    · intro hlt
      have htop : run.top.getD (gapOf p k + 1) 0 ≤ box.y := by
        rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hlt) with h | h
        · have hb' : run.top.getD (gapOf p k + 1) 0 +
              CoordsImpl.layerHeight run.coordinateProper run.layers[gapOf p k + 1] ≤ box.y :=
            hafter hnext h
          have hh := CoordsImpl.layerHeight_nonneg run.coordinateProper run.layers[gapOf p k + 1]
          omega
        · change run.top.getD (gapOf p k + 1) 0 ≤ box.y
          have h' : gapOf p k + 1 = rank := h
          rw [h']
          exact hboxLo
      exact Int.le_trans hm'.2 htop
    · intro h
      have hbase : box.y + box.h ≤ run.top.getD (gapOf p k) 0 +
          heights.getD (gapOf p k) 0 := by
        change _ ≤ _ + (run.layers.map (RouteImpl.layerHeight p)).getD (gapOf p k) 0
        rw [heights_getD hprev, hheight]
        rcases Nat.lt_or_eq_of_le (show rank ≤ gapOf p k by omega) with h' | h'
        · have hb' := hbefore hprev h'
          have hh := CoordsImpl.layerHeight_nonneg run.coordinateProper run.layers[gapOf p k]
          omega
        · have hrow' := hrow
          rw [h'] at hrow'
          have he := Option.some.inj (hrow'.symm.trans hprev)
          have hboxHi' := hboxHi
          rw [h', he] at hboxHi'
          exact hboxHi'
      exact Int.le_trans hbase hm'.1
  constructor
  · intro k _ hk _
    have hbnd := RouteImpl.mem_edgesOf hk
    obtain ⟨ht, hh, _⟩ := hedge k hbnd
    obtain ⟨hst, hrunX, htarget⟩ := hport hbnd
    obtain ⟨hsUp, hsDown⟩ := hstarts hbnd
    obtain ⟨heUp, heDown⟩ := hends hbnd
    have hxTail (hr : gapOf p k = rank) :
        middleXGap (middleRect run (edgeAt p k).tail) box ∨
          box.y + box.h ≤ (pieceStart p run.ys r k).y := by
      rcases (hanchors hk).1 hr with hp | ⟨marker, hm, hb⟩
      · exact Or.inl (hvX ht (hforeign k hk).1 hr hp)
      · obtain ⟨hy, hh⟩ := bottomExit hm hb hr
        exact Or.inr (by
          change box.y + box.h ≤ tailPortY p run.ys (edgeAt p k).tail
          rwa [hy])
    have hxHead (hr : gapOf p k + 1 = rank) :
        middleXGap (middleRect run (edgeAt p k).head) box ∨
          (pieceEnd p run.ys r k).y ≤ box.y := by
      have he := (hheadRank hbnd).trans hr
      rcases (hanchors hk).2 he with hp | ⟨marker, hm, hb⟩
      · exact Or.inl (hvX hh (hforeign k hk).2 he hp)
      · exact Or.inr (topEntry hm hb he)
    refine ⟨?_, ?_, ?_⟩
    · rcases Nat.lt_trichotomy (gapOf p k) rank with h | h | h
      · exact miss_above (Int.max_le.mpr ⟨hsUp h, hsUp h⟩)
      · rcases hxTail h with hx | hy
        · exact middleMissX hx hst hrunX
        · exact miss_below (Int.le_min.mpr ⟨hy, hy⟩)
      · exact miss_below (Int.le_min.mpr ⟨hsDown h, hsDown h⟩)
    · intro hstraight
      by_cases hEarlier : gapOf p k + 1 < rank
      · exact miss_above (Int.max_le.mpr ⟨hsUp (by omega), heUp hEarlier⟩)
      by_cases hLater : rank < gapOf p k
      · exact miss_below (Int.le_min.mpr ⟨hsDown hLater, heDown (by omega)⟩)
      by_cases htEq : gapOf p k = rank
      · rcases hxTail htEq with hx | hy
        · refine middleMissX hx hrunX ?_
          change middleInX _ (r.targetX.getD k 0)
          rwa [← hstraight]
        · exact miss_below (Int.le_min.mpr ⟨hy, heDown (by omega)⟩)
      · have hhEq : gapOf p k + 1 = rank := by omega
        rcases hxHead hhEq with hx | hy
        · refine middleMissX hx ?_ htarget
          change middleInX _ (runOf r k)
          rwa [hstraight]
        · exact miss_above (Int.max_le.mpr ⟨hsUp (by omega), hy⟩)
    · intro hbent
      obtain ⟨hmUp, hmDown⟩ := hmid hk hbent
      constructor
      · rcases Nat.lt_trichotomy (gapOf p k) rank with h | h | h
        · exact miss_above (Int.max_le.mpr ⟨hsUp h, hmUp h⟩)
        · rcases hxTail h with hx | hy
          · exact middleMissX hx hrunX hrunX
          · exact miss_below (Int.le_min.mpr ⟨hy, hmDown (by omega)⟩)
        · exact miss_below (Int.le_min.mpr ⟨hsDown h, hmDown (by omega)⟩)
      · rcases Nat.lt_trichotomy (gapOf p k + 1) rank with h | h | h
        · exact miss_above (Int.max_le.mpr ⟨hmUp (by omega), heUp h⟩)
        · rcases hxHead h with hx | hy
          · exact middleMissX hx htarget htarget
          · exact miss_above (Int.max_le.mpr ⟨hmUp (by omega), hy⟩)
        · exact miss_below (Int.le_min.mpr ⟨hmDown h, heDown h⟩)
  · intro a b ha hb' hlink
    obtain ⟨ha', hb'', hab, _⟩ := hlink
    have hsame : gapOf p a + 1 = gapOf p b := by
      exact (hheadRank ha').symm.trans (congrArg (middleRank run) hab)
    rcases Nat.lt_trichotomy (gapOf p b) rank with h | h | h
    · exact miss_above (Int.max_le.mpr ⟨(hends ha').1 (by omega), (hstarts hb'').1 h⟩)
    · rcases (hanchors hb').1 h with hp | ⟨marker, hm, hb⟩
      · have hx := hvX (hedge _ hb'').1 (hforeign b hb').1 h hp
        refine middleMissX hx ?_ (hport hb'').1
        rw [← hab]
        exact (hport ha').2.2
      · obtain ⟨hy, hlow⟩ := bottomExit hm hb h
        have hlo : box.y + box.h ≤ (pieceEnd p run.ys r a).y := by
          change box.y + box.h ≤ yAt run.ys (edgeAt p a).head
          rwa [hab]
        have hhi : box.y + box.h ≤ (pieceStart p run.ys r b).y := by
          change box.y + box.h ≤ tailPortY p run.ys (edgeAt p b).tail
          rwa [hy]
        exact miss_below (Int.le_min.mpr ⟨hlo, hhi⟩)
    · exact miss_below (Int.le_min.mpr ⟨(hends ha').2 (by omega), (hstarts hb'').2 h⟩)

private theorem middleCoordinateDummyPlain {P : Params} {exact : List Nat} {s : RegionSpec}
    {cg : Graph} {ranks : List Int} {p0 labeled : Proper} {labels : List MeasuredLabel}
    (hnorm : normalize cg ranks = .ok p0)
    (hlab : Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled)
    {v : Nat} {n : ProperNode}
    (hn : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some n)
    (hd : n.dummy = true) : n.node.border = 0 := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  have hsized {k : Nat} {m : ProperNode} (hm : sized.nodes[k]? = some m)
      (hdm : m.dummy = true) : m.node.border = 0 := by
    have hk := sizeProperPortsX_key P exact labeled k
    change (sized.nodes[k]?).map _ = _ at hk
    cases hs : labeled.nodes[k]? with
    | none => simp [hm, hs] at hk
    | some src =>
      simp only [hm, hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      have hdSrc : src.dummy = true := hk.1.symm.trans hdm
      rcases addLabelNodes_keys _ _ _ (normalize_keys hnorm) hlab k src hs with
        ⟨_, _, hdFalse, _, _⟩ | ⟨_, hb, _⟩
      · rw [hdSrc] at hdFalse
        cases hdFalse
      · exact hk.2.1.trans hb
  have hmat : (materializeDummyPaths (clearProxyExtents bordered)).nodes[v]? = some n := hn
  obtain ⟨m, hm, hmd, hmb, _, _⟩ := materialize_lookup _ hmat
  rw [clearProxyExtents_nodes, List.getElem?_map] at hm
  obtain ⟨old, hold, he⟩ := Option.map_eq_some_iff.mp hm
  have hdOld : old.dummy = true := ((clearF_keys old).1.symm.trans
    ((congrArg ProperNode.dummy he).trans (hmd.symm.trans hd)))
  have hbOld : old.node.border = 0 := by
    obtain ⟨extra, hbordered, hextra⟩ := addClusterBorders_extra titled P.clusterBorderW
    change bordered.nodes = titled.nodes ++ extra at hbordered
    rw [hbordered] at hold
    rcases List.mem_append.mp (List.mem_of_getElem? hold) with ho | ho
    · change old ∈ (sized.nodes.map _) ++ _ at ho
      rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp ho
        have htrim : (if src.node.border == -2 || src.node.border == 2 then
            { src with node := { src.node with w := 0, h := 0 } } else src).dummy =
            src.dummy := by split <;> rfl
        have hsrcD := htrim.symm.trans hdOld
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hsrc
        have hb := hsized hk hsrcD
        simp [hb]
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
        obtain ⟨hq, htop⟩ := List.mem_filter.mp hq
        have hb := hsized (List.mem_zipIdx_iff_getElem?.mp hq) hdOld
        rw [hb] at htop
        cases htop
    · have he' := (hextra old ho).1
      rw [hdOld] at he'
      cases he'
  exact hmb.trans ((congrArg (fun x : ProperNode => x.node.border) he).symm.trans
    ((clearF_keys old).2.1.trans hbOld))

private theorem middleActiveChainNodePlain {P : Params} {exactIds : List String}
    {s : RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp candidate labels order =
      .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    {v : Nat} (hd : ChainNode run.proper v) : middlePlain run v := by
  obtain ⟨out, hout, hdOut⟩ := hd
  obtain ⟨rs, _, _, _, labeled, p, _, _, _, _, placed, q0, _, _, st⟩ := componentRunR_stages hrun
  have hrs := Except.ok.inj (st.hRs.symm.trans hactive)
  rcases st.hPlaced with ⟨hnone, _, _, _, _⟩ | ⟨_, _, _, _, hcross⟩
  · rw [hrs] at hnone
    cases hnone
  obtain ⟨allocation⟩ := crossCoordsR_allocation_stages hcross
  have plen : placed.nodes.length = p.nodes.length := by
    simpa only [List.length_map] using
      congrArg List.length (crossCoordsR_label_metadata hcross).1
  have hpp : allocation.placement.p = p := by rw [allocation.hPlacement]
  have hn : run.proper.nodes = q0.nodes := by rw [← st.hDrop, OrderImpl.dropSynthetic_nodes]
  have hfinal : q0.nodes[v]? = some out := by rwa [← hn]
  obtain ⟨_, _, hlen, _, hp, _⟩ := proxyWidths_rel st.hProxy
  have hv : v < p.nodes.length := by
    have hb := (List.getElem?_eq_some_iff.mp hfinal).1
    rwa [hlen, plen] at hb
  have hvp : p.nodes[v]? = some p.nodes[v] := List.getElem?_eq_getElem hv
  have hsource : allocation.placement.p.nodes[v]? = some p.nodes[v] := by rwa [hpp]
  obtain ⟨m, hm, hmb⟩ := reservedPortsR_preserves_border allocation.hFramesAndPorts hsource
  obtain ⟨m', hm', hmd⟩ := rfc4CrossCoordsR_metadata_holds hcross v _ hvp
  have he := Option.some.inj (hm'.symm.trans hm)
  subst m'
  obtain ⟨q, hq, hqd, hqb, _⟩ := hp v m hm
  have hqEq := Option.some.inj (hq.symm.trans hfinal)
  subst q
  have hpd : p.nodes[v].dummy = true := hmd.symm.trans (hqd.symm.trans hdOut)
  have hc : (coordinateGraphR P (exactDecls exactIds inp) (some s) labeled).nodes[v]? =
      some p.nodes[v] := by rw [st.hCoord]; exact hvp
  exact ⟨out, hout, hqb.trans (hmb.trans (middleCoordinateDummyPlain st.hNorm st.hLabels hc hpd))⟩

private theorem middleChainNodesOrEnds (p : Proper) :
    ∀ {xs : List Nat}, chainRel (ChainLink p) xs → ∀ {k}, k ∈ xs →
      ((∃ j, xs.head? = some j ∧ (edgeAt p k).tail = (edgeAt p j).tail) ∨
        ChainNode p (edgeAt p k).tail) ∧
      ((∃ j, xs.getLast? = some j ∧ (edgeAt p k).head = (edgeAt p j).head) ∨
        ChainNode p (edgeAt p k).head) := by
  intro xs
  induction xs with
  | nil => intro _ k hk; simp at hk
  | cons a rest ih =>
    cases rest with
    | nil =>
      intro _ k hk
      have he : k = a := by simpa using hk
      subst k
      exact ⟨Or.inl ⟨a, rfl, rfl⟩, Or.inl ⟨a, rfl, rfl⟩⟩
    | cons b rest =>
      intro hc k hk
      obtain ⟨_, _, hlink, hd⟩ := hc.1
      rcases List.mem_cons.mp hk with heq | hk
      · rw [heq]
        exact ⟨Or.inl ⟨a, rfl, rfl⟩, Or.inr (hlink.symm ▸ hd)⟩
      · obtain ⟨ht, hh⟩ := ih hc.2 hk
        constructor
        · right
          rcases ht with ⟨j, hj, he⟩ | ht
          · have hjEq : b = j := Option.some.inj hj
            subst j
            rw [he]
            exact hd
          · exact ht
        · rcases hh with ⟨j, hj, he⟩ | hh
          · exact Or.inl ⟨j, by simpa using hj, he⟩
          · exact Or.inr hh

theorem selectedActiveForwardPieces_of_strictlyInteriorRank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    {s : R6_SelectedLoopPartR e c part} {i v : Nat} {pts : List Point} {rect : Rect}
    (n : SelectedOrdinaryPair s i v pts rect) {spec : RegionSpec} (hused : s.used = some spec)
    (hlane : s.run.lanes.runs.find? (fun l => l.original == n.native.original) = none)
    (hstart : gapOf s.run.proper n.first < (rk s.run.proper.rank v).toNat)
    (hend : (rk s.run.proper.rank v).toNat <
      (rk s.run.proper.rank (edgeAt s.run.proper n.last).head).toNat) :
    ActiveForwardPieces e.params s.run n.native.original v := by
  apply selectedActiveForwardPieces_of_anchorsAtVictimRank n hused hlane
  rcases s.dispatch n.edgeAt with
    ⟨hnone, _, _⟩ | ⟨_, _, _, hfound, hactive, _, _, _⟩
  · rw [hused] at hnone
    cases hnone
  have hrun := s.hRun
  rw [hfound] at hrun hactive
  have hshape := componentRunR_properShape_someR rfc4CrossCoordsR_metadata_holds _ rfl hrun
  intro k hk
  obtain ⟨ht, hh⟩ := middleChainNodesOrEnds s.run.proper (hshape n.native.original) hk
  constructor
  · intro hr
    rcases ht with ⟨j, hj, he⟩ | ht
    · have hjEq := Option.some.inj (hj.symm.trans n.firstAt)
      rw [he, hjEq] at hr
      exact ((Nat.ne_of_lt hstart) hr).elim
    · exact Or.inl (middleActiveChainNodePlain (exactIds := exactIds) hrun hactive ht)
  · intro hr
    rcases hh with ⟨j, hj, he⟩ | hh
    · have hjEq := Option.some.inj (hj.symm.trans n.lastAt)
      rw [he, hjEq] at hr
      exact ((Nat.ne_of_lt hend) hr.symm).elim
    · exact Or.inl (middleActiveChainNodePlain (exactIds := exactIds) hrun hactive hh)

#print axioms selectedActiveForwardPieces_of_anchorsAtVictimRank
#print axioms selectedActiveForwardPieces_of_strictlyInteriorRank

/-- The installed coordinate record is a case split, never a universal premise:
active placement may give a top marker positive height. -/
structure SelectedClearanceResidual {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) : Prop where
  loops : R6_SelectedLoopPolylineClearanceR e
  fallbackBottom : ∀ {c : Nat} {part : List Nat × Part} (s : R6_SelectedLoopPartR e c part)
    {i routeKey j boxKey : Nat} {pts : List Point} {rect : Rect},
    R6_SelectedPartPairR e s i routeKey j boxKey pts rect →
    s.loops.find? (fun l => l.1 == routeKey) = none → s.used = none →
    ¬ (∃ exactRes, layoutX exactIds inp o = .ok exactRes) → ExactBottomBracketVacant s.run
  forwardPieces : ∀ {c : Nat} {part : List Nat × Part} (s : R6_SelectedLoopPartR e c part)
    {i routeKey j boxKey : Nat} {pts : List Point} {rect : Rect},
    R6_SelectedPartPairR e s i routeKey j boxKey pts rect →
    s.loops.find? (fun l => l.1 == routeKey) = none →
    ∀ (n : SelectedOrdinaryPair s i j pts rect) {spec : RegionSpec}, s.used = some spec →
    ¬ ActiveCoordFacts e.params s.run → 0 < nodeH s.run.proper j →
    s.run.lanes.runs.find? (fun l => l.original == n.native.original) = none →
    ¬ VictimBeforeForwardPieces s.run n.native.original j →
    ¬ VictimAfterForwardPieces s.run n.native.original j →
    ActiveForwardPieces e.params s.run n.native.original j
  reverseSameRankStubs : ∀ {c : Nat} {part : List Nat × Part} (s : R6_SelectedLoopPartR e c part)
    {i routeKey j boxKey : Nat} {pts : List Point} {rect : Rect},
    R6_SelectedPartPairR e s i routeKey j boxKey pts rect →
    s.loops.find? (fun l => l.1 == routeKey) = none →
    ∀ (n : SelectedOrdinaryPair s i j pts rect) {spec : RegionSpec}, s.used = some spec →
    ¬ ActiveCoordFacts e.params s.run → 0 < nodeH s.run.proper j →
    ∀ {lane : ReversedLane},
    s.run.lanes.runs.find? (fun l => l.original == n.native.original) = some lane →
    ActiveReverseSameRankStubs e.params s.run lane j

private theorem selectedChain_of_residual {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (h : SelectedClearanceResidual e) :
    R6_SelectedChainPartClearanceR e := by
  classical
  intro c part s i routeKey j boxKey pts rect pair hfind
  obtain ⟨n⟩ := selectedOrdinaryPair s hwf pair hfind
  intro hhit
  have hh := n.hit.mp hhit
  have hv : 0 < nodeH s.run.proper j := hh.2.1
  have hnative := List.mem_of_getElem? n.nativeAt
  rcases s.dispatch n.edgeAt with ⟨hused, hcg, hx⟩ | ⟨spec, rm, reserved, hused, hactive, _, _, hrouter⟩
  · rw [hcg] at hx
    have hbottom : ExactBottomBracketVacant s.run := by
      by_cases hex : ∃ exactRes, layoutX exactIds inp o = .ok exactRes
      · obtain ⟨_, hsuccess⟩ := hex
        exact fallbackBracket_of_exactSuccess e hsuccess hwf hfp s hx
      · exact h.fallbackBottom s pair hfind hused hex
    have hshape := componentCandidate_shape (components_nodup e.graph part.1 s.hComp)
      (exactGraph_shape (measuredGraph_shape e.graph0_eq) e.graph_eq) s.candidate
    exact (componentRunX_route_avoids_real_of_bottom_bracket (exactIds := exactIds)
      (checkedParams_valid e.checked)
      hshape hx hbottom hnative n.firstAt n.lastAt n.bound n.real n.foreignFirst n.foreignLast) hh
  · have hr := s.hRun
    rw [hused] at hr hactive
    by_cases hfacts : ActiveCoordFacts e.params s.run
    · have hedge : s.cg.edges[n.native.original]? = some n.edge := by rw [n.original]; exact n.edgeAt
      exact (activeNativeMiss_of_selectedGraph (exactIds := exactIds) e.checked hr hactive hfacts
        hnative hedge n.nonloop n.nodeAt n.plain n.firstAt n.lastAt n.bound n.real
        n.foreignFirst n.foreignLast) hh
    · cases hn : s.run.lanes.runs.find? (fun l => l.original == n.native.original) with
      | none =>
        have hroutes := routePointsWithLanes_mem (componentRunR_routes_eqR hr) hnative
        have hnonempty : (edgesOf s.run.proper n.native.original).isEmpty = false := by
          rw [List.isEmpty_eq_false_iff]
          exact List.ne_nil_of_mem (RouteImpl.mem_of_head' n.firstAt)
        have hflag := activeForward_reversed_false hrouter hroutes.1 hnonempty hn
        have hshape := componentRunR_properShape_someR rfc4CrossCoordsR_metadata_holds spec rfl hr
        obtain ⟨base, hb, hslot, _⟩ := routeWithLanesR_spec hrouter
        have hgapClear {k : Nat} (hk : k ∈ edgesOf s.run.proper n.native.original)
            (hne : runOf s.run.lanes.routing k ≠ s.run.lanes.routing.targetX.getD k 0) :
            let mid := midOf s.run.proper e.params.slot s.run.top
              (s.run.layers.map (RouteImpl.layerHeight s.run.proper)) s.run.lanes.routing k
            Polyline.segMisses ⟨runOf s.run.lanes.routing k, mid⟩
              ⟨s.run.lanes.routing.targetX.getD k 0, mid⟩
              (boxRect s.run.proper s.run.xs s.run.ys j) := by
          have hm := Elegant.Layered.PipelineImpl.mem_edgesOf.mp hk
          have hgap := (route_segment_facts hb hm.1).1
          have hmid := activeForward_midBounds hrouter hslot
            (halfSlot_reserved (checkedParams_valid e.checked) s.run (gapOf s.run.proper k))
            hm.1 (by rw [hm.2]; exact hflag) hne (reservedMidStep (exactIds := exactIds) hr hgap)
          exact activeGapMiss (exactIds := exactIds) hr n.bound n.nodeAt n.plain hgap hmid.1 hmid.2
        have hpieces : ActiveForwardPieces e.params s.run n.native.original j := by
          by_cases before : VictimBeforeForwardPieces s.run n.native.original j
          · exact selectedActiveForwardPieces_of_victimBefore n hused hn before
          · by_cases after : VictimAfterForwardPieces s.run n.native.original j
            · exact selectedActiveForwardPieces_of_victimAfter n hused hn after
            · exact h.forwardPieces s pair hfind n hused hfacts hv hn before after
        exact (activeForward_miss_of_pieces hshape hn hroutes.2 hgapClear hpieces) hh
      | some lane =>
        exact (activeReverse_miss_of_stubs n hr hactive hrouter hn
          (selectedActiveReverseStubs_of_sameRank n hr hactive hrouter hn
            (h.reverseSameRankStubs s pair hfind n hused hfacts hv hn))) hh

def ReindexedSelectedClearanceResidual (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    FixedSizesPositive inp → FrameClearanceSeam inp o res →
    layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
    ∀ (e : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res),
      SelectedClearanceResidual e

theorem reindexedSelectedClearance_of_residual {exactIds : List String}
    {idSets : List (String × List String)} (h : ReindexedSelectedClearanceResidual exactIds idSets) :
    R6_ReindexedSelectedClearance exactIds idSets := by
  intro inp o res hwf hfp hfix hframe hok e
  have residual := h inp o res hwf hfp hfix hframe hok e
  exact ⟨selectedChain_of_residual e hwf hfp residual, residual.loops⟩

end Elegant.Layered.PipelineImpl.RegionOrdinaryC6

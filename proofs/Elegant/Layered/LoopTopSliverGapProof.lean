import Elegant.Layered.LoopFootprintBeyondTopProof
import Elegant.Layered.LoopFootprintBeyondPlainProof
import Elegant.Layered.LoopResTopReservationProof
import Elegant.Layered.LoopResMarkerCopyProof
import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.CoordGraph
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.SideMarkerFactsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Single firing-level marker fact (file-unique name `TopSliverMarkerReady`):
for a group-top `v` (border `-2`) with nonempty loops and a sliver frame `b`
that is nondegenerate, y-overlapping the footprint, and not left of it, the
group's right marker is ready in `b`'s rank layer: coordinate and proper
records for the marker `mR` (border `1`, last of `v`'s path) and for `b`
(non-proxy, with the coordinate `xs` equation), with `mR` layered left of `b`.
Strictly narrower than `TopSliverRightGapBt`: it concludes positioned records,
not the placed-`x` gap. Probe `proofs/wip/Probe/LoopTopSliverGapTProbe.lean`
checks every firing on looping groups beside a foreign titled group (wide
loop label, wide member-loop title, nested group loop): all 48 firings show a
foreign border-3 title copy for `b`, markers of `v` at `b`'s rank in `b`'s
layer, and the right marker left of `b`. -/
def TopSliverMarkerReady (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions) (v b : Nat),
    comp ∈ components e.graph →
    componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run →
    v < (componentCandidate e.graph comp candidate).nodes.length →
    (componentCandidate e.graph comp candidate).nodes.length ≤ b →
    b < run.proper.nodes.length →
    ((componentCandidate e.graph comp candidate).nodes.getD v default).border = -2 →
    loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
      (componentCandidate e.graph comp candidate).slot ≠ [] →
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≠ 0 →
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).h ≠ 0 →
    (frameRect default (componentCandidate e.graph comp candidate) run b).w ≠ 0 →
    (frameRect default (componentCandidate e.graph comp candidate) run b).h ≠ 0 →
    ¬((loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).y +
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).h ≤
        (frameRect default (componentCandidate e.graph comp candidate) run b).y) →
    ¬((frameRect default (componentCandidate e.graph comp candidate) run b).y +
        (frameRect default (componentCandidate e.graph comp candidate) run b).h ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).y) →
    ¬((frameRect default (componentCandidate e.graph comp candidate) run b).x +
        (frameRect default (componentCandidate e.graph comp candidate) run b).w ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x) →
    ∃ (nodeV : Node) (mR : Nat) (nR actualB : ProperNode) (layer : List Nat)
      (j iv : Nat),
      (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV ∧
      nodeV.border = -2 ∧
      run.coordinateProper.nodes[mR]? = some nR ∧
      nR.node.border = 1 ∧
      nR.node.clusterPath.getLast? = some nodeV.decl ∧
      run.coordinateProper.nodes[b]? = some actualB ∧
      ¬(actualB.node.border = -2 ∨ actualB.node.border = 2) ∧
      run.proper.nodes[b]? = some actualB ∧
      run.xs.getD b 0 = run.coordinateXs.getD b 0 ∧
      layer ∈ run.layers ∧
      layer[j]? = some mR ∧ layer[iv]? = some b ∧ j < iv

/-- Single narrow rank fact (file-unique name `TopSliverSpanCovered`): the
group's proper members span the sliver's rank, with witnesses below and
above whose cluster paths contain the group top's declaration. Same firing
binders as `TopSliverMarkerReady` (the alignment seam is not needed for the
rank fact). Probe `proofs/wip/Probe/LoopTopSliverGapTProbe.lean`: `spanOk`
holds on all 48 firings. -/
def TopSliverSpanCovered (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions) (v b : Nat),
    comp ∈ components e.graph →
    componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run →
    v < (componentCandidate e.graph comp candidate).nodes.length →
    (componentCandidate e.graph comp candidate).nodes.length ≤ b →
    b < run.proper.nodes.length →
    ((componentCandidate e.graph comp candidate).nodes.getD v default).border = -2 →
    loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
      (componentCandidate e.graph comp candidate).slot ≠ [] →
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≠ 0 →
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).h ≠ 0 →
    (frameRect default (componentCandidate e.graph comp candidate) run b).w ≠ 0 →
    (frameRect default (componentCandidate e.graph comp candidate) run b).h ≠ 0 →
    ¬((loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).y +
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).h ≤
        (frameRect default (componentCandidate e.graph comp candidate) run b).y) →
    ¬((frameRect default (componentCandidate e.graph comp candidate) run b).y +
        (frameRect default (componentCandidate e.graph comp candidate) run b).h ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).y) →
    ¬((frameRect default (componentCandidate e.graph comp candidate) run b).x +
        (frameRect default (componentCandidate e.graph comp candidate) run b).w ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x) →
    ∃ (nodeV : Node) (low high : Nat) (lowNd highNd : ProperNode),
      (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV ∧
      nodeV.border = -2 ∧
      run.proper.nodes[low]? = some lowNd ∧
      lowNd.node.clusterPath.contains nodeV.decl = true ∧
      (rk run.proper.rank low).toNat ≤ (rk run.proper.rank b).toNat ∧
      run.proper.nodes[high]? = some highNd ∧
      highNd.node.clusterPath.contains nodeV.decl = true ∧
      (rk run.proper.rank b).toNat ≤ (rk run.proper.rank high).toNat

/-- Local copy of the private `lrt_lines_len` in `LoopResTopReservationProof`:
executed lines match the input boxes. -/
private theorem ltsg_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- Frame at a beyond-range index is the placed node rect: the candidate
lookup misses, so the default node (border `0`) takes the `nodeRect` branch. -/
private theorem ltsg_frameB_x {P : Params} {cg : Graph} {run : Run}
    {b : Nat} {actualB : ProperNode}
    (hlen : cg.nodes.length ≤ b)
    (hproperB : run.proper.nodes[b]? = some actualB) :
    (frameRect P cg run b).x = (Labels.rectAt run.proper run.xs run.ys b).x := by
  have hnone : cg.nodes[b]? = none :=
    List.getElem?_eq_none_iff.mpr (by omega)
  have hget : cg.nodes.getD b default = default := by
    simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
  have hgetNe : (cg.nodes.getD b default).border ≠ -2 := by
    rw [hget]; decide
  have hframe : frameRect P cg run b = nodeRect cg run b := by
    unfold frameRect
    simp only []
    exact ite_eq_left (by simpa using hgetNe)
  have hrect : nodeRect cg run b = Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hproperB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hproperB]
  rw [hframe, hrect]

/-- Beyond-range transfer: a proper record past the candidate length comes
back verbatim from the coordinate phase (with its `xs` entry), and its
border is never a proxy border. The coordinate node is original (then
`NodeKeys` forces border `0` past the candidate length), a side marker
(`±1`), or a title copy (`3`); proxy widths preserve the border.
Generalizes the private `pbcp_coord_of_proper` with the border fact proved
from the coordinate classification instead of assumed. -/
private theorem ltsg_beyond_coord {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params
      (componentCandidate e.graph comp candidate) e.measured orderOptions =
      .ok run)
    {b : Nat} {actualB : ProperNode}
    (hle : (componentCandidate e.graph comp candidate).nodes.length ≤ b)
    (hget : run.proper.nodes[b]? = some actualB) :
    run.coordinateProper.nodes[b]? = some actualB ∧
      ¬(actualB.node.border = -2 ∨ actualB.node.border = 2) ∧
      run.xs.getD b 0 = run.coordinateXs.getD b 0 := by
  obtain ⟨_, labeled, _, hc, hkeys, _, _, _⟩ :=
    componentRun_prepared_titled_source e.graph_eq hcomp hrun
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, _, hlenQ, _, hpresAll, hpresSame⟩ := proxyWidths_rel hproxy
  have hlen' : b < run.coordinateProper.nodes.length := by
    have h1 := (List.getElem?_eq_some_iff.mp hget).1
    have h2 : run.proper.nodes.length = q0.nodes.length := by
      have hd := OrderImpl.dropSynthetic_nodes q0
      rw [← hdrop]
      exact congrArg List.length hd
    omega
  obtain ⟨m', hm'⟩ : ∃ m', run.coordinateProper.nodes[b]? = some m' :=
    ⟨_, List.getElem?_eq_getElem hlen'⟩
  have hm'c : (coordinateGraph e.params labeled).nodes[b]? = some m' := by
    rw [hc]; exact hm'
  obtain ⟨nd'', hnd'', _, hbdrP, _⟩ := hpresAll b m' hm'
  have hnd''p : run.proper.nodes[b]? = some nd'' := by
    have hd := OrderImpl.dropSynthetic_nodes q0
    rw [← hdrop, hd]; exact hnd''
  have heq : nd'' = actualB := Option.some.inj (hnd''p.symm.trans hget)
  have hm'bdr : m'.node.border = actualB.node.border := by rw [← hbdrP, heq]
  have hne : ¬(actualB.node.border = -2 ∨ actualB.node.border = 2) := by
    rcases coordinateGraph_lookup e.params labeled hm'c with
      ⟨m, hm, _, hbdrL, _, _⟩ | ⟨_, hbB⟩ | ⟨_, _, _, _, _, hbdrT, _⟩
    · have hb0 : m.node.border = 0 := by
        rcases hkeys b m hm with ⟨n, hn, _, _, _⟩ | ⟨_, hb0, _⟩
        · rw [List.getElem?_eq_none (by omega)] at hn
          cases hn
        · exact hb0
      rw [← heq, hbdrP, hbdrL, hb0]; decide
    · rw [← heq, hbdrP]
      rcases hbB with h | h <;> omega
    · rw [← heq, hbdrP, hbdrT]; decide
  obtain ⟨hrec, hxs⟩ := hpresSame b m' hm' (by rw [hm'bdr]; exact hne)
  have hrecp : run.proper.nodes[b]? = some m' := by
    have hd := OrderImpl.dropSynthetic_nodes q0
    rw [← hdrop, hd]; exact hrec
  have heq2 : m' = actualB := Option.some.inj (hrecp.symm.trans hget)
  refine ⟨by rw [heq2] at hm'; exact hm', hne, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hxs, Option.getD_some]

/-- Full frame at a beyond-range index is the placed node rect. -/
private theorem ltsg_frameB_full {P : Params} {cg : Graph} {run : Run}
    {b : Nat}
    (hlen : cg.nodes.length ≤ b) :
    frameRect P cg run b = nodeRect cg run b := by
  have hnone : cg.nodes[b]? = none := List.getElem?_eq_none_iff.mpr (by omega)
  have hget : cg.nodes.getD b default = default := by
    simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
  have hgetNe : (cg.nodes.getD b default).border ≠ -2 := by rw [hget]; decide
  unfold frameRect
  simp only []
  exact ite_eq_left (by simpa using hgetNe)

/-- Rank tops are nonnegative on executed runs: copy of the `htopNN` block in
`plain_frame_disjoint`, used for the member-hull bottom bound. -/
private theorem ltsg_top_nonneg {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) (r : Nat) :
    0 ≤ run.top.getD r 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, hry, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, _, _, hslots, _, htopEq, _⟩ := CoordsImpl.rankCoordsWith_spec hry
  have hheights : ∀ h ∈ run.layers.map (CoordsImpl.layerHeight
      run.coordinateProper), 0 ≤ h := by
    intro h hh
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hh
    exact CoordsImpl.layerHeight_nonneg _ _
  have hsteps : ∀ s ∈ CoordsImpl.rankSteps P.rankGap P.slot
      run.coordinateProper run.layers (run.routing.gaps.map (fun x => x.slots)),
      0 ≤ s :=
    CoordsImpl.rankSteps_nonneg (by omega) (by omega) _ _ _ hslots
  have hmono : ∀ e ∈ CoordsImpl.topsFrom (0 : Int) 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (fun x => x.slots))), (0 : Int) ≤ e := fun e he =>
    CoordsImpl.topsFrom_ge 0 1 (by omega) (by omega) _ _ 0 hheights hsteps e he
  cases hget : run.top[r]? with
  | none => simp only [List.getD_eq_getElem?_getD, hget, Option.getD_none]; omega
  | some v =>
    simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
    have hmem : v ∈ run.top := List.mem_of_getElem? hget
    rw [htopEq] at hmem
    exact hmono v hmem

/-- A nondegenerate loop footprint forces a nonempty member hull. -/
private theorem ltsg_members_nonempty {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nodeV : Node}
    (hnodeV : cg.nodes[v]? = some nodeV) (hvTop : nodeV.border = -2)
    (hwfp : (loopFootprint cg run labels v).h ≠ 0) :
    groupMemberRects cg run nodeV.decl ≠ [] := by
  intro hnil
  have hfh : (frameRect default cg run v).h = 0 := by
    rw [frameRect_group_span hnodeV hvTop, hnil]
    show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
    rfl
  have hexact : run.exact = [] := componentRun_exact_nil hrun
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hfoot : loopFootprint cg run labels v = ⟨(frameRect default cg run v).x +
      (frameRect default cg run v).w, (frameRect default cg run v).y,
      Loops.extent cg.slot (loopSizes cg.edges labels v cg.slot),
      (frameRect default cg run v).h⟩ := by
    unfold loopFootprint
    simp only [hcon, Bool.false_eq_true, ↓reduceIte]
  have hfp : (loopFootprint cg run labels v).h =
      (frameRect default cg run v).h := by
    rw [hfoot]
  exact hwfp (hfp.trans hfh)

/-- Span below: if no containing node sits at or below the sliver rank, every
member rect lies below the sliver, contradicting the `¬(fr.y + fr.h ≤ fp.y)`
firing premise. Contrapositive of the above-rank `y`-branch of
`plain_frame_disjoint`, replayed for a beyond-range sliver against the loop
footprint (same `y`/`h` as the group frame). -/
private theorem ltsg_span_low {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecution inp o res} {comp : List Nat} {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params
      (componentCandidate e.graph comp candidate) e.measured orderOptions =
      .ok run)
    {v b : Nat} {nodeV : Node}
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvTop : nodeV.border = -2)
    (hle : (componentCandidate e.graph comp candidate).nodes.length ≤ b)
    {actualB : ProperNode}
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hmemNe : groupMemberRects (componentCandidate e.graph comp candidate) run
      nodeV.decl ≠ [])
    (hys2 : ¬((frameRect default (componentCandidate e.graph comp candidate)
        run b).y + (frameRect default (componentCandidate e.graph comp
        candidate) run b).h ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run
          e.measured v).y)) :
    ∃ low lowNd, run.proper.nodes[low]? = some lowNd ∧
      lowNd.node.clusterPath.contains nodeV.decl = true ∧
      (rk run.proper.rank low).toNat ≤ (rk run.proper.rank b).toNat := by
  classical
  refine Classical.byContradiction (fun hcon => ?_)
  have hall : ∀ low lowNd, run.proper.nodes[low]? = some lowNd →
      lowNd.node.clusterPath.contains nodeV.decl = true →
      ¬((rk run.proper.rank low).toNat ≤ (rk run.proper.rank b).toNat) := by
    intro low lowNd hrec hcontains hleQB
    exact hcon ⟨low, lowNd, hrec, hcontains, hleQB⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hry, _, _⟩ :=
    componentRun_spec hrun
  have hranks : run.proper.rank = run.coordinateProper.rank :=
    proper_rank_eq_coordinate hrun
  obtain ⟨lB, hlyB, _, hbBot⟩ := run_node_band hrun hproperB
  have hfr : (frameRect default (componentCandidate e.graph comp candidate)
      run b).y + (frameRect default (componentCandidate e.graph comp
      candidate) run b).h =
      run.ys.getD b 0 + RouteImpl.nodeH run.proper b := by
    rw [ltsg_frameB_full hle, nodeRect_of_record hproperB]
    simp only [RouteImpl.nodeH, hproperB]
  have hexact : run.exact = [] := componentRun_exact_nil hrun
  have hcon2 : run.exact.contains v = false := by simp [hexact]
  have hfoot : loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v = ⟨(frameRect default (componentCandidate e.graph comp
      candidate) run v).x + (frameRect default (componentCandidate e.graph comp
      candidate) run v).w, (frameRect default (componentCandidate e.graph comp
      candidate) run v).y, Loops.extent (componentCandidate e.graph comp
      candidate).slot (loopSizes (componentCandidate e.graph comp candidate).edges
      e.measured v (componentCandidate e.graph comp candidate).slot),
      (frameRect default (componentCandidate e.graph comp candidate)
      run v).h⟩ := by
    unfold loopFootprint
    simp only [hcon2, Bool.false_eq_true, ↓reduceIte]
  have hfpY : (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).y = (frameRect default (componentCandidate e.graph comp
      candidate) run v).y := by
    rw [hfoot]
  have hmem : ∀ r ∈ groupMemberRects (componentCandidate e.graph comp
      candidate) run nodeV.decl,
      run.ys.getD b 0 + RouteImpl.nodeH run.proper b ≤ r.y := by
    intro r hr
    obtain ⟨q, nd, hq, hconQ, hrq⟩ := groupMemberRects_inv hr
    have hltQB : (rk run.proper.rank b).toNat < (rk run.proper.rank q).toNat := by
      refine Classical.byContradiction (fun hleQB => ?_)
      exact hall q nd hq hconQ (by omega)
    have hltQC : (rk run.coordinateProper.rank b).toNat <
        (rk run.coordinateProper.rank q).toNat := by
      rw [hranks] at hltQB
      exact hltQB
    obtain ⟨lQ, hlyQ, hqTop, _⟩ := run_node_band hrun hq
    have hband := CoordsImpl.rankAxis_bands_disjoint hry _ _ lB lQ hltQC
      hlyB hlyQ
    simp only [RouteImpl.nodeH, hproperB] at hbBot
    rw [hrq, rectAt_eq run.proper run.xs run.ys q]
    simp only [RouteImpl.yAt, RouteImpl.nodeH, hproperB]
    omega
  have hcontra : (frameRect default (componentCandidate e.graph comp candidate)
      run b).y + (frameRect default (componentCandidate e.graph comp candidate)
      run b).h ≤ (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).y := by
    rw [hfr, hfpY, frameRect_group_span hnodeV hvTop]
    exact boundsOf_minY_ge_of_all hmemNe hmem
  exact hys2 hcontra

/-- Span above: if no containing node sits at or above the sliver rank, every
member rect lies above the sliver, contradicting the `¬(fp.y + fp.h ≤ fr.y)`
firing premise. Contrapositive of the below-rank `y`-branch of
`plain_frame_disjoint`, replayed for a beyond-range sliver. -/
private theorem ltsg_span_high {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecution inp o res} {comp : List Nat} {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params
      (componentCandidate e.graph comp candidate) e.measured orderOptions =
      .ok run)
    {v b : Nat} {nodeV : Node}
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvTop : nodeV.border = -2)
    (hle : (componentCandidate e.graph comp candidate).nodes.length ≤ b)
    {actualB : ProperNode}
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hys1 : ¬((loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).y + (loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).h ≤
        (frameRect default (componentCandidate e.graph comp candidate)
        run b).y)) :
    ∃ high highNd, run.proper.nodes[high]? = some highNd ∧
      highNd.node.clusterPath.contains nodeV.decl = true ∧
      (rk run.proper.rank b).toNat ≤ (rk run.proper.rank high).toNat := by
  classical
  refine Classical.byContradiction (fun hcon => ?_)
  have hall : ∀ high highNd, run.proper.nodes[high]? = some highNd →
      highNd.node.clusterPath.contains nodeV.decl = true →
      ¬((rk run.proper.rank b).toNat ≤ (rk run.proper.rank high).toNat) := by
    intro high highNd hrec hcontains hleQB
    exact hcon ⟨high, highNd, hrec, hcontains, hleQB⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hry, _, _⟩ :=
    componentRun_spec hrun
  have hranks : run.proper.rank = run.coordinateProper.rank :=
    proper_rank_eq_coordinate hrun
  obtain ⟨lB, hlyB, hbTop, _⟩ := run_node_band hrun hproperB
  have hysNN : 0 ≤ run.ys.getD b 0 :=
    Int.le_trans (ltsg_top_nonneg hrun _) hbTop
  have hfrY : (frameRect default (componentCandidate e.graph comp candidate)
      run b).y = run.ys.getD b 0 := by
    rw [ltsg_frameB_full hle, nodeRect_of_record hproperB]
  have hexact : run.exact = [] := componentRun_exact_nil hrun
  have hcon2 : run.exact.contains v = false := by simp [hexact]
  have hfoot : loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v = ⟨(frameRect default (componentCandidate e.graph comp
      candidate) run v).x + (frameRect default (componentCandidate e.graph comp
      candidate) run v).w, (frameRect default (componentCandidate e.graph comp
      candidate) run v).y, Loops.extent (componentCandidate e.graph comp
      candidate).slot (loopSizes (componentCandidate e.graph comp candidate).edges
      e.measured v (componentCandidate e.graph comp candidate).slot),
      (frameRect default (componentCandidate e.graph comp candidate)
      run v).h⟩ := by
    unfold loopFootprint
    simp only [hcon2, Bool.false_eq_true, ↓reduceIte]
  have hmem : ∀ r ∈ groupMemberRects (componentCandidate e.graph comp
      candidate) run nodeV.decl,
      r.y + r.h ≤ run.ys.getD b 0 := by
    intro r hr
    obtain ⟨q, nd, hq, hconQ, hrq⟩ := groupMemberRects_inv hr
    have hltBQ : (rk run.proper.rank q).toNat < (rk run.proper.rank b).toNat := by
      refine Classical.byContradiction (fun hleQB => ?_)
      exact hall q nd hq hconQ (by omega)
    have hltCQ : (rk run.coordinateProper.rank q).toNat <
        (rk run.coordinateProper.rank b).toNat := by
      rw [hranks] at hltBQ
      exact hltBQ
    obtain ⟨lQ, hlyQ, _, hqBot⟩ := run_node_band hrun hq
    have hband := CoordsImpl.rankAxis_bands_disjoint hry _ _ lQ lB hltCQ
      hlyQ hlyB
    simp only [RouteImpl.nodeH, hq] at hqBot
    rw [hrq, rectAt_eq run.proper run.xs run.ys q]
    simp only [RouteImpl.yAt, RouteImpl.nodeH, hq]
    omega
  have hbot2 := boundsOf_bottom_le_of_all hysNN hmem
  have hfpYS : (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).y + (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).h =
      (boundsOf (groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl) []).bottom := by
    rw [hfoot, frameRect_group_span hnodeV hvTop]
    show (boundsOf (groupMemberRects (componentCandidate e.graph comp
      candidate) run nodeV.decl) []).minY +
      ((boundsOf (groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl) []).bottom -
        (boundsOf (groupMemberRects (componentCandidate e.graph comp candidate)
        run nodeV.decl) []).minY) =
      (boundsOf (groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl) []).bottom
    omega
  have hcontra : (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).y + (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).h ≤
      (frameRect default (componentCandidate e.graph comp candidate)
      run b).y := by
    rw [hfpYS, hfrY]
    exact hbot2
  exact hys1 hcontra

/-- The member span covers the sliver rank: below from `ltsg_span_low`, above
from `ltsg_span_high`, with nonempty members from the nondegenerate loop
footprint. -/
theorem topSliverSpanCovered_holds {inp : Input} {o : Options}
    {res : FamilyResult} :
    TopSliverSpanCovered inp o res := by
  intro e comp candidate run _orderOptions v b _hcomp hrun hv hle hlt hvTop
    _hne _hwfp hhfp _hwfr _hhfr hys1 hys2 _hleft
  obtain ⟨nodeV, hnodeV⟩ : ∃ n, (componentCandidate e.graph comp
      candidate).nodes[v]? = some n := ⟨_, List.getElem?_eq_getElem hv⟩
  have hvTop' : nodeV.border = -2 := by
    have hget : (componentCandidate e.graph comp candidate).nodes.getD v
        default = nodeV := by
      rw [List.getD_eq_getElem?_getD, hnodeV]; rfl
    rw [← hget]; exact hvTop
  obtain ⟨actualB, hproperB⟩ : ∃ nd, run.proper.nodes[b]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hmemNe := ltsg_members_nonempty hrun hnodeV hvTop' hhfp
  obtain ⟨low, lowNd, hlowRec, hlowCon, hlowLe⟩ :=
    ltsg_span_low hrun hnodeV hvTop' hle hproperB hmemNe hys2
  obtain ⟨high, highNd, hhighRec, hhighCon, hhighGe⟩ :=
    ltsg_span_high hrun hnodeV hvTop' hle hproperB hys1
  exact ⟨nodeV, low, high, lowNd, highNd, hnodeV, hvTop', hlowRec, hlowCon,
    hlowLe, hhighRec, hhighCon, hhighGe⟩

/-- The group's right marker in the sliver's layer: the member span feeds
`bracketMarkersAtRank'`, the pair shares the sliver rank, hence its layer. -/
private theorem ltsg_marker_layer {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hspan : TopSliverSpanCovered inp o res)
    {e : SceneExecution inp o res} {comp : List Nat} {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params
      (componentCandidate e.graph comp candidate) e.measured orderOptions =
      .ok run)
    {v b : Nat}
    (hcomp : comp ∈ components e.graph)
    (hv : v < (componentCandidate e.graph comp candidate).nodes.length)
    (hle : (componentCandidate e.graph comp candidate).nodes.length ≤ b)
    (hlt : b < run.proper.nodes.length)
    (hvTop : ((componentCandidate e.graph comp candidate).nodes.getD v
      default).border = -2)
    (_hne : loopSizes (componentCandidate e.graph comp candidate).edges
      e.measured v (componentCandidate e.graph comp candidate).slot ≠ [])
    (_hwfp : (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).w ≠ 0)
    (_hhfp : (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).h ≠ 0)
    (_hwfr : (frameRect default (componentCandidate e.graph comp candidate)
      run b).w ≠ 0)
    (_hhfr : (frameRect default (componentCandidate e.graph comp candidate)
      run b).h ≠ 0)
    (_hys1 : ¬((loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).y + (loopFootprint (componentCandidate e.graph comp
        candidate) run e.measured v).h ≤
        (frameRect default (componentCandidate e.graph comp candidate)
        run b).y))
    (_hys2 : ¬((frameRect default (componentCandidate e.graph comp candidate)
        run b).y + (frameRect default (componentCandidate e.graph comp
        candidate) run b).h ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).y))
    (_hleft : ¬((frameRect default (componentCandidate e.graph comp candidate)
        run b).x + (frameRect default (componentCandidate e.graph comp
        candidate) run b).w ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).x)) :
    ∃ (nodeV : Node) (mR : Nat) (nR actualB : ProperNode) (layer : List Nat)
      (j iv : Nat),
      (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV ∧
      nodeV.border = -2 ∧
      run.coordinateProper.nodes[mR]? = some nR ∧
      nR.node.border = 1 ∧
      nR.node.clusterPath.getLast? = some nodeV.decl ∧
      run.coordinateProper.nodes[b]? = some actualB ∧
      ¬(actualB.node.border = -2 ∨ actualB.node.border = 2) ∧
      run.proper.nodes[b]? = some actualB ∧
      run.xs.getD b 0 = run.coordinateXs.getD b 0 ∧
      layer ∈ run.layers ∧
      layer[j]? = some mR ∧ layer[iv]? = some b := by
  obtain ⟨nodeV, hnodeV⟩ : ∃ n, (componentCandidate e.graph comp
      candidate).nodes[v]? = some n := ⟨_, List.getElem?_eq_getElem hv⟩
  have hvTop' : nodeV.border = -2 := by
    have hget : (componentCandidate e.graph comp candidate).nodes.getD v
        default = nodeV := by
      rw [List.getD_eq_getElem?_getD, hnodeV]; rfl
    rw [← hget]; exact hvTop
  obtain ⟨actualB, hproperB⟩ : ∃ nd, run.proper.nodes[b]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨hcoordB, hbne, hxsB⟩ := ltsg_beyond_coord e hcomp hrun hle hproperB
  obtain ⟨nodeVS, low, high, lowNd, highNd, hnodeVS, _, hlowRec, hlowCon,
      hlowLe, hhighRec, hhighCon, hhighGe⟩ :=
    hspan e comp candidate run orderOptions v b hcomp hrun hv hle hlt hvTop
      _hne _hwfp _hhfp _hwfr _hhfr _hys1 _hys2 _hleft
  have hVS : nodeVS = nodeV := Option.some.inj (hnodeVS.symm.trans hnodeV)
  obtain ⟨mL, mR, nL, nR, hcoordL, hbL, hlastL, hrankL, hcoordR, hbR, hlastR,
      hrankR⟩ :=
    bracketMarkersAtRank' e.graph_eq (ltsg_lines_len e) hwf hfp hcomp hrun
      (rk run.proper.rank b).toNat hlowRec hlowCon hlowLe hhighRec hhighCon
      hhighGe
  rw [hVS] at hlastR
  have hranks : run.proper.rank = run.coordinateProper.rank :=
    proper_rank_eq_coordinate hrun
  obtain ⟨hpropL, _⟩ := componentRun_border_record hrun hcoordL (Or.inl hbL)
  obtain ⟨hpropR, _⟩ := componentRun_border_record hrun hcoordR (Or.inr hbR)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hgeom := (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, _, _, hcov, _⟩ := RouteImpl.layersOk_spec hgeom
  obtain ⟨lB, hlyB, hmemB, hrkBNNproper⟩ := hcov b hlt
  have hrkBNN : 0 ≤ rk run.coordinateProper.rank b := by
    rw [← hranks]; exact hrkBNNproper
  have hrkRmB : rk run.proper.rank mR = rk run.proper.rank b := by
    rw [hranks, hrankR, hranks]; exact Int.toNat_of_nonneg hrkBNN
  have hwR : mR < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hpropR).1
  obtain ⟨lM, hlyM, hmemM, _⟩ := hcov mR hwR
  have hlyEq : lM = lB := by
    rw [hrkRmB] at hlyM
    exact Option.some.inj (hlyM.symm.trans hlyB)
  rw [hlyEq] at hmemM
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemM
  obtain ⟨iv, hiv⟩ := List.mem_iff_getElem?.mp hmemB
  have hlayer : lB ∈ run.layers := by
    obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyB
    rw [← hmemEq]; exact List.getElem_mem hmemLT
  exact ⟨nodeV, mR, nR, actualB, lB, j, iv, hnodeV, hvTop', hcoordR, hbR,
    hlastR, hcoordB, hbne, hproperB, hxsB, hlayer, hj, hiv⟩

/-- The footprint's `x` is the group hull's right edge. -/
private theorem ltsg_hull_right_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nodeV : Node}
    (hnodeV : cg.nodes[v]? = some nodeV) (hvTop : nodeV.border = -2) :
    (loopFootprint cg run labels v).x =
      (boundsOf (groupBorderRects cg run nodeV.decl) []).right := by
  have hexact : run.exact = [] := componentRun_exact_nil hrun
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hfoot : loopFootprint cg run labels v = ⟨(frameRect default cg run v).x +
      (frameRect default cg run v).w, (frameRect default cg run v).y,
      Loops.extent cg.slot (loopSizes cg.edges labels v cg.slot),
      (frameRect default cg run v).h⟩ := by
    unfold loopFootprint
    simp only [hcon, Bool.false_eq_true, ↓reduceIte]
  rw [hfoot, frameRect_group_span hnodeV hvTop]
  show (boundsOf (groupBorderRects cg run nodeV.decl) []).minX +
      ((boundsOf (groupBorderRects cg run nodeV.decl) []).right -
        (boundsOf (groupBorderRects cg run nodeV.decl) []).minX) =
      (boundsOf (groupBorderRects cg run nodeV.decl) []).right
  omega

/-- A beyond-range sliver frame's `x`-span is its placed rect's span. -/
private theorem ltsg_sliver_rect_eq {P : Params} {cg : Graph} {run : Run}
    {b : Nat} {actualB : ProperNode}
    (hlen : cg.nodes.length ≤ b)
    (hproperB : run.proper.nodes[b]? = some actualB) :
    (frameRect P cg run b).x + (frameRect P cg run b).w =
      (Labels.rectAt run.proper run.xs run.ys b).x +
      (Labels.rectAt run.proper run.xs run.ys b).w := by
  rw [ltsg_frameB_full hlen, nodeRect_of_record hproperB,
    rectAt_eq run.proper run.xs run.ys b]
  simp only [RouteImpl.nodeW, hproperB]

/-- `TopSliverMarkerReady` from the span: the marker layer gives positioned
records; left-of-marker applies the reservation shape through the hull
bound, right-of-or-on-marker contradicts the not-left firing premise. -/
theorem topSliverMarkerReady_of_span {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hspan : TopSliverSpanCovered inp o res) :
    TopSliverMarkerReady inp o res := by
  intro e comp candidate run orderOptions v b hcomp hrun hv hle hlt hvTop
    hne hwfp hhfp hwfr hhfr hys1 hys2 hleft
  obtain ⟨nodeV, mR, nR, actualB, layer, j, iv, hnodeV, hvTop', hcoordR, hbR,
      hlastR, hcoordB, hbne, hproperB, hxsB, hlayer, hj, hiv⟩ :=
    ltsg_marker_layer hwf hfp hspan hrun hcomp hv hle hlt hvTop hne hwfp
      hhfp hwfr hhfr hys1 hys2 hleft
  have hfpX := ltsg_hull_right_eq hrun hnodeV hvTop'
  have hfrR := ltsg_sliver_rect_eq (P := default) hle hproperB
  obtain ⟨hpropR, _⟩ := componentRun_border_record hrun hcoordR (Or.inr hbR)
  rcases Nat.lt_or_ge j iv with hltM | hgeM
  · exact ⟨nodeV, mR, nR, actualB, layer, j, iv, hnodeV, hvTop', hcoordR, hbR,
      hlastR, hcoordB, hbne, hproperB, hxsB, hlayer, hj, hiv, hltM⟩
  · rcases Nat.eq_or_lt_of_le hgeM with heq | hgt
    · have heqMB : mR = b := by
        have h1 : layer[j]? = some b := by rw [← heq]; exact hiv
        exact Option.some.inj (hj.symm.trans h1)
      subst heqMB
      have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈
          groupBorderRects (componentCandidate e.graph comp candidate) run
          nodeV.decl :=
        groupBorderRects_mem_of_record hpropR (Or.inr hbR) hlastR
      have hmem2 := (boundsOf_rect_mem hmemR).2
      have hle_fp : (frameRect default (componentCandidate e.graph comp
          candidate) run mR).x + (frameRect default (componentCandidate e.graph
          comp candidate) run mR).w ≤
          (loopFootprint (componentCandidate e.graph comp candidate) run
          e.measured v).x := by
        rw [hfrR, hfpX]
        exact hmem2
      exact absurd hle_fp hleft
    · have hbneR : ¬(nR.node.border = -2 ∨ nR.node.border = 2) := by
        rw [hbR]; decide
      have hsep := componentRun_nonproxy_ordered_intervals e.graph_eq hcomp
        hrun hlayer hgt hiv hj hcoordB hcoordR hbne hbneR
      have hwR : mR < run.proper.nodes.length :=
        (List.getElem?_eq_some_iff.mp hpropR).1
      have hnnW := proper_nodeW_nonneg hrun hwR
      have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈
          groupBorderRects (componentCandidate e.graph comp candidate) run
          nodeV.decl :=
        groupBorderRects_mem_of_record hpropR (Or.inr hbR) hlastR
      have hmem2 := (boundsOf_rect_mem hmemR).2
      simp only [rectAt_eq, RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
        hproperB, hpropR] at hsep hnnW hmem2
      have hle_fp : (frameRect default (componentCandidate e.graph comp
          candidate) run b).x + (frameRect default (componentCandidate e.graph
          comp candidate) run b).w ≤
          (loopFootprint (componentCandidate e.graph comp candidate) run
          e.measured v).x := by
        rw [hfrR, hfpX, rectAt_eq run.proper run.xs run.ys b]
        simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hproperB]
        omega
      exact absurd hle_fp hleft

/-- The `hgap` premise of `topLoopsSliverResidual_holds` for executed runs:
with the right marker ready in the sliver's layer, the marker copy
(`loopFootprintTop_hext_all`) and the bound alignment feed the executed
top reservation (`loopResTopReservation_holds`). -/
theorem topSliverMarkerReady_gap {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hready : TopSliverMarkerReady inp o res) :
    TopSliverRightGapBt inp o res := by
  intro e comp candidate run orderOptions v b hcomp hrun hv hle hlt hvTop hne
    halign hwfp hhfp hwfr hhfr hys1 hys2 hleft
  obtain ⟨nodeV, mR, nR, actualB, layer, j, iv, hnodeV, hvTop', hcoordR, hbR,
    hlastR, hcoordB, hbne, hproperB, hxsB, hlayer, hj, hiv, hltM⟩ :=
    hready e comp candidate run orderOptions v b hcomp hrun hv hle hlt hvTop
      hne hwfp hhfp hwfr hhfr hys1 hys2 hleft
  have hext := loopFootprintTop_hext_all e comp candidate run orderOptions v
    mR nodeV nR hcomp hnodeV hvTop' hrun hcoordR hbR hlastR
  exact loopResTopReservation_holds e hwf hfp hcomp hrun hnodeV hvTop' hcoordR
    hbR hlastR hext halign hcoordB hbne hproperB hxsB hlayer hj hiv hltM

/-- Closed top-sliver residual: with the marker ready, the looping group-top
footprint separates from every sliver frame. -/
theorem topLoopsSliverResidual_closed {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (hready : TopSliverMarkerReady inp o res) :
    TopLoopsSliverResidual inp o res :=
  topLoopsSliverResidual_holds hx (topSliverMarkerReady_gap hwf hfp hready)

/-- Prefixed copy of the private `beyond_sep_of_empty_loops` in
`LoopFootprintBeyondProperProof`: an empty loop-size list gives a zero-width
footprint, so it meets no frame interior. -/
private theorem ltsg_sep_of_empty_loops {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hempty : loopSizes cg.edges labels v cg.slot = [])
    (hexact : run.exact = []) :
    LoopFootprintSeparation cg run labels v b := by
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hext : (if run.exact.contains v then Loops.exactExtent else Loops.extent)
      cg.slot (loopSizes cg.edges labels v cg.slot) = 0 := by
    have h1 : (if run.exact.contains v then Loops.exactExtent else Loops.extent) =
        Loops.extent := by simp only [hcon, Bool.false_eq_true, ↓reduceIte]
    rw [h1, hempty]
    simp [Loops.extent]
  unfold LoopFootprintSeparation loopFootprint
  rw [hext]
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  dsimp only at hx
  omega

/-- Closed beyond-proper footprint seam for one input: replay of the case
split in `loopFootprintBeyondProper_holds` with per-input premises (the
original statement ignores its own `WellFormed`/`framedParents` hypotheses
and applies both residuals at the same input). The plain case is the proved
`plainSliverResidual_holds`; the bottom and empty-loop cases close by the
proved border facts plus the empty-footprint copy; the top-with-loops case
is `topLoopsSliverResidual_closed`. -/
theorem loopFootprintBeyondProper_closed (inp : Input) (o : Options)
    (res : FamilyResult)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (hready : TopSliverMarkerReady inp o res) :
    LoopFootprintBeyondProper inp o res := by
  intro e comp candidate run orderOptions v b hcomp hrun hv hle hlt
  by_cases hv0 : ((componentCandidate e.graph comp candidate).nodes.getD v
      default).border = 0
  · exact plainSliverResidual_holds e comp candidate run orderOptions v b
      hcomp hrun hv hle hlt hv0
  · rcases LoopFootprintOtherBorder_holds e comp candidate run orderOptions v
      hcomp hrun hv hv0 with htop | hbot
    · by_cases hempty : loopSizes
          (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot = []
      · exact ltsg_sep_of_empty_loops hempty (componentRun_exact_nil hrun)
      · exact topLoopsSliverResidual_closed hwf hfp hx hready e comp
          candidate run orderOptions v b hcomp hrun hv hle hlt htop hempty
    · have hempty := LoopFootprintBottomEmpty_holds e comp candidate run
        orderOptions v hcomp hrun hv hbot
      exact ltsg_sep_of_empty_loops hempty (componentRun_exact_nil hrun)

end PipelineImpl
end Layered
end Elegant

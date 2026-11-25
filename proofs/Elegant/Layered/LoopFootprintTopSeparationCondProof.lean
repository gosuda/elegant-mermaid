import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.FlatC6Loops
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Coords
import Elegant.Layered.Labels
import Elegant.Layered.SceneBounds
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.LoopFootprintFactsProof
import Elegant.Layered.Route
import Elegant.Layered.LoopResTopReservationProof
import Elegant.Layered.LoopResMarkerCopyProof

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Per-input loop footprint top separation

Per-input variant of `loopFootprintTopSeparation_holds`: the global
`∀ inp o res` premises are specialised to one executed triple, and the two
residuals are discharged by `loopResTopReservation_hright` and
`loopFootprintTop_hext_all`. Private steps below are prefixed copies of the
corresponding `tsep_*` steps in `LoopFootprintTopSeparationProof`.
-/

/-- Local copy of the general `bind_ok`. -/
private theorem ctsep_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => simp [hx, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [hx, Except.bind] using h⟩
/-- Local copy of `componentRun_exact_nil_general`. -/
private theorem ctsep_exact_nil {P : Params} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (h : componentRun P cg labels orderOptions = .ok run) : run.exact = [] := by
  unfold componentRun at h
  obtain ⟨rr, _, h⟩ := ctsep_bind_ok h
  obtain ⟨p0, _, h⟩ := ctsep_bind_ok h
  obtain ⟨p, _, h⟩ := ctsep_bind_ok h
  obtain ⟨ord, _, h⟩ := ctsep_bind_ok h
  obtain ⟨xs, _, h⟩ := ctsep_bind_ok h
  obtain ⟨routed, _, h⟩ := ctsep_bind_ok h
  obtain ⟨lanes, _, h⟩ := ctsep_bind_ok h
  obtain ⟨yt, _, h⟩ := ctsep_bind_ok h
  obtain ⟨routes, _, h⟩ := ctsep_bind_ok h
  have hfin := Except.ok.inj h
  subst hfin
  rfl

/-- Local copy of `lines_len_general`. -/
private theorem ctsep_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- A degenerate-width frame is disjoint from every loop footprint. -/
private theorem ctsep_sep_of_frame_oob {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hw : (frameRect default cg run b).w = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  omega

/-- A degenerate-height footprint is disjoint from every frame. -/
private theorem ctsep_sep_of_foot_oob {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v : Nat}
    (hh : (loopFootprint cg run labels v).h = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨-, hy⟩
  omega

/-- A candidate frame at a `border = 0` position is its node rect. -/
private theorem ctsep_frame_node {P : Params} {cg : Graph} {run : Run}
    {v : Nat} {node : Node}
    (hget : cg.nodes.getD v default = node) (hb : node.border = 0) :
    frameRect P cg run v = nodeRect cg run v := by
  unfold frameRect
  simp only []
  rw [hget, hb]
  rfl

/-- The footprint of any node in an exact-free run. -/
private theorem ctsep_foot_eq {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v : Nat}
    (hexact : run.exact = []) :
    loopFootprint cg run labels v =
      ⟨(frameRect default cg run v).x + (frameRect default cg run v).w,
        (frameRect default cg run v).y,
        Loops.extent cg.slot (loopSizes cg.edges labels v cg.slot),
        (frameRect default cg run v).h⟩ := by
  unfold loopFootprint
  have hcon : run.exact.contains v = false := by simp [hexact]
  simp only [hcon, Bool.false_eq_true, ↓reduceIte]

private theorem ctsep_fold_right_mono (rs : List Rect) (b : Bounds) :
    b.right ≤ (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).right := by
  induction rs generalizing b with
  | nil => simp
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (by simp only; omega) (ih _)

private theorem ctsep_fold_right_mem (rs : List Rect) (b : Bounds) {r : Rect}
    (hmem : r ∈ rs) :
    r.x + r.w ≤ (rs.foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).right := by
  induction rs generalizing b with
  | nil => simp at hmem
  | cons r0 rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Int.le_trans (by simp only; omega) (ctsep_fold_right_mono rest _)
    · exact ih _ hmem

/-- Every border rectangle's right edge is at most the hull's right edge. -/
private theorem ctsep_borders_right_ge {rs : List Rect} {r : Rect}
    (hmem : r ∈ rs) :
    r.x + r.w ≤ (boundsOf rs []).right := by
  cases rs with
  | nil => simp at hmem
  | cons r0 rest =>
    show r.x + r.w ≤ (((r0 :: rest).foldl (fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩)) (⟨r0.x, r0.y, 0, 0⟩ : Bounds)).right
    exact ctsep_fold_right_mem _ _ hmem

/-- Good-position case: the plain box sits at or before the group's right
marker in its layer. Its frame ends left of the marker's right edge. -/
private theorem ctsep_good_case
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v b : Nat) (nodeV nodeB : Node)
    (actualB : ProperNode) (mR : Nat) (nR : ProperNode)
    (hcomp : comp ∈ components e.graph)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop' : nodeV.border = -2)
    (hnodeB : (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB)
    (hb0' : nodeB.border = 0)
    (hbB0 : actualB.node.border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured oo = .ok run)
    (hpropB : run.proper.nodes[b]? = some actualB)
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hxeqB : run.xs.getD b 0 = run.coordinateXs.getD b 0)
    (hcpmR : run.coordinateProper.nodes[mR]? = some nR)
    (hborderR : nR.node.border = 1)
    (hlastR : nR.node.clusterPath.getLast? = some nodeV.decl)
    (layer : List Nat) (hlayerMem : layer ∈ run.layers)
    (iv j : Nat) (hiv : layer[iv]? = some b) (hj : layer[j]? = some mR)
    (hlt : iv < j) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  have hexact := ctsep_exact_nil hrun
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
  have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
      nodeB := by
    simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
  have hframeV := frameRect_group_span (P := default) (run := run) hnodeV hvtop'
  have hframeB := ctsep_frame_node (P := default) (run := run) hgetB hb0'
  have hfoot := ctsep_foot_eq (cg := componentCandidate e.graph comp candidate)
    (run := run) (labels := e.measured) (v := v) hexact
  have hrb := rectAt_eq run.proper run.xs run.ys b
  have hrm := rectAt_eq run.proper run.xs run.ys mR
  obtain ⟨_, _, _, q0, _, _, _, _, hcross, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, hnp⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hnotProxyR : ¬ (nR.node.border = -2 ∨ nR.node.border = 2) := by
    rw [hborderR]; omega
  obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
  have hmarkRunR : run.proper.nodes[mR]? = some nR := by
    rw [hnodes]; exact hnpRecR
  have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈
      groupBorderRects (componentCandidate e.graph comp candidate) run
        nodeV.decl :=
    groupBorderRects_mem_of_record hmarkRunR (Or.inr hborderR) hlastR
  obtain ⟨_, _, _, hcoordinate, hkeys, _, _, _⟩ :=
    componentRun_prepared_titled_source e.graph_eq hcomp hrun
  have hshape := componentCandidate_shape (components_nodup e.graph comp hcomp)
    (measuredGraph_shape e.graph_eq) candidate
  have huniq : ∀ (u w : Nat) (left right : ProperNode),
      run.coordinateProper.nodes[u]? = some left →
      run.coordinateProper.nodes[w]? = some right →
      left.node.border = 3 → right.node.border = 3 →
      left.node.clusterPath = right.node.clusterPath → u = w := by
    intro u w left right hleft hright hleftBorder hrightBorder hpath
    apply pc_title_unique hkeys hshape
      (by rw [hcoordinate]; exact hleft)
      (by rw [hcoordinate]; exact hright) hleftBorder hrightBorder hpath
  have hsep := CoordsImpl.cluster_all_pairs_separated hcross huniq layer
    hlayerMem iv j b mR actualB nR hlt hiv hj hcoordB hcpmR
    (by rw [hbB0]; omega) (by rw [hbB0]; omega)
    (by rw [hborderR]; omega) (by rw [hborderR]; omega)
  obtain ⟨hng, hcp, _, hsizesNN, _⟩ :=
    CoordsImpl.crossCoordsClusterWith_spec hcross
  have hgap : 1 ≤ min e.params.nodeGap e.params.clusterPad := by omega
  have hwbNN : (0 : Int) ≤ actualB.node.w :=
    (sizesNonneg_lookup hsizesNN b actualB hcoordB).1
  have hwmNN : (0 : Int) ≤ nR.node.w :=
    (sizesNonneg_lookup hsizesNN mR nR hcpmR).1
  obtain ⟨_, hxM⟩ := componentRun_border_record hrun hcpmR (Or.inr hborderR)
  have hstep : RouteImpl.leftOf run.proper run.xs b +
      RouteImpl.nodeW run.proper b ≤
      RouteImpl.leftOf run.proper run.xs mR +
        RouteImpl.nodeW run.proper mR := by
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordB, hcpmR,
      RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hpropB, hmarkRunR,
      hxeqB, hxM,
      Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
    omega
  have hrectB : nodeRect (componentCandidate e.graph comp candidate) run b =
      Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hpropB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hpropB]
  have h1 : (Labels.rectAt run.proper run.xs run.ys b).x +
      (Labels.rectAt run.proper run.xs run.ys b).w =
      RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b := by
    simp only [hrb]
  have h2 : (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
    simp only [hrm]
  have hle : RouteImpl.leftOf run.proper run.xs b +
      RouteImpl.nodeW run.proper b ≤
      (boundsOf (groupBorderRects (componentCandidate e.graph comp candidate) run
        nodeV.decl) []).right :=
    Int.le_trans hstep (by rw [← h2]; exact ctsep_borders_right_ge hmemR)
  unfold LoopFootprintSeparation
  rw [hfoot, hframeV, hframeB, hrectB]
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  dsimp only at hx
  simp only [h1] at hx
  omega

/-- The plain box sits strictly above every member rank. -/
private theorem ctsep_above_case
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v b : Nat) (nodeV nodeB : Node)
    (actualB : ProperNode)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop : nodeV.border = -2)
    (hnodeB : (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB)
    (hb0 : nodeB.border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured oo = .ok run)
    (hpropB : run.proper.nodes[b]? = some actualB)
    (haboveFacts : ∀ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd →
      nd.node.clusterPath.contains nodeV.decl = true →
      (rk run.proper.rank b).toNat < (rk run.proper.rank q).toNat) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  have hexact := ctsep_exact_nil hrun
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
  have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
      nodeB := by
    simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
  have hframeV := frameRect_group_span (P := default) (run := run) hnodeV hvtop
  have hframeB := ctsep_frame_node (P := default) (run := run) hgetB hb0
  have hfoot := ctsep_foot_eq (cg := componentCandidate e.graph comp candidate)
    (run := run) (labels := e.measured) (v := v) hexact
  have hrectB : nodeRect (componentCandidate e.graph comp candidate) run b =
      Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hpropB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hpropB]
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, hry, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  obtain ⟨lB, hlyB, _, hbBot⟩ := run_node_band hrun hpropB
  have hmem : ∀ r ∈ groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl,
      run.ys.getD b 0 + RouteImpl.nodeH run.proper b ≤ r.y := by
    intro r hr
    obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
    obtain ⟨l, hly, hqTop, _⟩ := run_node_band hrun hq
    have hlt : (rk run.coordinateProper.rank b).toNat <
        (rk run.coordinateProper.rank q).toNat := by
      rw [← hranks]
      exact haboveFacts q nd hq hcon
    have hband := CoordsImpl.rankAxis_bands_disjoint hry _ _ _ _ hlt hlyB hly
    rw [hrq, rectAt_eq]
    dsimp only
    simp only [RouteImpl.yAt]
    omega
  by_cases hnil : groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl = []
  · have hh : (loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).h = 0 := by
      rw [hfoot, hframeV, hnil]
      rfl
    exact ctsep_sep_of_foot_oob hh
  · have htop := boundsOf_minY_ge_of_all hnil hmem
    have hnH : RouteImpl.nodeH run.proper b = actualB.node.h := by
      simp only [RouteImpl.nodeH, hpropB]
    unfold LoopFootprintSeparation
    rw [hfoot, hframeV, hframeB, hrectB, rectAt_eq run.proper run.xs run.ys b]
    refine rect_disjoint_of_y (Or.inr ?_)
    dsimp only
    simp only [RouteImpl.yAt]
    omega

/-- The plain box sits strictly below every member rank. -/
private theorem ctsep_below_case
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v b : Nat) (nodeV nodeB : Node)
    (actualB : ProperNode)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop : nodeV.border = -2)
    (hnodeB : (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB)
    (hb0 : nodeB.border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured oo = .ok run)
    (hpropB : run.proper.nodes[b]? = some actualB)
    (hbelowFacts : ∀ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd →
      nd.node.clusterPath.contains nodeV.decl = true →
      (rk run.proper.rank q).toNat < (rk run.proper.rank b).toNat) :
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b := by
  have hexact := ctsep_exact_nil hrun
  have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
      nodeV := by
    simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
  have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
      nodeB := by
    simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
  have hframeV := frameRect_group_span (P := default) (run := run) hnodeV hvtop
  have hframeB := ctsep_frame_node (P := default) (run := run) hgetB hb0
  have hfoot := ctsep_foot_eq (cg := componentCandidate e.graph comp candidate)
    (run := run) (labels := e.measured) (v := v) hexact
  have hrectB : nodeRect (componentCandidate e.graph comp candidate) run b =
      Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hpropB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hpropB]
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, hry, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  obtain ⟨lB, hlyB, hbTop, _⟩ := run_node_band hrun hpropB
  have htopNN := fbs_run_top_nonneg hrun
  have hysWNN : (0 : Int) ≤ run.ys.getD b 0 :=
    Int.le_trans (htopNN _) hbTop
  have hmem : ∀ r ∈ groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl,
      r.y + r.h ≤ run.ys.getD b 0 := by
    intro r hr
    obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
    obtain ⟨l, hly, _, hqBot⟩ := run_node_band hrun hq
    have hlt : (rk run.coordinateProper.rank q).toNat <
        (rk run.coordinateProper.rank b).toNat := by
      rw [← hranks]
      exact hbelowFacts q nd hq hcon
    have hband := CoordsImpl.rankAxis_bands_disjoint hry _ _ _ _ hlt hly hlyB
    rw [hrq, rectAt_eq]
    dsimp only
    simp only [RouteImpl.yAt]
    omega
  by_cases hnil : groupMemberRects (componentCandidate e.graph comp candidate)
      run nodeV.decl = []
  · have hh : (loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).h = 0 := by
      rw [hfoot, hframeV, hnil]
      rfl
    exact ctsep_sep_of_foot_oob hh
  · have hbot := boundsOf_bottom_le_of_all hysWNN hmem
    unfold LoopFootprintSeparation
    rw [hfoot, hframeV, hframeB, hrectB, rectAt_eq run.proper run.xs run.ys b]
    refine rect_disjoint_of_y (Or.inl ?_)
    dsimp only
    simp only [RouteImpl.yAt]
    omega

/-- Per-input top separation: the footprint of a group-top self-loop separates
from every plain box frame. Same proof as `loopFootprintTopSeparation_holds`,
with the global premises specialised to the outer executed triple. -/
theorem loopFootprintTopSeparation_cond (inp : Input) (o : Options)
    (res : FamilyResult)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (hbeyond : LoopFootprintBeyondProper inp o res)
    (hright : ∀ (e : SceneExecution inp o res) (comp : List Nat)
      (candidate : Nat)
      (run : Run) (oo : OrderOptions) (v b : Nat) (nodeV nodeB : Node)
      (actualB : ProperNode) (mR : Nat) (nR : ProperNode),
      comp ∈ components e.graph →
      (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV →
      nodeV.border = -2 →
      (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB →
      nodeB.border = 0 →
      actualB.node.border = 0 →
      componentRun e.params (componentCandidate e.graph comp candidate) e.measured
        oo = .ok run →
      run.proper.nodes[b]? = some actualB →
      run.coordinateProper.nodes[b]? = some actualB →
      run.coordinateProper.nodes[mR]? = some nR →
      nR.node.border = 1 →
      nR.node.clusterPath.getLast? = some nodeV.decl →
      SideMarkerSpanAligned →
      ((nR.node.loopExtent : Int) ≥ Loops.extent
        (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot)) →
      ∀ (layer : List Nat), layer ∈ run.layers →
        ∀ (iv j : Nat), layer[iv]? = some b → layer[j]? = some mR → j < iv →
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x +
          (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≤
          (frameRect default (componentCandidate e.graph comp candidate) run b).x)
    (hext : ∀ (e : SceneExecution inp o res) (comp : List Nat)
      (candidate : Nat)
      (run : Run) (oo : OrderOptions) (v m : Nat) (nodeV : Node) (mk : ProperNode),
      comp ∈ components e.graph →
      (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV →
      nodeV.border = -2 →
      componentRun e.params (componentCandidate e.graph comp candidate) e.measured
        oo = .ok run →
      run.coordinateProper.nodes[m]? = some mk →
      mk.node.border = 1 →
      mk.node.clusterPath.getLast? = some nodeV.decl →
      (mk.node.loopExtent : Int) ≥ Loops.extent
        (componentCandidate e.graph comp candidate).slot
        (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
          (componentCandidate e.graph comp candidate).slot)) :
    LoopFootprintTopSeparation inp o res := by
  intro e comp candidate run oo v b hcomp hb0 hrun hvlen hvtop
  by_cases hblen : b < (componentCandidate e.graph comp candidate).nodes.length
  · obtain ⟨nodeV, hnodeV⟩ : ∃ n,
        (componentCandidate e.graph comp candidate).nodes[v]? = some n :=
      ⟨_, List.getElem?_eq_getElem hvlen⟩
    obtain ⟨nodeB, hnodeB⟩ : ∃ n,
        (componentCandidate e.graph comp candidate).nodes[b]? = some n :=
      ⟨_, List.getElem?_eq_getElem hblen⟩
    have hgetV : (componentCandidate e.graph comp candidate).nodes.getD v default =
        nodeV := by
      simp only [List.getD_eq_getElem?_getD, hnodeV, Option.getD_some]
    have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
        nodeB := by
      simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
    have hvtop' : nodeV.border = -2 := by rw [← hgetV]; exact hvtop
    have hb0' : nodeB.border = 0 := by rw [← hgetB]; exact hb0
    obtain ⟨actualB, hcoordB, hpropB, _, hbB0, hpathB, _, _, _, hxeqB⟩ :=
      componentRun_original_plain_record hrun hnodeB hb0'
    obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, hroute, _, _, _, _⟩ :=
      componentRun_spec hrun
    obtain ⟨_, hrankEq, _, _, _, hnp⟩ := proxyWidths_rel hproxy
    have hranks : run.proper.rank = run.coordinateProper.rank := by
      rw [← hdrop, OrderImpl.dropSynthetic_rank]; exact hrankEq
    have hnodes : run.proper.nodes = q0.nodes := by
      rw [← hdrop, OrderImpl.dropSynthetic_nodes]
    obtain ⟨_, _, _, hcov, _⟩ :=
      RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1
    have hwP : b < run.proper.nodes.length :=
      (List.getElem?_eq_some_iff.mp hpropB).1
    obtain ⟨lB, hlyB, hmemB, hrkBNN⟩ := hcov b hwP
    have hrkWNN : 0 ≤ rk run.coordinateProper.rank b := by
      rw [← hranks]; exact hrkBNN
    have hlayerMem : lB ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyB
      rw [← hmemEq]; exact List.getElem_mem hmemLT
    obtain ⟨iv, hiv⟩ := List.mem_iff_getElem?.mp hmemB
    have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
    by_cases hmemC : actualB.node.clusterPath.contains nodeV.decl = true
    · obtain ⟨_, mR, _, nR, _, _, _, _, hcpmR, hborderR, hlastR, hrankR⟩ :=
        bracketMarkersAtRank' e.graph_eq (ctsep_lines_len e) hwf hfp hcomp
          hrun (rk run.proper.rank b).toNat hpropB hmemC (Nat.le_refl _)
          hpropB hmemC (Nat.le_refl _)
      have hnotProxyR : ¬ (nR.node.border = -2 ∨ nR.node.border = 2) := by
        rw [hborderR]; omega
      obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
      have hmarkRunR : run.proper.nodes[mR]? = some nR := by
        rw [hnodes]; exact hnpRecR
      have hrankmWR : rk run.proper.rank mR = rk run.proper.rank b := by
        rw [hranks, hrankR, hranks]; exact Int.toNat_of_nonneg hrkWNN
      have hwM : mR < run.proper.nodes.length :=
        (List.getElem?_eq_some_iff.mp hmarkRunR).1
      obtain ⟨lM, hlyM, hmemM, -⟩ := hcov mR hwM
      have hlyEq : lM = lB := by
        rw [hrankmWR] at hlyM
        exact Option.some.inj (hlyM.symm.trans hlyB)
      rw [hlyEq] at hmemM
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemM
      rcases Nat.lt_or_ge iv j with hlt | hge
      · exact ctsep_good_case e comp candidate run oo v b nodeV nodeB actualB
          mR nR hcomp hnodeV hvtop' hnodeB hb0' hbB0 hrun hpropB hcoordB hxeqB hcpmR
          hborderR hlastR lB hlayerMem iv j hiv hj hlt
      · rcases Nat.eq_or_lt_of_le hge with heq | hgt
        · have hbm : b = mR := Option.some.inj (hiv.symm.trans (heq ▸ hj))
          subst hbm
          have heq2 := Option.some.inj (hpropB.symm.trans hmarkRunR)
          rw [heq2] at hbB0; omega
        · exact rect_disjoint_of_x (Or.inl (hright e comp candidate
            run oo v b nodeV nodeB actualB mR nR hcomp hnodeV hvtop' hnodeB
            hb0' hbB0 hrun hpropB hcoordB hcpmR hborderR hlastR halign
            (hext e comp candidate run oo v mR nodeV nR hcomp
            hnodeV hvtop' hrun hcpmR hborderR hlastR) lB hlayerMem iv j hiv hj
            hgt))
    · by_cases hLow : ∃ (q : Nat) (nd : ProperNode),
          run.proper.nodes[q]? = some nd ∧
          nd.node.clusterPath.contains nodeV.decl = true ∧
          (rk run.proper.rank q).toNat ≤ (rk run.proper.rank b).toNat
      · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode),
            run.proper.nodes[q]? = some nd ∧
            nd.node.clusterPath.contains nodeV.decl = true ∧
            (rk run.proper.rank b).toNat ≤ (rk run.proper.rank q).toNat
        · obtain ⟨low, lowNd, hlowRec, hlowCon, hlowLe⟩ := hLow
          obtain ⟨high, highNd, hhighRec, hhighCon, hhighGe⟩ := hHigh
          obtain ⟨_, mR, _, nR, _, _, _, _, hcpmR, hborderR, hlastR, hrankR⟩ :=
            bracketMarkersAtRank' e.graph_eq (ctsep_lines_len e) hwf hfp hcomp
              hrun (rk run.proper.rank b).toNat hlowRec hlowCon hlowLe
              hhighRec hhighCon hhighGe
          have hnotProxyR : ¬ (nR.node.border = -2 ∨ nR.node.border = 2) := by
            rw [hborderR]; omega
          obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
          have hmarkRunR : run.proper.nodes[mR]? = some nR := by
            rw [hnodes]; exact hnpRecR
          have hrankmWR : rk run.proper.rank mR = rk run.proper.rank b := by
            rw [hranks, hrankR, hranks]; exact Int.toNat_of_nonneg hrkWNN
          have hwM : mR < run.proper.nodes.length :=
            (List.getElem?_eq_some_iff.mp hmarkRunR).1
          obtain ⟨lM, hlyM, hmemM, -⟩ := hcov mR hwM
          have hlyEq : lM = lB := by
            rw [hrankmWR] at hlyM
            exact Option.some.inj (hlyM.symm.trans hlyB)
          rw [hlyEq] at hmemM
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemM
          rcases Nat.lt_or_ge iv j with hlt | hge
          · exact ctsep_good_case e comp candidate run oo v b nodeV nodeB
              actualB mR nR hcomp hnodeV hvtop' hnodeB hb0' hbB0 hrun hpropB
              hcoordB hxeqB hcpmR hborderR hlastR lB hlayerMem iv j hiv hj hlt
          · rcases Nat.eq_or_lt_of_le hge with heq | hgt
            · have hbm : b = mR := Option.some.inj (hiv.symm.trans (heq ▸ hj))
              subst hbm
              have heq2 := Option.some.inj (hpropB.symm.trans hmarkRunR)
              rw [heq2] at hbB0; omega
            · exact rect_disjoint_of_x (Or.inl (hright e comp candidate
                run oo v b nodeV nodeB actualB mR nR hcomp hnodeV hvtop' hnodeB
                hb0' hbB0 hrun hpropB hcoordB hcpmR hborderR hlastR halign
                (hext e comp candidate run oo v mR nodeV nR
                hcomp hnodeV hvtop' hrun hcpmR hborderR hlastR) lB hlayerMem
                iv j hiv hj hgt))
        · have hbelowFacts : ∀ (q : Nat) (nd : ProperNode),
              run.proper.nodes[q]? = some nd →
              nd.node.clusterPath.contains nodeV.decl = true →
              (rk run.proper.rank q).toNat < (rk run.proper.rank b).toNat := by
            intro q nd hq hc
            refine Classical.byContradiction (fun hle => ?_)
            exact hHigh ⟨q, nd, hq, hc, by omega⟩
          exact ctsep_below_case e comp candidate run oo v b nodeV nodeB actualB
            hnodeV hvtop' hnodeB hb0' hrun hpropB hbelowFacts
      · have haboveFacts : ∀ (q : Nat) (nd : ProperNode),
            run.proper.nodes[q]? = some nd →
            nd.node.clusterPath.contains nodeV.decl = true →
            (rk run.proper.rank b).toNat < (rk run.proper.rank q).toNat := by
          intro q nd hq hc
          refine Classical.byContradiction (fun hle => ?_)
          exact hLow ⟨q, nd, hq, hc, by omega⟩
        exact ctsep_above_case e comp candidate run oo v b nodeV nodeB actualB
          hnodeV hvtop' hnodeB hb0' hrun hpropB haboveFacts
  · by_cases hbproper : b < run.proper.nodes.length
    · exact hbeyond e comp candidate run oo v b hcomp hrun hvlen
        (Nat.le_of_not_gt hblen) hbproper
    · have hnone : (componentCandidate e.graph comp candidate).nodes[b]? = none :=
        List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hblen)
      have hgetB : (componentCandidate e.graph comp candidate).nodes.getD b default =
          default := by
        simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
      have hframeB : frameRect default (componentCandidate e.graph comp candidate)
          run b = nodeRect (componentCandidate e.graph comp candidate) run b :=
        ctsep_frame_node hgetB rfl
      have hproperB : run.proper.nodes.getD b default = default := by
        have hnoneP : run.proper.nodes[b]? = none :=
          List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hbproper)
        simp only [List.getD_eq_getElem?_getD, hnoneP, Option.getD_none]
      have hdefW : (default : ProperNode).node.w = 0 := rfl
      have hwB : (frameRect default (componentCandidate e.graph comp candidate)
          run b).w = 0 := by
        simp only [hframeB, nodeRect, hproperB, hdefW]
      exact ctsep_sep_of_frame_oob hwB

/-- Closed per-input top separation: `hright` and `hext` discharge through
`loopResTopReservation_hright` and `loopFootprintTop_hext_all`. -/
theorem loopFootprintTopSeparation_closed (inp : Input) (o : Options)
    (res : FamilyResult)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (hbeyond : LoopFootprintBeyondProper inp o res) :
    LoopFootprintTopSeparation inp o res := by
  apply loopFootprintTopSeparation_cond inp o res hwf hfp hx hbeyond
  · intro e comp candidate run oo v b nodeV nodeB actualB mR nR hcomp hnodeV
      hvTop hnodeB hbB hbAB hrun hpropB hcoordB hcoordR hbR hlastR halign hext
      layer hlayer iv j hiv hj hlt
    exact loopResTopReservation_hright inp o res e hwf hfp comp candidate run
      oo v b nodeV nodeB actualB mR nR hcomp hnodeV hvTop hnodeB hbB hbAB hrun
      hpropB hcoordB hcoordR hbR hlastR halign hext layer hlayer iv j hiv hj hlt
  · intro e comp candidate run oo v m nodeV mk hcomp hnodeV hvB hrun hcoord hb1
      hlast
    exact loopFootprintTop_hext_all e comp candidate run oo v m nodeV mk hcomp
      hnodeV hvB hrun hcoord hb1 hlast

end PipelineImpl
end Layered
end Elegant

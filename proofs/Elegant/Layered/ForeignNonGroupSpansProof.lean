import Elegant.Layered.CoordGraph
import Elegant.Layered.Coords
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Route
import Elegant.Layered.SizingFacts
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # The non-group foreign-span seam of one executed component run

`ForeignNonGroupSpansClear` (`Layered/ForeignSpansFacts.lean`) is the open seam
for the executed foreign-span clause against a witness `w` that is not a group
declaration.  The measured graph only carries border values `0`, `-2` and `2`
(`componentCandidate_marker_shape`), so a non-group witness is either a plain
node or a group's bottom marker:

* a bottom marker keeps height `0` through the whole pipeline
  (`pc_frame_flat`), so its placed rectangle has an empty `y`-interval and
  cannot meet any interior;
* a plain node separates on `y` whenever its rank lies strictly outside the
  rank range of the group's member nodes, through the executed rank-band
  geometry (`run_node_band`, `rankAxis_bands_disjoint`); an empty member hull
  is a zero-height frame;
* a plain node whose rank lies inside that range separates on `x` through the
  group's border-marker pair: pair existence, pair separation and same-side
  alignment plus same-rank side ordering are the three named one-phase
  residuals below.

`ForeignBorderSpansSeparated` is not consumed: no case compares two group
hulls. -/

/-! ## Generic helpers -/

/-- A rectangle field identity: the placed rect of a node is its left edge,
`y`-coordinate, width and height. -/
theorem rectAt_eq (p : Proper) (xs ys : List Int) (v : Nat) :
    Labels.rectAt p xs ys v =
      ⟨RouteImpl.leftOf p xs v, RouteImpl.yAt ys v,
        RouteImpl.nodeW p v, RouteImpl.nodeH p v⟩ := rfl

/-- A placed rect of a run node, read off its record. -/
theorem nodeRect_of_record {cg : Graph} {run : Run} {i : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[i]? = some nd) :
    nodeRect cg run i =
      ⟨RouteImpl.leftOf run.proper run.xs i, run.ys.getD i 0,
        nd.node.w, nd.node.h⟩ := by
  simp only [nodeRect, RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
    List.getD_eq_getElem?_getD, hnd, Option.getD_some]

/-- A zero-height rectangle on either side makes open interiors disjoint. -/
theorem disjoint_of_height_zero_right {a b : Rect} (hb : b.h = 0) :
    Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

theorem disjoint_of_height_zero_left {a b : Rect} (ha : a.h = 0) :
    Disjoint a b := by
  rw [Disjoint.comm]
  exact disjoint_of_height_zero_right ha

/-- Separated `y`-intervals make open interiors disjoint. -/
theorem rect_disjoint_of_y {a b : Rect} (h : a.y + a.h ≤ b.y ∨ b.y + b.h ≤ a.y) :
    Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

/-- Separated `x`-intervals make open interiors disjoint. -/
theorem rect_disjoint_of_x {a b : Rect} (h : a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x) :
    Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

/-- One step of the rect hull fold. -/
private def hullStep (b : Bounds) (r : Rect) : Bounds :=
  ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩

private theorem hullStep_bounds (b : Bounds) (r : Rect) :
    (hullStep b r).minX ≤ b.minX ∧ (hullStep b r).minX ≤ r.x ∧
      b.right ≤ (hullStep b r).right ∧ r.x + r.w ≤ (hullStep b r).right := by
  unfold hullStep
  dsimp only
  omega

private theorem foldl_hull_bounds : ∀ (l : List Rect) (b : Bounds),
    (l.foldl hullStep b).minX ≤ b.minX ∧ b.right ≤ (l.foldl hullStep b).right := by
  intro l
  induction l with
  | nil => intro b; exact ⟨Int.le_refl _, Int.le_refl _⟩
  | cons first rest ih =>
    intro b
    have hstep := hullStep_bounds b first
    have hrest := ih (hullStep b first)
    exact ⟨Int.le_trans hrest.1 hstep.1, Int.le_trans hstep.2.2.1 hrest.2⟩

private theorem foldl_hull_mem : ∀ (l : List Rect) (b : Bounds) (r : Rect),
    r ∈ l → (l.foldl hullStep b).minX ≤ r.x ∧ r.x + r.w ≤ (l.foldl hullStep b).right := by
  intro l
  induction l with
  | nil => intro b r hr; cases hr
  | cons first rest ih =>
    intro b r hr
    rcases List.mem_cons.mp hr with h | h
    · subst h
      have hstep := hullStep_bounds b r
      have hrest := foldl_hull_bounds rest (hullStep b r)
      exact ⟨Int.le_trans hrest.1 hstep.2.1, Int.le_trans hstep.2.2.2 hrest.2⟩
    · exact ih (hullStep b first) r h

/-- The rect hull of a list contains each member horizontally. -/
theorem boundsOf_rect_mem {rects : List Rect} {r : Rect} (hr : r ∈ rects) :
    (boundsOf rects []).minX ≤ r.x ∧ r.x + r.w ≤ (boundsOf rects []).right := by
  cases rects with
  | nil => cases hr
  | cons first rest =>
    change ((first :: rest).foldl hullStep (⟨first.x, first.y, 0, 0⟩ : Bounds)).minX ≤ r.x ∧
      r.x + r.w ≤ ((first :: rest).foldl hullStep (⟨first.x, first.y, 0, 0⟩ : Bounds)).right
    exact foldl_hull_mem _ _ _ hr

/-- Membership of one side marker's rect in the border hull input. -/
theorem groupBorderRects_mem_of_record {cg : Graph} {run : Run} {decl m : Nat}
    {marker : ProperNode} (hnd : run.proper.nodes[m]? = some marker)
    (hb : marker.node.border = -1 ∨ marker.node.border = 1)
    (hlast : marker.node.clusterPath.getLast? = some decl) :
    Labels.rectAt run.proper run.xs run.ys m ∈ groupBorderRects cg run decl := by
  have hcond : ((marker.node.border == -1 || marker.node.border == 1) &&
      marker.node.clusterPath.getLast? == some decl) = true := by
    rcases hb with hb | hb <;> simp [hb, hlast]
  refine (List.mem_filterMap.mpr ⟨(marker, m),
    List.mk_mem_zipIdx_iff_getElem?.mpr hnd, ?_⟩)
  simp [hcond]

/-- Every border-marker rect comes from a run node of that declaration. -/
theorem groupBorderRects_inv {cg : Graph} {run : Run} {decl : Nat} {r : Rect}
    (hr : r ∈ groupBorderRects cg run decl) :
    ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      (nd.node.border = -1 ∨ nd.node.border = 1) ∧
      nd.node.clusterPath.getLast? = some decl ∧
      r = Labels.rectAt run.proper run.xs run.ys q := by
  obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hr
  have hcond : ((a.1.node.border == -1 || a.1.node.border == 1) &&
      a.1.node.clusterPath.getLast? == some decl) = true := by
    by_cases hc : ((a.1.node.border == -1 || a.1.node.border == 1) &&
      a.1.node.clusterPath.getLast? == some decl) = true
    · exact hc
    · simp [hc] at hfa
  rw [hcond] at hfa
  simp only [reduceIte] at hfa
  refine ⟨a.2, a.1, List.mem_zipIdx_iff_getElem?.mp ha, ?_, ?_, (Option.some.inj hfa).symm⟩
  · simpa using (Bool.and_eq_true_iff.mp hcond).1
  · simpa using (Bool.and_eq_true_iff.mp hcond).2

/-- Every member rect comes from a run node whose cluster path contains the
declaration. -/
theorem groupMemberRects_inv {cg : Graph} {run : Run} {decl : Nat} {r : Rect}
    (hr : r ∈ groupMemberRects cg run decl) :
    ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains decl = true ∧
      r = Labels.rectAt run.proper run.xs run.ys q := by
  obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hr
  cases hval : a.1.node.clusterPath.contains decl with
  | true =>
    rw [hval] at hfa
    simp only [reduceIte] at hfa
    exact ⟨a.2, a.1, List.mem_zipIdx_iff_getElem?.mp ha, hval, (Option.some.inj hfa).symm⟩
  | false =>
    rw [hval] at hfa
    simp at hfa

/-! ## The executed run's node records and rank bands -/

/-- Every run node's record agrees with a coordinate-phase record on border and
height. -/
theorem run_record_source {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {q : Nat} {nd : ProperNode} (hq : run.proper.nodes[q]? = some nd) :
    ∃ cw : ProperNode, run.coordinateProper.nodes[q]? = some cw ∧
      cw.node.border = nd.node.border ∧ cw.node.h = nd.node.h := by
  obtain ⟨_ranks, _p0, _labeled, q0, _hn, _hlabeled, _hc, _ordp, _cross,
    hproxy, hdrop, _hroute, _hr2, _hry, _hys, _hroutes⟩ :=
    componentRun_spec hrun
  obtain ⟨_edges, _rank, hlen, _xlen, hrecords, _nonproxy⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq0 : q0.nodes[q]? = some nd := by rw [← hnodes]; exact hq
  have hqLen : q < run.coordinateProper.nodes.length := by
    have hq0len : q < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0).1
    omega
  have hsource : run.coordinateProper.nodes[q]? =
      some (run.coordinateProper.nodes[q]'hqLen) :=
    List.getElem?_eq_getElem hqLen
  obtain ⟨final, hfinal, _dummy, hborder, hheight⟩ := hrecords q _ hsource
  have heq : final = nd := Option.some.inj (hfinal.symm.trans hq0)
  refine ⟨_, hsource, ?_, ?_⟩
  · exact hborder.symm.trans (congrArg (fun n => n.node.border) heq)
  · exact hheight.symm.trans (congrArg (fun n => n.node.h) heq)

/-- Every placed run node lies inside its rank band: its `y` is at least the
band top and its placed bottom at most the band bottom.  Side markers, title
copies and plain nodes are placed inside the band; the flat proxies
(`border ±2`) are placed exactly at band boundaries with height `0`. -/
theorem run_node_band {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {q : Nat} {nd : ProperNode} (hq : run.proper.nodes[q]? = some nd) :
    ∃ l : List Nat,
      run.layers[(rk run.coordinateProper.rank q).toNat]? = some l ∧
      run.top.getD (rk run.coordinateProper.rank q).toNat 0 ≤ run.ys.getD q 0 ∧
      run.ys.getD q 0 + RouteImpl.nodeH run.proper q ≤
        run.top.getD (rk run.coordinateProper.rank q).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper l := by
  obtain ⟨_ranks, _p0, labeled, q0, _hn, _hlabeled, hc, _ordp, _cross,
    hproxy, hdrop, hroute, _hr2, hry, hys, _hroutes⟩ :=
    componentRun_spec hrun
  obtain ⟨_edges, hrankEq, hlen, _xlen, _records, _nonproxy⟩ := proxyWidths_rel hproxy
  obtain ⟨_len, _sz, _members, hcov, _edges2⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_gap, _slot, _len2, _slots, _sizes, _htopEq, hyEq⟩ :=
    CoordsImpl.rankCoordsWith_spec hry
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  have hqP : q < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hq).1
  obtain ⟨cw, hcw, _, hheightEq⟩ := run_record_source hrun hq
  have hnodeH : RouteImpl.nodeH run.proper q = cw.node.h := by
    simp only [RouteImpl.nodeH, hq]
    rw [hheightEq]
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    rw [hyEq]; simp
  obtain ⟨l, hly, hqIn, hrkNN⟩ := hcov q hqP
  have hrkNNcp : 0 ≤ rk run.coordinateProper.rank q := by rw [← hranks]; exact hrkNN
  have hvn : q < run.coordinateProper.nodes.length := by
    rw [← hlen, ← hnodes]
    exact hqP
  have hlycp : run.layers[(rk run.coordinateProper.rank q).toNat]? = some l := by
    rw [← hranks]
    exact hly
  have hcy : q < run.coordinateYs.length := by omega
  have hysRaw : run.ys.getD q 0 =
      (if cw.node.border == -2 then run.top.getD (rk run.coordinateProper.rank q).toNat 0
        else if cw.node.border == 2 then run.top.getD (rk run.coordinateProper.rank q).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper
            (run.layers.getD (rk run.coordinateProper.rank q).toNat [])
        else run.coordinateYs.getD q 0) := by
    rw [← hys]
    exact proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs hcw hcy
  have hLH : 0 ≤ CoordsImpl.layerHeight run.coordinateProper l :=
    CoordsImpl.layerHeight_nonneg _ _
  by_cases hbm2 : cw.node.border = -2
  · have hcgq : (coordinateGraph P labeled).nodes[q]? = some cw := by rw [hc]; exact hcw
    have hflat : cw.node.h = 0 := pc_frame_flat hcgq (Or.inl hbm2)
    have hbeq : (cw.node.border == -2) = true := by rw [hbm2]; rfl
    rw [hbeq] at hysRaw
    simp only [reduceIte] at hysRaw
    exact ⟨l, hlycp, by omega, by omega⟩
  · by_cases hb2 : cw.node.border = 2
    · have hcgq : (coordinateGraph P labeled).nodes[q]? = some cw := by rw [hc]; exact hcw
      have hflat : cw.node.h = 0 := pc_frame_flat hcgq (Or.inr hb2)
      have hbeqF : (cw.node.border == -2) = false := by simp [hbm2]
      have hbeqT : (cw.node.border == 2) = true := by rw [hb2]; rfl
      rw [hbeqF] at hysRaw
      simp only [Bool.false_eq_true, reduceIte] at hysRaw
      rw [hbeqT] at hysRaw
      simp only [reduceIte] at hysRaw
      have hgetL : run.layers.getD (rk run.coordinateProper.rank q).toNat [] = l := by
        rw [List.getD_eq_getElem?_getD, hlycp]
        rfl
      rw [hgetL] at hysRaw
      exact ⟨l, hlycp, by omega, by omega⟩
    · have hbeqF : (cw.node.border == -2) = false := by simp [hbm2]
      have hbeqF2 : (cw.node.border == 2) = false := by simp [hb2]
      rw [hbeqF] at hysRaw
      simp only [Bool.false_eq_true, reduceIte] at hysRaw
      rw [hbeqF2] at hysRaw
      simp only [Bool.false_eq_true, reduceIte] at hysRaw
      have hband := CoordsImpl.rankAxis_node_in_band hry hlycp hqIn hvn
        ((Int.toNat_of_nonneg hrkNNcp).symm)
      have hnodeHcp : CoordsImpl.nodeH run.coordinateProper q = cw.node.h := by
        simp only [CoordsImpl.nodeH, hcw]
      exact ⟨l, hlycp, by omega, by omega⟩

/-! ## Named residuals (one pipeline phase each) -/

/-- Residual (rank assignment and border-marker creation phase): when the nodes
of one group declaration occupy ranks on both sides of a rank `r`, the
coordinate phase has created both the left (`border = -1`) and the right
(`border = 1`) side markers of the declaration at rank `r`.  This
is the executed form of the constraint-edge rank bracket
(`compound_member_constraint_edges` with `rankingGraph_constraint_feasible`)
composed with the marker creation of `coordinateGraph_rank_pair`, restricted
to pipeline-built graphs (`measuredGraph` success and component membership).
It is the one-declaration, one-rank form of the per-rank pair content of
`ForeignClusterRankSpans`. -/
def BracketMarkersAtRank : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl : Nat} (r : Nat) {low high : Nat} {lowNd highNd : ProperNode},
      run.proper.nodes[low]? = some lowNd →
      lowNd.node.clusterPath.contains decl = true →
      (rk run.proper.rank low).toNat ≤ r →
      run.proper.nodes[high]? = some highNd →
      highNd.node.clusterPath.contains decl = true →
      r ≤ (rk run.proper.rank high).toNat →
      ∃ (mL mR : Nat) (nL nR : ProperNode),
        run.coordinateProper.nodes[mL]? = some nL ∧
        nL.node.border = -1 ∧
        nL.node.clusterPath.getLast? = some decl ∧
        rk run.coordinateProper.rank mL = (r : Int) ∧
        run.coordinateProper.nodes[mR]? = some nR ∧
        nR.node.border = 1 ∧
        nR.node.clusterPath.getLast? = some decl ∧
        rk run.coordinateProper.rank mR = (r : Int)

/-- Residual (order phase): a plain run node whose cluster path does not
contain a declaration `decl` keeps its placed `x`-interval clear of the
declaration's marker pair at the same rank: it lies left of the left
(`border = -1`) marker or right of the right (`border = 1`) marker.  This is
the per-rank cluster contiguity of the order pass
(`order_clusters_contiguous`, via `componentRun_nonproxy_ordered_intervals`)
applied to foreign plain witnesses, restricted to pipeline-built graphs
(`measuredGraph` success and component membership). -/
def PlainClearOfSideMarker : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl v mL mR : Nat} {plain nL nR : ProperNode},
      run.proper.nodes[v]? = some plain →
      plain.node.border = 0 →
      plain.node.clusterPath.contains decl = false →
      run.proper.nodes[mL]? = some nL →
      nL.node.border = -1 →
      nL.node.clusterPath.getLast? = some decl →
      run.proper.nodes[mR]? = some nR →
      nR.node.border = 1 →
      nR.node.clusterPath.getLast? = some decl →
      rk run.proper.rank mL = rk run.proper.rank v →
      rk run.proper.rank mR = rk run.proper.rank v →
      RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
          RouteImpl.leftOf run.proper run.xs mL ∨
        RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR ≤
          RouteImpl.leftOf run.proper run.xs v

/-- Residual (alignment phase): two side markers of one declaration on the
same side of an executed run share a single placed `x`-span, whose right edge
is nonnegative; moreover a left (`border = -1`) marker lies left of a right
(`border = 1`) marker of the same declaration at the same rank.  This is the
chain alignment of the horizontal pass (`BorderChainUps` via
`borderChainBlock_of_ups`) transported to the placed `x`-coordinates, together
with the executed left-before-right border order, restricted to
pipeline-built graphs (`measuredGraph` success and component membership). -/
def SideMarkerSpanAligned : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl m m' : Nat} {marker marker' : ProperNode},
      run.proper.nodes[m]? = some marker →
      (marker.node.border = -1 ∨ marker.node.border = 1) →
      marker.node.clusterPath.getLast? = some decl →
      run.proper.nodes[m']? = some marker' →
      (marker'.node.border = -1 ∨ marker'.node.border = 1) →
      marker'.node.clusterPath.getLast? = some decl →
      (marker.node.border = marker'.node.border →
        RouteImpl.leftOf run.proper run.xs m =
          RouteImpl.leftOf run.proper run.xs m' ∧
        RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m =
          RouteImpl.leftOf run.proper run.xs m' + RouteImpl.nodeW run.proper m') ∧
      0 ≤ RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m ∧
      ((marker.node.border = -1 ∧ marker'.node.border = 1 ∧
        rk run.proper.rank m = rk run.proper.rank m') →
        RouteImpl.leftOf run.proper run.xs m ≤
          RouteImpl.leftOf run.proper run.xs m' ∧
        RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m ≤
          RouteImpl.leftOf run.proper run.xs m' + RouteImpl.nodeW run.proper m')

/-! ## The bottom-marker case -/

/-- A bottom marker of the measured graph keeps height `0` through the executed
pipeline, so its placed frame rectangle is disjoint from every rectangle. -/
theorem bottomMarker_frame_disjoint {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {w : Nat} {wNode : Node} (hw : cg.nodes[w]? = some wNode)
    (hbottom : wNode.border = 2) (u : Nat) :
    Disjoint (frameRect P cg run u) (frameRect P cg run w) := by
  obtain ⟨_ranks, _p0, labeled, q0, hn, hlabeled, hc, _ordp, _cross,
    hproxy, hdrop, _hroute, _hr2, _hry, _hys, _hroutes⟩ :=
    componentRun_spec hrun
  obtain ⟨_edges, _rank, _nlen, _xlen, hrecords, _nonproxy⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hlabRec : labeled.nodes[w]? = some (⟨wNode, false, none, false⟩ : ProperNode) :=
    addLabelNodes_untouched_node hlabeled (normalize_node_record hn hw) rfl
  have hdummyW : (⟨wNode, false, none, false⟩ : ProperNode).dummy = false := rfl
  have hcpRec : (coordinateGraph P labeled).nodes[w]? =
      some (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))) :=
    coordinateGraph_marker_record hlabRec (Or.inr hbottom) hdummyW
  have hcpBorder : (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))).node.border
      = wNode.border :=
    (clearF_keys _).2.1.trans (titleF_keys _).2.1
  have hcpFlat : (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))).node.h = 0 :=
    pc_frame_flat hcpRec (Or.inr (hcpBorder.trans hbottom))
  have hrunCpRec : run.coordinateProper.nodes[w]? =
      some (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))) := by
    rw [← hc]; exact hcpRec
  obtain ⟨final, hfinal, _dummy, _border, hfinalH⟩ := hrecords w _ hrunCpRec
  have hpropW' : run.proper.nodes[w]? = some final := by rw [hnodes]; exact hfinal
  have hgetW : cg.nodes.getD w default = wNode := by
    rw [List.getD_eq_getElem?_getD, hw]; rfl
  have hframeW : frameRect P cg run w = nodeRect cg run w := by
    unfold frameRect
    simp only []
    rw [hgetW, hbottom]
    rfl
  rw [hframeW, nodeRect_of_record hpropW']
  refine disjoint_of_height_zero_right ?_
  rw [hfinalH]
  exact hcpFlat

/-! ## The plain-witness case -/

/-- A plain witness separates from the group's frame on `y` whenever its rank
is outside the member rank range, and on `x` through the border-marker pair
span whenever inside; the marker facts are the three residuals. -/
theorem plain_frame_disjoint {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (hbracket : BracketMarkersAtRank)
    (horder : PlainClearOfSideMarker)
    (halign : SideMarkerSpanAligned)
    {u w : Nat} {uNode wNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hw : (componentCandidate graph comp candidate).nodes[w]? = some wNode)
    (hgroupU : uNode.border = -2) (hplain : wNode.border = 0)
    (hpathW : wNode.clusterPath.contains uNode.decl = false) :
    Disjoint (frameRect P (componentCandidate graph comp candidate) run u)
      (frameRect P (componentCandidate graph comp candidate) run w) := by
  obtain ⟨actual, _coord, hpropW, _dummy, hbW0, hpathWeq, _edge, _wmin, _heq, _xeq⟩ :=
    componentRun_original_plain_record hrun hw hplain
  have hgetW : (componentCandidate graph comp candidate).nodes.getD w default = wNode := by
    rw [List.getD_eq_getElem?_getD, hw]; rfl
  have hframeW : frameRect P (componentCandidate graph comp candidate) run w =
      nodeRect (componentCandidate graph comp candidate) run w := by
    unfold frameRect
    simp only []
    rw [hgetW, hplain]
    rfl
  obtain ⟨_ranks, _p0, _labeled, q0, _hn, _hlabeled, _hc, _ordp, _cross,
    hproxy, hdrop, hroute, _hr2, hry, _hys, _hroutes⟩ :=
    componentRun_spec hrun
  obtain ⟨_edges, hrankEq, _nlen, _xlen, _records, hnp⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  obtain ⟨_len, _sz, _members, hcov, _edges2⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨hgap, hslot, _len2, hslots, _sizes, htopEq, _hyEq⟩ :=
    CoordsImpl.rankCoordsWith_spec hry
  have htopNN : ∀ r : Nat, (0 : Int) ≤ run.top.getD r 0 := by
    intro r
    have hheights : ∀ h ∈ run.layers.map (CoordsImpl.layerHeight run.coordinateProper),
        0 ≤ h := by
      intro h hh
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hh
      exact CoordsImpl.layerHeight_nonneg _ _
    have hsteps : ∀ s ∈ CoordsImpl.rankSteps P.rankGap P.slot run.coordinateProper
        run.layers (run.routing.gaps.map (fun x => x.slots)), 0 ≤ s :=
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
  have hwP : w < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hpropW).1
  obtain ⟨lW, hlyW, hwTopBand, hwBotBand⟩ := run_node_band hrun hpropW
  have hcovw := hcov w hwP
  obtain ⟨-, -, -, hwNN⟩ := hcovw
  have hrkWNN : 0 ≤ rk run.coordinateProper.rank w := by rw [← hranks]; exact hwNN
  have hysWNN : (0 : Int) ≤ run.ys.getD w 0 :=
    Int.le_trans (htopNN _) hwTopBand
  by_cases hLow : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains uNode.decl = true ∧
      (rk run.coordinateProper.rank q).toNat ≤ (rk run.coordinateProper.rank w).toNat
  · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains uNode.decl = true ∧
      (rk run.coordinateProper.rank w).toNat ≤ (rk run.coordinateProper.rank q).toNat
    · -- the bracket case: marker pair at w's rank, aligned span, foreign clearance
      obtain ⟨low, lowNd, hlowRec, hlowCon, hlowLe⟩ := hLow
      obtain ⟨high, highNd, hhighRec, hhighCon, hhighGe⟩ := hHigh
      rw [← hranks] at hlowLe hhighGe
      obtain ⟨mL, mR, nL, nR, hcpmL, hborderL, hlastL, hrankL,
        hcpmR, hborderR, hlastR, hrankR⟩ :=
        hbracket hgraph hcomp hrun (rk run.proper.rank w).toNat
          hlowRec hlowCon hlowLe hhighRec hhighCon hhighGe
      have hnotProxyL : ¬(nL.node.border = -2 ∨ nL.node.border = 2) := by
        rw [hborderL]; omega
      have hnotProxyR : ¬(nR.node.border = -2 ∨ nR.node.border = 2) := by
        rw [hborderR]; omega
      obtain ⟨hnpRecL, -⟩ := hnp mL nL hcpmL hnotProxyL
      obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
      have hmarkRunL : run.proper.nodes[mL]? = some nL := by
        rw [hnodes]; exact hnpRecL
      have hmarkRunR : run.proper.nodes[mR]? = some nR := by
        rw [hnodes]; exact hnpRecR
      have hrankmWL : rk run.proper.rank mL = rk run.proper.rank w := by
        rw [hranks, hrankL, hranks]
        exact Int.toNat_of_nonneg hrkWNN
      have hrankmWR : rk run.proper.rank mR = rk run.proper.rank w := by
        rw [hranks, hrankR, hranks]
        exact Int.toNat_of_nonneg hrkWNN
      have hrankLR : rk run.proper.rank mL = rk run.proper.rank mR := by
        rw [hrankmWL, hrankmWR]
      have hnotMem : actual.node.clusterPath.contains uNode.decl = false := by
        rw [hpathWeq]
        exact hpathW
      obtain hsep :=
        horder hgraph hcomp hrun hpropW hbW0 hnotMem
          hmarkRunL hborderL hlastL hmarkRunR hborderR hlastR hrankmWL hrankmWR
      have hmemRectL : Labels.rectAt run.proper run.xs run.ys mL ∈
          groupBorderRects (componentCandidate graph comp candidate) run uNode.decl :=
        groupBorderRects_mem_of_record hmarkRunL (Or.inl hborderL) hlastL
      have hneRects : groupBorderRects (componentCandidate graph comp candidate) run uNode.decl ≠ [] := by
        intro hnil
        rw [hnil] at hmemRectL
        simp at hmemRectL
      have hborderLOr : nL.node.border = -1 ∨ nL.node.border = 1 :=
        Or.inl hborderL
      have hborderROr : nR.node.border = -1 ∨ nR.node.border = 1 :=
        Or.inr hborderR
      have hcross :=
        (halign hgraph hcomp hrun hmarkRunL hborderLOr hlastL
          hmarkRunR hborderROr hlastR).2.2 ⟨hborderL, hborderR, hrankLR⟩
      have hall : ∀ r ∈ groupBorderRects (componentCandidate graph comp candidate) run uNode.decl,
          RouteImpl.leftOf run.proper run.xs mL ≤ r.x ∧
            r.x + r.w ≤ RouteImpl.leftOf run.proper run.xs mR +
              RouteImpl.nodeW run.proper mR := by
        intro r hr
        obtain ⟨q, nd, hq, hbq, hlastq, hrq⟩ := groupBorderRects_inv hr
        rcases hbq with hbqL | hbqR
        · obtain ⟨heq1, heq2⟩ :=
            (halign hgraph hcomp hrun hmarkRunL hborderLOr hlastL
              hq (Or.inl hbqL) hlastq).1 (by rw [hborderL, hbqL])
          rw [hrq, rectAt_eq]
          dsimp only
          rw [heq1, ← heq2]
          exact ⟨Int.le_refl _, hcross.2⟩
        · obtain ⟨heq1, heq2⟩ :=
            (halign hgraph hcomp hrun hmarkRunR hborderROr hlastR
              hq (Or.inr hbqR) hlastq).1 (by rw [hborderR, hbqR])
          rw [hrq, rectAt_eq]
          dsimp only
          refine ⟨?_, ?_⟩
          · rw [← heq1]; exact hcross.1
          · omega
      have hnonnegR :=
        (halign hgraph hcomp hrun hmarkRunR hborderROr hlastR
          hmarkRunR hborderROr hlastR).2.1
      have hminX := boundsOf_minX_ge_of_all hneRects (fun r hr => (hall r hr).1)
      have hright := boundsOf_right_le_of_all hnonnegR
        (fun r hr => (hall r hr).2)
      have hcontain := boundsOf_rect_mem hmemRectL
      rw [rectAt_eq] at hcontain
      rw [frameRect_group_span hu hgroupU, hframeW, nodeRect_of_record hpropW]
      unfold Disjoint Rect.meetsInterior
      simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
        hpropW, hmarkRunL, hmarkRunR,
        Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)]
        at hsep hcontain hminX hright ⊢
      omega
    · -- every member rank is strictly above w's rank
      have hAllAbove : ∀ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd →
          nd.node.clusterPath.contains uNode.decl = true →
          (rk run.coordinateProper.rank q).toNat < (rk run.coordinateProper.rank w).toNat := by
        intro q nd hrec hcon
        refine Classical.byContradiction (fun hcontra => ?_)
        exact hHigh ⟨q, nd, hrec, hcon, by omega⟩
      have hmem : ∀ r ∈ groupMemberRects (componentCandidate graph comp candidate) run uNode.decl,
          r.y + r.h ≤ run.ys.getD w 0 := by
        intro r hr
        obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
        obtain ⟨l, hly, hqTop, hqBot⟩ := run_node_band hrun hq
        have hband := CoordsImpl.rankAxis_bands_disjoint hry
          (rk run.coordinateProper.rank q).toNat (rk run.coordinateProper.rank w).toNat
          l lW (hAllAbove q nd hq hcon) hly hlyW
        simp only [RouteImpl.nodeH, hq] at hqBot
        rw [hrq, rectAt_eq]
        simp only [RouteImpl.yAt, RouteImpl.nodeH, hq]
        omega
      have hbot := boundsOf_bottom_le_of_all hysWNN hmem
      rw [frameRect_group_span hu hgroupU, hframeW, nodeRect_of_record hpropW]
      refine rect_disjoint_of_y (Or.inl ?_)
      have hkey : (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run uNode.decl) []).minY +
          ((boundsOf (groupMemberRects (componentCandidate graph comp candidate) run uNode.decl) []).bottom -
            (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run uNode.decl) []).minY) ≤
          run.ys.getD w 0 := by omega
      exact hkey
  · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains uNode.decl = true ∧
      (rk run.coordinateProper.rank w).toNat ≤ (rk run.coordinateProper.rank q).toNat
    · -- every member rank is strictly below w's rank
      by_cases hmemNil : groupMemberRects (componentCandidate graph comp candidate) run uNode.decl = []
      · rw [frameRect_group_span hu hgroupU, hmemNil]
        refine disjoint_of_height_zero_left ?_
        show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
        rfl
      · have hmem : ∀ r ∈ groupMemberRects (componentCandidate graph comp candidate) run uNode.decl,
          run.ys.getD w 0 + RouteImpl.nodeH run.proper w ≤ r.y := by
          intro r hr
          obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
          obtain ⟨l, hly, hqTop, hqBot⟩ := run_node_band hrun hq
          have hAllBelow : (rk run.coordinateProper.rank w).toNat <
              (rk run.coordinateProper.rank q).toNat := by
            refine Classical.byContradiction (fun hcontra => ?_)
            exact hLow ⟨q, nd, hq, hcon, by omega⟩
          have hband := CoordsImpl.rankAxis_bands_disjoint hry
            (rk run.coordinateProper.rank w).toNat (rk run.coordinateProper.rank q).toNat
            lW l hAllBelow hlyW hly
          simp only [RouteImpl.nodeH, hq] at hqBot
          simp only [RouteImpl.nodeH, hpropW] at hwBotBand
          rw [hrq, rectAt_eq]
          dsimp only
          simp only [RouteImpl.yAt, RouteImpl.nodeH, hpropW]
          omega
        have htop := boundsOf_minY_ge_of_all hmemNil hmem
        simp only [RouteImpl.nodeH, hpropW] at htop
        rw [frameRect_group_span hu hgroupU, hframeW, nodeRect_of_record hpropW]
        refine rect_disjoint_of_y (Or.inr ?_)
        omega
    · -- no member at all: the frame is flat
      have hmemNil : groupMemberRects (componentCandidate graph comp candidate) run uNode.decl = [] := by
        refine Classical.byContradiction (fun hne => ?_)
        cases hmem : groupMemberRects (componentCandidate graph comp candidate) run uNode.decl with
        | nil => exact hne hmem
        | cons r rest =>
          obtain ⟨q, nd, hq, hcon, _r⟩ :=
            groupMemberRects_inv (show r ∈ groupMemberRects (componentCandidate graph comp candidate) run uNode.decl by
              rw [hmem]; exact List.mem_cons_self)
          rcases (show (rk run.coordinateProper.rank q).toNat ≤
              (rk run.coordinateProper.rank w).toNat ∨
            (rk run.coordinateProper.rank w).toNat ≤
              (rk run.coordinateProper.rank q).toNat by omega) with hle | hle
          · exact hLow ⟨q, nd, hq, hcon, hle⟩
          · exact hHigh ⟨q, nd, hq, hcon, hle⟩
      rw [frameRect_group_span hu hgroupU, hmemNil]
      refine disjoint_of_height_zero_left ?_
      show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
      rfl

/-! ## The seam -/

/-- The non-group foreign-span seam: from the marker-existence, marker-ordering
and marker-alignment residuals, every non-group witness of an executed run
keeps its frame rectangle disjoint from an unrelated group's frame.  The
bottom-marker case and both rank-band cases of plain witnesses are proved
outright; only the inside-the-bracket plain case consumes the residuals. -/
theorem foreignNonGroupSpansClear
    (hbracket : BracketMarkersAtRank)
    (horder : PlainClearOfSideMarker)
    (halign : SideMarkerSpanAligned) :
    ForeignNonGroupSpansClear := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions
    hrun u w uNode wNode hu hw hgroupU hwNgroup hne hpathW hpathU
  obtain ⟨hborders, _path⟩ := componentCandidate_marker_shape hgraph hw
  rcases hborders with hwPlain | hgroupW | hwBottom
  · exact plain_frame_disjoint hgraph hcomp hrun hbracket horder halign hu hw hgroupU hwPlain hpathW
  · exact absurd hgroupW hwNgroup
  · exact bottomMarker_frame_disjoint hrun hw hwBottom u

end PipelineImpl

end Elegant.Layered

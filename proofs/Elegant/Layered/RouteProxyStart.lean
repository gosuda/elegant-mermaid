import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ParentContainmentFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.Coords
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.BottomClearanceExistence
import Elegant.Layered.BottomClearanceNesting
import Elegant.Layered.BottomClearanceBracket
import Elegant.Layered.CgShape
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.CoordGraph

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Elegant.Layered.PipelineImpl

private theorem foldl_bounds_minY_ge {rs : List Rect} {b : Bounds} {Y : Int}
    (hb : Y ≤ b.minY) (hall : ∀ r ∈ rs, Y ≤ r.y) :
    Y ≤ (rs.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
      max b.bottom (r.y + r.h)⟩) b).minY := by
  induction rs generalizing b with
  | nil => exact hb
  | cons r rs ih =>
    refine ih ?_ (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    dsimp only
    rw [Int.min_def]
    split
    · exact hb
    · exact hall r (List.mem_cons.mpr (Or.inl rfl))

private theorem boundsOf_minY_ge_of_mem {rects : List Rect} {Y : Int}
    (hne : rects ≠ []) (hall : ∀ r ∈ rects, Y ≤ r.y) :
    Y ≤ (boundsOf rects []).minY := by
  cases rects with
  | nil => exact absurd rfl hne
  | cons r rs =>
    have hstart : Y ≤ (⟨r.x, r.y, 0, 0⟩ : Bounds).minY := by
      simpa using hall r (List.mem_cons.mpr (Or.inl rfl))
    have hfold := foldl_bounds_minY_ge (rs := r :: rs)
      (b := (⟨r.x, r.y, 0, 0⟩ : Bounds)) hstart hall
    unfold boundsOf
    dsimp only
    simpa using hfold

/-- The top of a group frame equals the routed `ys` of its top proxy, given that every
member's routed `ys` is at least the proxy's. -/
theorem frameRect_top_eq_of_members
    {P : Params} {cg : Graph} {run : Run} {i : Nat} {Y : Int}
    (hf : (cg.nodes.getD i default).border = -2)
    (hself : (run.proper.nodes.getD i default).node.clusterPath.contains
        (cg.nodes.getD i default).decl = true)
    (hlen : i < run.proper.nodes.length)
    (hys : run.ys.getD i 0 = Y)
    (hlow : ∀ q : ProperNode × Nat, q ∈ run.proper.nodes.zipIdx →
      q.1.node.clusterPath.contains (cg.nodes.getD i default).decl = true →
        Y ≤ run.ys.getD q.2 0) :
    (frameRect P cg run i).y = Y := by
  have hget : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  have hq0 : (run.proper.nodes.getD i default, i) ∈ run.proper.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hget
  have hmem : Labels.rectAt run.proper run.xs run.ys i ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD i default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    apply List.mem_filterMap.mpr
    refine ⟨(run.proper.nodes.getD i default, i), hq0, ?_⟩
    rw [hself]
    simp
  have hrectY : (Labels.rectAt run.proper run.xs run.ys i).y = Y := by
    show RouteImpl.yAt run.ys i = Y
    exact hys
  have hall : ∀ r ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD i default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none), Y ≤ r.y := by
    intro r hr
    obtain ⟨q, hq, hrfl⟩ := List.mem_filterMap.mp hr
    by_cases hcontains : q.1.node.clusterPath.contains (cg.nodes.getD i default).decl = true
    · rw [hcontains] at hrfl
      rw [← Option.some.inj hrfl]
      show Y ≤ RouteImpl.yAt run.ys q.2
      exact hlow q hq hcontains
    · have hfalse : q.1.node.clusterPath.contains (cg.nodes.getD i default).decl = false := by
        simpa using hcontains
      rw [hfalse] at hrfl
      exact absurd hrfl (by simp)
  have hne : (run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains (cg.nodes.getD i default).decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none) ≠ [] := by
    intro hempty
    rw [hempty] at hmem
    simp at hmem
  have hle := boundsOf_minY_le_rect_y _ [] _ hmem
  have hge := boundsOf_minY_ge_of_mem hne hall
  simp only [frameRect, hf, show ((-2 : Int) != -2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  omega

/-- Port positions of a group top proxy lie within the group frame's horizontal range:
the proxy span comes from rank-matched side borders, and every such border also belongs
to the frame's wider horizontal hull. -/
theorem componentRun_group_frame_x_contains_port
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat}
    (hnode : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
    (hborder : (run.coordinateProper.nodes.getD v default).node.border = -2)
    (hcborder : (cg.nodes.getD v default).border = -2)
    (howner : (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl)
    (px : Int)
    (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    (frameRect P cg run v).x ≤ px ∧
      px ≤ (frameRect P cg run v).x + (frameRect P cg run v).w := by
  obtain ⟨owner, span, ownerEq, hspan, _, _, hleft, hright⟩ :=
    componentRun_proxy_interval hrun hnode (Or.inl hborder)
  have hownerEq : owner = (cg.nodes.getD v default).decl :=
    Option.some.inj (ownerEq.symm.trans howner)
  obtain ⟨li, ri, left, right, hleftGet, hrightGet, hleftBorder, hrightBorder,
    hleftOwner, hrightOwner, _, _, hlo, hhi⟩ := proxySpan_endpoint_sources hspan
  have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
    rcases hleftBorder with h | h <;> omega
  have hrightNotProxy : ¬(right.node.border = -2 ∨ right.node.border = 2) := by
    rcases hrightBorder with h | h <;> omega
  obtain ⟨hleftProper, hleftXs⟩ := componentRun_nonproxy_record hrun hleftGet hleftNotProxy
  obtain ⟨hrightProper, hrightXs⟩ := componentRun_nonproxy_record hrun hrightGet hrightNotProxy
  have hleftOwner' : left.node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl := by rw [hleftOwner, hownerEq]
  have hrightOwner' : right.node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl := by rw [hrightOwner, hownerEq]
  have hleftRect : Labels.rectAt run.proper run.xs run.ys li ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some (cg.nodes.getD v default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    apply List.mem_filterMap.mpr
    refine ⟨(left, li), List.mem_zipIdx_iff_getElem?.mpr hleftProper, ?_⟩
    rcases hleftBorder with h | h
    · simp [h, hleftOwner']
    · simp [h, hleftOwner']
  have hrightRect : Labels.rectAt run.proper run.xs run.ys ri ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some (cg.nodes.getD v default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    apply List.mem_filterMap.mpr
    refine ⟨(right, ri), List.mem_zipIdx_iff_getElem?.mpr hrightProper, ?_⟩
    rcases hrightBorder with h | h
    · simp [h, hrightOwner']
    · simp [h, hrightOwner']
  have hleftLo : (Labels.rectAt run.proper run.xs run.ys li).x = span.lo := by
    have hw : RouteImpl.nodeW run.proper li = left.node.w := by
      simp only [RouteImpl.nodeW, hleftProper]
    show run.xs.getD li 0 - Int.fdiv (RouteImpl.nodeW run.proper li) 2 = span.lo
    rw [hleftXs, hlo, hw]
  have hrightHi : (Labels.rectAt run.proper run.xs run.ys ri).x +
      (Labels.rectAt run.proper run.xs run.ys ri).w = span.hi := by
    have hw : RouteImpl.nodeW run.proper ri = right.node.w := by
      simp only [RouteImpl.nodeW, hrightProper]
    show run.xs.getD ri 0 - Int.fdiv (RouteImpl.nodeW run.proper ri) 2 +
      RouteImpl.nodeW run.proper ri = span.hi
    rw [hrightXs, hhi, hw]
  have hminX := boundsOf_minX_le_rect_x _ [] _ hleftRect
  have hrightBound := rect_right_le_boundsOf_right _ [] _ hrightRect
  have hboxX : (RouteImpl.boxRect run.proper run.xs run.ys v).x = span.lo := by
    show RouteImpl.leftOf run.proper run.xs v = span.lo
    exact hleft
  have hboxW : (RouteImpl.boxRect run.proper run.xs run.ys v).x +
      (RouteImpl.boxRect run.proper run.xs run.ys v).w = span.hi := by
    show RouteImpl.leftOf run.proper run.xs v +
      RouteImpl.nodeW run.proper v = span.hi
    exact hright
  simp only [frameRect, hcborder, show ((-2 : Int) != -2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  constructor <;> omega

/-- The routed port point of a group top proxy lies on the group frame boundary:
its vertical coordinate is the frame top and its horizontal coordinate stays inside
the frame's horizontal range. -/
theorem componentRun_group_frame_boundary
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat}
    (hnode : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
    (hborder : (run.coordinateProper.nodes.getD v default).node.border = -2)
    (hcborder : (cg.nodes.getD v default).border = -2)
    (howner : (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
      some (cg.nodes.getD v default).decl)
    (hcontains : (run.proper.nodes.getD v default).node.clusterPath.contains
      (cg.nodes.getD v default).decl = true)
    (hv : v < run.proper.nodes.length)
    (hlow : ∀ q : ProperNode × Nat, q ∈ run.proper.nodes.zipIdx →
      q.1.node.clusterPath.contains (cg.nodes.getD v default).decl = true →
        run.ys.getD v 0 ≤ run.ys.getD q.2 0)
    (px : Int)
    (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    Validator.onBoundary ⟨px, run.ys.getD v 0⟩ (frameRect P cg run v) := by
  have hx := componentRun_group_frame_x_contains_port hrun hnode hborder hcborder howner px hpx
  have hy := frameRect_top_eq_of_members (P := P) (i := v) (Y := run.ys.getD v 0)
    hcborder hcontains hv rfl hlow
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _, hroute, _⟩ := componentRun_spec hrun
  have hdims := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.1
  have hshape : ProperDimsNonneg run.proper := by
    intro i nd hget
    have hi : i < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hget).1
    have hw := hdims i hi
    have hnd : RouteImpl.nodeW run.proper i = nd.node.w ∧
        RouteImpl.nodeH run.proper i = nd.node.h := by
      simp only [RouteImpl.nodeW, RouteImpl.nodeH, hget]
      trivial
    omega
  have hdim := frameRect_dims_nonneg P cg run v hshape hv
  simp only [Validator.onBoundary]
  rw [hy]
  refine ⟨hx.1, hx.2, ?_, ?_, Or.inr (Or.inr (Or.inl rfl))⟩
  · omega
  · omega

/-- The routed `ys` of a group top proxy equals its layer top `run.top[k]`,
where `k` is its rank.  Plumbing half of the C5 group-endpoint fact. -/
theorem componentRun_group_proxy_ys_eq_top
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : cg.nodes[v]? = some nd) (hborder : nd.border = -2)
    (hv : v < cg.nodes.length) :
    run.ys.getD v 0 = run.top.getD (rk run.proper.rank v).toNat 0 := by
  obtain ⟨rr, labeled, hrr, hcoord, hrankRec, hnodeRec, _⟩ :=
    componentRun_ranked_node_records hrun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hy, hproxyYs, _⟩ := componentRun_spec hrun
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _⟩ := componentRun_spec hrun
  have hnodes : run.proper.nodes = routed.nodes := by rw [← hdrop]; rfl
  obtain ⟨_, hrankPW, hproperLen, _, hrecPW, _⟩ := proxyWidths_rel hproxy
  have hlabeledNode : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ :=
    hnodeRec v nd hnode
  have hcoordNode : run.coordinateProper.nodes[v]? =
      some (clearF (titleF ⟨nd, false, none, false⟩)) := by
    rw [← hcoord]
    exact coordinateGraph_marker_record hlabeledNode (Or.inl hborder) rfl
  -- the coordinateProper node at v has border -2
  have hbCoord : (run.coordinateProper.nodes.getD v default).node.border = -2 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : run.coordinateProper.nodes[v]? with
    | none => simp [h] at hcoordNode
    | some n =>
      rw [h] at hcoordNode
      have heq : n = clearF (titleF ⟨nd, false, none, false⟩) := Option.some.inj hcoordNode
      have hb1 : (titleF ⟨nd, false, none, false⟩).node.border = -2 := by
        have t1 : (titleF ⟨nd, false, none, false⟩).node.border = nd.border :=
          (titleF_keys _).2.1
        rw [t1, hborder]
      have hb2 : (clearF (titleF ⟨nd, false, none, false⟩)).node.border =
          (titleF ⟨nd, false, none, false⟩).node.border :=
        (clearF_keys _).2.1
      rw [heq]
      show (clearF (titleF ⟨nd, false, none, false⟩)).node.border = -2
      rw [hb2, hb1]
  obtain ⟨nd', hnd'get, _, hnd'border, _⟩ :=
    hrecPW v _ hcoordNode
  have hvProper : v < run.proper.nodes.length := componentRun_original_nodes_covered hrun v hv
  have hproperLenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hproperLen]
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hyvv := (CoordsImpl.rankCoordsWith_spec hy).2.2.2.2.2.2
  have hvCy : v < run.coordinateYs.length := by
    have hcylen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
      rw [hyvv, List.length_map, List.length_range]
    rw [hcylen]
    exact hvC
  have hb2eq : ((run.coordinateProper.nodes.getD v default).node.border == -2) = true := by
    simpa only [beq_iff_eq] using hbCoord
  have hfinalrank : run.proper.rank = run.coordinateProper.rank := by
    have := congrArg Proper.rank hdrop
    rw [OrderImpl.dropSynthetic_rank] at this
    exact this.symm.trans hrankPW
  have hndG : run.coordinateProper.nodes[v]? =
      some (run.coordinateProper.nodes.getD v default) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvC]
  have hpy := proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
    (v := v) (nd := run.coordinateProper.nodes.getD v default) hndG hvCy
  rw [← hproxyYs, hpy]
  split
  · rw [hfinalrank]
  · rename_i hcond
    exact absurd hb2eq hcond

/-! ### Candidate-graph membership helpers (C5 `hlow`, rank half) -/

private theorem isEmpty_false_ne_nil' {α : Type} {l : List α} (h : l.isEmpty = false) :
    l ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp at h

private theorem findSome {l : List (Node × Nat)} {pred : Node × Nat → Bool}
    {entry : Node × Nat} (hmem : entry ∈ l) (hp : pred entry = true) :
    ∃ b : Node × Nat, l.find? pred = some b :=
  Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, hmem, hp⟩)

/-- In a prepared measured graph, two bottom markers (`border = 2`) with equal
declarations are the same zip entry: every such node is a `markExtras` image whose
record is determined by the group-box index. -/
private theorem markOne_border_ne_two {boxesD : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {nodes0 : List Node}
    (hplain : ∀ (i : Nat) (n : Node), nodes0[i]? = some n → n.border = 0)
    {entry : Node × Nat} (hentry : entry ∈ nodes0.zipIdx) :
    (markOne boxesD pad titles entry).border ≠ 2 := by
  have hsrc : entry.1.border = 0 := by
    have := hplain entry.2 entry.1 (List.mem_zipIdx_iff_getElem?.mp hentry)
    simpa using this
  unfold markOne
  split
  · simpa only [hsrc] using (show (0 : Int) ≠ 2 by decide)
  · split
    · exact (show (-2 : Int) ≠ 2 by decide)
    · simpa only [hsrc] using (show (0 : Int) ≠ 2 by decide)

private def extraBottom (boxesD : List ModelBox) (boxD : ModelBox × Nat) : Node :=
  { decl := boxD.2, w := 0, h := 0
    clusterPath := Compound.path boxesD boxD.1 ++ [boxD.2], border := 2 }

private theorem markExtras_eq_extraBottom (boxesD : List ModelBox) :
    markExtras boxesD =
      (boxesD.zipIdx.filter fun q => q.1.role == .group).map (extraBottom boxesD) := by
  rw [markExtras_eq_map]
  rfl

private theorem extraBottom_decl (boxesD : List ModelBox) (boxD : ModelBox × Nat) :
    (extraBottom boxesD boxD).decl = boxD.2 := rfl

private theorem extraBottom_inj {boxesD : List ModelBox} {q q' : ModelBox × Nat}
    (hq : q ∈ boxesD.zipIdx) (hq' : q' ∈ boxesD.zipIdx)
    (h : extraBottom boxesD q = extraBottom boxesD q') : q = q' := by
  have hdecl : q.2 = q'.2 := by
    have := congrArg Node.decl h
    simpa [extraBottom] using this
  have hget : boxesD[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  have hget' : boxesD[q'.2]? = some q'.1 := List.mem_zipIdx_iff_getElem?.mp hq'
  rw [hdecl] at hget
  exact Prod.ext (Option.some.inj (hget.symm.trans hget')) hdecl

private theorem extraBottom_inj_decl {boxesD : List ModelBox} {q q' : ModelBox × Nat}
    (hq : q ∈ boxesD.zipIdx) (hq' : q' ∈ boxesD.zipIdx)
    (h : q.2 = q'.2) : q = q' := by
  have hget : boxesD[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  have hget' : boxesD[q'.2]? = some q'.1 := List.mem_zipIdx_iff_getElem?.mp hq'
  rw [h] at hget
  exact Prod.ext (Option.some.inj (hget.symm.trans hget')) h

private theorem extraBottom_nodup {boxesD : List ModelBox} :
    (((boxesD.zipIdx.filter fun q => q.1.role == .group).map
      (extraBottom boxesD)).map (·.decl)).Nodup := by
  rw [← markExtras_eq_extraBottom]
  exact markExtras_decl_nodup boxesD

private theorem prepare_bottom_unique {boxesD : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {nodes0 : List Node} {edges0 : List Edge} {slot : Int}
    (hplain : ∀ (i : Nat) (n : Node), nodes0[i]? = some n → n.border = 0)
    {eF eG : Node × Nat}
    (hF : eF ∈ (Compound.prepare boxesD pad titles
        { nodes := nodes0, edges := edges0, slot := slot }).nodes.zipIdx)
    (hG : eG ∈ (Compound.prepare boxesD pad titles
        { nodes := nodes0, edges := edges0, slot := slot }).nodes.zipIdx)
    (hbF : eF.1.border = 2) (hbG : eG.1.border = 2) (hd : eF.1.decl = eG.1.decl) :
    eF = eG := by
  have hsplit : (Compound.prepare boxesD pad titles
      { nodes := nodes0, edges := edges0, slot := slot }).nodes =
      nodes0.zipIdx.map (markOne boxesD pad titles) ++ markExtras boxesD := by
    rw [show (Compound.prepare boxesD pad titles
        { nodes := nodes0, edges := edges0, slot := slot }).nodes =
        Compound.markNodes boxesD pad titles nodes0 from rfl, markNodes_eq]
  have himage : ∀ e : Node × Nat,
      e ∈ (Compound.prepare boxesD pad titles
        { nodes := nodes0, edges := edges0, slot := slot }).nodes.zipIdx →
      e.1.border = 2 →
      ∃ (q : ModelBox × Nat) (p : Nat),
        extraBottom boxesD q = e.1 ∧
        (boxesD.zipIdx.filter fun r => r.1.role == .group)[p]? = some q ∧
        e.2 = (nodes0.zipIdx.map (markOne boxesD pad titles)).length + p := by
    intro e he hbe
    have hmem : e.1 ∈ (Compound.prepare boxesD pad titles
        { nodes := nodes0, edges := edges0, slot := slot }).nodes :=
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)
    rw [hsplit] at hmem
    rcases List.mem_append.mp hmem with horig | hextra
    · obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp horig
      have hnot := markOne_border_ne_two (boxesD := boxesD) (pad := pad)
        (titles := titles) hplain hentry
      rw [heq] at hnot
      exact (hnot hbe).elim
    · rw [markExtras_eq_extraBottom] at hextra
      obtain ⟨q, hq, heq⟩ := List.mem_map.mp hextra
      have heget : (Compound.prepare boxesD pad titles
          { nodes := nodes0, edges := edges0, slot := slot }).nodes[e.2]? = some e.1 :=
        List.mem_zipIdx_iff_getElem?.mp he
      rw [hsplit] at heget
      have hge : (nodes0.zipIdx.map (markOne boxesD pad titles)).length ≤ e.2 := by
        by_cases hlt : e.2 < (nodes0.zipIdx.map (markOne boxesD pad titles)).length
        · exfalso
          rw [List.getElem?_append_left hlt] at heget
          obtain ⟨entry, hentry, heq'⟩ := List.mem_map.mp (List.mem_of_getElem? heget)
          have hnot := markOne_border_ne_two (boxesD := boxesD) (pad := pad)
            (titles := titles) hplain hentry
          rw [heq', ← heq] at hnot
          exact (hnot rfl).elim
        · omega
      have hright := List.getElem?_append_right
        (l₁ := nodes0.zipIdx.map (markOne boxesD pad titles)) (l₂ := markExtras boxesD) hge
      rw [hright] at heget
      have hextraGet : (markExtras boxesD)[e.2 - (nodes0.zipIdx.map
          (markOne boxesD pad titles)).length]? = some e.1 := by
        simpa using heget
      rw [markExtras_eq_extraBottom, List.getElem?_map, Option.map_eq_some_iff] at hextraGet
      obtain ⟨q', hq'get, hval⟩ := hextraGet
      have hqq' : q = q' := extraBottom_inj
        (List.mem_filter.mp hq).1
        (List.mem_filter.mp (List.mem_of_getElem? hq'get)).1
        (heq.trans hval.symm)
      exact ⟨q, e.2 - (nodes0.zipIdx.map (markOne boxesD pad titles)).length, heq,
        by rw [hqq']; exact hq'get, by omega⟩
  obtain ⟨qF, pF, hvalF, hgetF, hidxF⟩ := himage eF hF hbF
  obtain ⟨qG, pG, hvalG, hgetG, hidxG⟩ := himage eG hG hbG
  have hmemF : qF ∈ boxesD.zipIdx :=
    (List.mem_filter.mp (List.mem_of_getElem? hgetF)).1
  have hmemG : qG ∈ boxesD.zipIdx :=
    (List.mem_filter.mp (List.mem_of_getElem? hgetG)).1
  have hdeclF : qF.2 = eF.1.decl :=
    (extraBottom_decl boxesD qF).symm.trans (congrArg Node.decl hvalF)
  have hdeclG : qG.2 = eG.1.decl :=
    (extraBottom_decl boxesD qG).symm.trans (congrArg Node.decl hvalG)
  have hqq : qF = qG := extraBottom_inj_decl hmemF hmemG
    (hdeclF.trans (hd.trans hdeclG.symm))
  have hvalG' : extraBottom boxesD qF = eG.1 := by rw [hqq]; exact hvalG
  have hboundF : pF < (boxesD.zipIdx.filter fun r => r.1.role == .group).length :=
    (List.getElem?_eq_some_iff.mp hgetF).1
  have hdecF : (((boxesD.zipIdx.filter fun r => r.1.role == .group).map
      (extraBottom boxesD)).map (·.decl))[pF]? = some qF.2 := by
    rw [List.getElem?_map, List.getElem?_map, hgetF]
    simp [extraBottom]
  have hdecG : (((boxesD.zipIdx.filter fun r => r.1.role == .group).map
      (extraBottom boxesD)).map (·.decl))[pG]? = some qG.2 := by
    rw [List.getElem?_map, List.getElem?_map, hgetG]
    simp [extraBottom]
  have hboundFmap : pF < (((boxesD.zipIdx.filter fun r => r.1.role == .group).map
      (extraBottom boxesD)).map (·.decl)).length := by
    rw [List.length_map, List.length_map]; exact hboundF
  rw [← hqq] at hdecG
  have hpq : pF = pG :=
    (List.Nodup.getElem?_inj hboundFmap extraBottom_nodup).mp (hdecF.trans hdecG.symm)
  refine Prod.ext (hvalF.symm.trans hvalG') ?_
  rw [hidxF, hidxG, hpq]

/-- The bottom marker found by declaration is unique, so a qualifying zip entry
is exactly what `find?` returns. -/
private theorem find?_bottom_eq {graph : Graph} {d : Nat} {e : Node × Nat}
    (huniquq : ∀ f : Node × Nat, f ∈ graph.nodes.zipIdx → f.1.border = 2 →
      f.1.decl = d → f = e)
    (hd : e.1.decl = d)
    (he : e ∈ graph.nodes.zipIdx) (hb : e.1.border = 2) :
    graph.nodes.zipIdx.find? (fun x => x.1.border == 2 && x.1.decl == d) = some e := by
  obtain ⟨b, hbf⟩ :=
    findSome (pred := fun x : Node × Nat => x.1.border == 2 && x.1.decl == d) he
      (by simp [hb, hd])
  have hpred := Bool.and_eq_true_iff.mp
    (List.find?_some (p := fun x : Node × Nat => x.1.border == 2 && x.1.decl == d) hbf)
  rw [huniquq b (List.mem_of_find?_eq_some hbf) (by simpa using hpred.1)
    (by simpa using hpred.2)] at hbf
  exact hbf

/-- Measured-graph level wrapper for bottom-marker uniqueness. -/
private theorem measuredGraph_bottom_pair_unique {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (_hlines : lines.length = inp.boxes.length)
    {eA eB : Node × Nat} (hA : eA ∈ graph.nodes.zipIdx) (hB : eB ∈ graph.nodes.zipIdx)
    (hbA : eA.1.border = 2) (hbB : eB.1.border = 2) (hd : eA.1.decl = eB.1.decl) :
    eA = eB := by
  obtain ⟨nodes0, edges0, titles0, hprepared, _, hplain⟩ :=
    measuredGraph_prepared_source hgraph
  have hsubA : eA ∈ (Compound.prepare (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box)
        P.clusterPad titles0 { nodes := nodes0, edges := edges0, slot := P.slot }).nodes.zipIdx := by
    rw [hprepared] at hA
    exact hA
  have hsubB : eB ∈ (Compound.prepare (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box)
        P.clusterPad titles0 { nodes := nodes0, edges := edges0, slot := P.slot }).nodes.zipIdx := by
    rw [hprepared] at hB
    exact hB
  exact prepare_bottom_unique (fun i n hn => (hplain i n hn).2) hsubA hsubB hbA hbB hd

theorem componentRun_cg_bottom_find
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat}
    {j : Nat} {top : Node}
    (htop : (componentCandidate graph comp candidate).nodes[j]? = some top)
    (hgroup : top.border = -2) :
    ∃ bottom : Node × Nat,
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == top.decl) = some bottom := by
  obtain ⟨oIdx, hoIdx, hsource⟩ := componentCandidate_nonplain_source htop (by omega)
  have hoIn : oIdx ∈ comp := List.mem_of_getElem? hoIdx
  exact candidate_group_bottom_find hgraph hlines hcomp candidate
    (top := (top, oIdx)) (List.mem_zipIdx_iff_getElem?.mpr hsource) hoIn hgroup

/-- A candidate bottom marker belongs to a candidate group top with the same cluster
path: the paired `border = -2` marker of the source box sits in the same component,
connected through the compound constraint edges of its group. -/
theorem componentRun_cg_top_of_bottom
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat}
    {j : Nat} {bottom : Node}
    (hbot : (componentCandidate graph comp candidate).nodes[j]? = some bottom)
    (hborder : bottom.border = 2) :
    ∃ t : Node × Nat,
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == -2 && entry.1.clusterPath == bottom.clusterPath) = some t := by
  have hbd : ∀ e ∈ graph.edges ++ Compound.constraints graph,
      e.tail < graph.nodes.length ∧ e.head < graph.nodes.length := fun e he => by
    rcases List.mem_append.mp he with he | he
    · exact measuredGraph_edges_bounded hgraph hlines e he
    · exact constraints_bounded graph e he
  have hpathLen : ∀ n : Node, n ∈ graph.nodes → n.border = 2 →
      n.clusterPath.length ≤ inp.boxes.length + 1 := by
    intro n hn hb
    obtain ⟨boxD, hboxD, _, hnpath, _, _⟩ := measuredGraph_bottom_origin hgraph hn hb
    have hplen : (Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box) boxD).length ≤
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
            { box with role := .node } else box).length := by
      unfold Compound.path
      refine Nat.le_trans (ancestors_length_le _ _ _) ?_
      rw [List.length_map]
      exact Nat.le_refl _
    rw [hnpath, List.length_append, List.length_singleton]
    have hmaplen : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box).length = inp.boxes.length := by
      rw [List.length_map]
    omega
  obtain ⟨oIdx, hoIdx, hsource⟩ := componentCandidate_nonplain_source hbot (by omega)
  have hoIn : oIdx ∈ comp := List.mem_of_getElem? hoIdx
  obtain ⟨boxD, hboxD, hroleD, hbpathD, _, _⟩ :=
    measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hsource) hborder
  have hdbound : bottom.decl < lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hboxD).1
    rw [List.length_map] at hi
    omega
  obtain ⟨top0, bot0, htop0, hbotmem, htopborder, hbotborder, htopdecl, hbotdecl,
    htoppath, hbotpath, _, _⟩ := measuredGraph_paired_markers hgraph hdbound hboxD hroleD
  have hzipTop : (top0, top0.decl) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (by rw [htopdecl]; exact htop0)
  have hbotmemZip : (bottom, oIdx) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hsource
  have main : ∀ fuel : Nat, ∀ t e : Node × Nat,
      t ∈ graph.nodes.zipIdx → t.1.border = -2 → t.1.decl = e.1.decl →
      t.1.clusterPath = e.1.clusterPath → e ∈ graph.nodes.zipIdx → e.1.border = 2 →
      e.2 ∈ comp → inp.boxes.length + 2 - e.1.clusterPath.length = fuel →
      t.2 ∈ comp := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro t e htzip hgroup hdecl hpath hezip hbe hecomp hfuel
      have huniquqE : ∀ f : Node × Nat, f ∈ graph.nodes.zipIdx → f.1.border = 2 →
          f.1.decl = e.1.decl → f = e := fun f hf hfb hfd =>
        measuredGraph_bottom_pair_unique hgraph hlines hf hezip hfb hbe hfd
      have hfindE : graph.nodes.zipIdx.find? (fun x => x.1.border == 2 && x.1.decl == e.1.decl) =
          some e := find?_bottom_eq huniquqE rfl hezip hbe
      have hfindT : graph.nodes.zipIdx.find? (fun x => x.1.border == 2 && x.1.decl == t.1.decl) =
          some e := by
        simp only [hdecl]
        exact hfindE
      cases hmemCase : (graph.nodes.zipIdx.filter fun q =>
          q.1.border == 0 && q.1.clusterPath.contains t.1.decl).isEmpty with
      | false =>
        obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _
          (isEmpty_false_ne_nil' hmemCase)
        obtain ⟨hmZip, hmCond⟩ := List.mem_filter.mp hmember
        obtain ⟨hmPlain, hmInside⟩ := Bool.and_eq_true_iff.mp hmCond
        have hmPlain' : member.1.border = 0 := by simpa using hmPlain
        have hmInside' : member.1.clusterPath.contains t.1.decl = true := by
          simpa using hmInside
        obtain ⟨he₁, he₂⟩ := compound_member_constraint_edges (graph := graph)
          (top := t) (bottom := e) (member := member) htzip hgroup hfindT
          hmZip hmPlain' hmInside'
        obtain ⟨c, hcMem, hcT, hcH⟩ :=
          components_edge_endpoints hbd (List.mem_append_right _ he₂)
        have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcH hecomp
        rw [hcEq] at hcT
        obtain ⟨c', hcMem', hcT', hcH'⟩ :=
          components_edge_endpoints hbd (List.mem_append_right _ he₁)
        have hcEq' : c' = comp := components_shared_member_eq hcMem' hcomp hcH' hcT
        rw [hcEq'] at hcT'
        exact hcT'
      | true =>
        cases hchildCase : ((graph.nodes.zipIdx.filter fun q => q.1.border == -2).filter
            fun q => q.1.clusterPath.dropLast == t.1.clusterPath).isEmpty with
        | true =>
          have he₁ := compound_empty_group_constraint_edge (graph := graph)
            (top := t) (bottom := e) htzip hgroup hfindT hmemCase hchildCase
          obtain ⟨c, hcMem, hcT, hcH⟩ :=
            components_edge_endpoints hbd (List.mem_append_right _ he₁)
          have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcH hecomp
          rw [hcEq] at hcT
          exact hcT
        | false =>
          obtain ⟨child, hchildMem⟩ := List.exists_mem_of_ne_nil _
            (isEmpty_false_ne_nil' hchildCase)
          obtain ⟨hchildTops, hchildPathEq⟩ := List.mem_filter.mp hchildMem
          obtain ⟨hchildZip, hchildGroupB⟩ := List.mem_filter.mp hchildTops
          have hchildGroup : child.1.border = -2 := by simpa using hchildGroupB
          have hchildPath : child.1.clusterPath.dropLast = t.1.clusterPath := by
            simpa using hchildPathEq
          have hchildSource : graph.nodes[child.2]? = some child.1 :=
            List.mem_zipIdx_iff_getElem?.mp hchildZip
          obtain ⟨hdeclC, childBox, hchildBoxL, hchildRole, _⟩ :=
            measuredGraph_group_origin hgraph hchildSource hchildGroup
          have hchildDbound : child.1.decl < lines.length := by
            have hi := (List.getElem?_eq_some_iff.mp hchildBoxL).1
            rw [List.length_map] at hi
            omega
          obtain ⟨childTop, childBot, hchildTopL, hchildBotMem, hchildTopBorder,
            hchildBotBorder, hchildTopDecl, hchildBotDecl, hchildTopPath, hchildBotPath,
            _, _⟩ :=
            measuredGraph_paired_markers hgraph hchildDbound hchildBoxL hchildRole
          have hs : graph.nodes[child.1.decl]? = some child.1 := by
            rw [hdeclC]; exact hchildSource
          have h1 : graph.nodes[childTop.decl]? = some childTop := by
            rw [hchildTopDecl]; exact hchildTopL
          rw [hchildTopDecl] at h1
          have hchildTopEq : childTop = child.1 :=
            Option.some.inj (h1.symm.trans hs)
          obtain ⟨cbIdx, hcbIdx⟩ := List.mem_iff_getElem?.mp hchildBotMem
          have hcbZip : (childBot, cbIdx) ∈ graph.nodes.zipIdx :=
            List.mem_zipIdx_iff_getElem?.mpr hcbIdx
          obtain ⟨cb, hcbfind⟩ :=
            findSome (pred := fun x : Node × Nat =>
                x.1.border == 2 && x.1.decl == child.1.decl) hcbZip
              (by simp [hchildBotBorder, hchildBotDecl])
          have hcbPred : cb.1.border = 2 ∧ cb.1.decl = child.1.decl := by
            have := List.find?_some
              (p := fun x : Node × Nat => x.1.border == 2 && x.1.decl == child.1.decl)
              hcbfind
            simpa using this
          have hcbMemGet : graph.nodes[cb.2]? = some cb.1 :=
            List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hcbfind)
          have hcbMem : cb.1 ∈ graph.nodes := List.mem_of_getElem? hcbMemGet
          have hcbPathEq : cb.1.clusterPath = child.1.clusterPath := by
            have hiff := measuredGraph_bottom_path_iff_decl hgraph
              (List.mem_of_getElem? hcbMemGet) (List.mem_of_getElem? hcbIdx)
              hcbPred.1 hchildBotBorder
            have hdeq : cb.1.decl = childBot.decl := hcbPred.2.trans hchildBotDecl.symm
            rw [hiff.mpr hdeq, hchildBotPath, hchildTopEq]
          have hcbFuelEq : inp.boxes.length + 2 - cb.1.clusterPath.length = fuel - 1 := by
            have hlenChild : child.1.clusterPath.length =
                t.1.clusterPath.length + 1 := by
              have hd := congrArg List.length hchildPath
              rw [List.length_dropLast] at hd
              have htne := (measuredGraph_marker_shape hgraph
                (List.mem_zipIdx_iff_getElem?.mp htzip)).2 hgroup
              have htneLen : 0 < t.1.clusterPath.length :=
                List.length_pos_iff.mpr htne
              omega
            have hlenTE : t.1.clusterPath.length = e.1.clusterPath.length := by
              rw [hpath]
            have hlenCB : cb.1.clusterPath.length = child.1.clusterPath.length := by
              rw [hcbPathEq]
            have hboundCB : cb.1.clusterPath.length ≤ inp.boxes.length + 1 :=
              hpathLen cb.1 hcbMem hcbPred.1
            omega
          obtain ⟨he₁, he₂⟩ := compound_child_constraint_edges (graph := graph)
            (parent := t) (parentBottom := e) (child := child)
            (childBottom := cb) htzip hgroup hfindT
            hchildZip hchildGroup hchildPath hcbfind
          obtain ⟨c, hcMem, hcT, hcH⟩ :=
            components_edge_endpoints hbd (List.mem_append_right _ he₂)
          have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcH hecomp
          rw [hcEq] at hcT
          have hchildComp := ih (fuel - 1) (by
              have hbE : e.1.clusterPath.length ≤ inp.boxes.length + 1 :=
                hpathLen e.1 (List.mem_of_getElem?
                  (List.mem_zipIdx_iff_getElem?.mp hezip)) hbe
              omega) child cb
            hchildZip hchildGroup
            hcbPred.2.symm hcbPathEq.symm
            (List.mem_of_find?_eq_some hcbfind) hcbPred.1 hcT hcbFuelEq
          obtain ⟨c', hcMem', hcT', hcH'⟩ :=
            components_edge_endpoints hbd (List.mem_append_right _ he₁)
          have hcEq' : c' = comp :=
            components_shared_member_eq hcMem' hcomp hcH' hchildComp
          rw [hcEq'] at hcT'
          exact hcT'
  -- top0's component membership via the group of (bottom, oIdx)
  have hconnect := main (inp.boxes.length + 2 - bottom.clusterPath.length)
    (top0, top0.decl) (bottom, oIdx) hzipTop htopborder htopdecl
    (by rw [htoppath, hbpathD])
    hbotmemZip hborder hoIn rfl
  rw [componentCandidate_nodes]
  have hmem : top0 ∈ (componentGraph graph comp).nodes := by
    apply List.mem_map.mpr ⟨top0.decl, hconnect, ?_⟩
    rw [List.getD_eq_getElem?_getD, htopdecl, htop0]
    rfl
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_getElem?.mp hmem
  exact findSome
    (pred := fun entry : Node × Nat =>
      entry.1.border == -2 && entry.1.clusterPath == bottom.clusterPath)
    (entry := (top0, i₀))
    (List.mem_zipIdx_iff_getElem?.mpr hi₀)
    (by simp [htopborder, htoppath, hbpathD])

/-! ### Executed node band accounting (C5 `hlow`, ys half) -/

/-- Band tops are monotone in the band index. -/
private theorem top_band_le {rankGap slot : Int} {p : Proper} {layers : List (List Nat)}
    {slots y top : List Int}
    (hy : rankCoordsWith rankGap slot p layers slots = .ok (y, top))
    {r s : Nat} (hr : ∃ l : List Nat, layers[r]? = some l)
    (hs : ∃ l : List Nat, layers[s]? = some l) (hrs : r ≤ s) :
    top.getD r 0 ≤ top.getD s 0 := by
  obtain ⟨l, hl⟩ := hr
  obtain ⟨l', hl'⟩ := hs
  rcases Nat.eq_or_lt_of_le hrs with heq | hlt
  · rw [heq]
    exact Int.le_refl _
  · have hband := rankAxis_bands_disjoint hy r s l l' hlt hl hl'
    have hnonneg : 0 ≤ CoordsImpl.layerHeight p l := RouteImpl.layerHeight_nonneg p l
    omega

/-- Band comparison directly on the executed rank indices. -/
private theorem coverage_band {rankGap slot : Int} {p : Proper}
    {layers : List (List Nat)} {slots y top : List Int}
    (hy : rankCoordsWith rankGap slot p layers slots = .ok (y, top))
    (hcov : ∀ v : Nat, v < p.nodes.length →
      ∃ l : List Nat, layers[(rk p.rank v).toNat]? = some l ∧ v ∈ l ∧ 0 ≤ rk p.rank v)
    {a b : Nat} (ha : a < p.nodes.length) (hb : b < p.nodes.length)
    (hab : (rk p.rank a).toNat ≤ (rk p.rank b).toNat) :
    top.getD (rk p.rank a).toNat 0 ≤ top.getD (rk p.rank b).toNat 0 := by
  obtain ⟨la, hla, _, _⟩ := hcov a ha
  obtain ⟨lb, hlb, _, _⟩ := hcov b hb
  exact top_band_le hy ⟨_, hla⟩ ⟨_, hlb⟩ hab

/-- Executed ranks agree with coordinate ranks. -/
private theorem componentRun_rank_eq
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) (x : Nat) :
    rk run.proper.rank x = rk run.coordinateProper.rank x := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproj, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  have hdropRank : run.proper.rank = q0.rank := by
    rw [← hdrop]
    exact OrderImpl.dropSynthetic_rank q0
  rw [hdropRank, (proxyWidths_rel hproj).2.1]

/-- An executed node's border is the border of its coordinate node. -/
private theorem componentRun_executed_border
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < run.proper.nodes.length) :
    (run.coordinateProper.nodes.getD i default).node.border =
      (run.proper.nodes.getD i default).node.border := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproj, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  have hrel := proxyWidths_rel hproj
  have hlen : run.coordinateProper.nodes.length = run.proper.nodes.length := by
    rw [← hrel.2.2.1, ← hdrop, OrderImpl.dropSynthetic_nodes]
  have hcget : run.coordinateProper.nodes[i]? =
      some (run.coordinateProper.nodes.getD i default) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by omega : i < run.coordinateProper.nodes.length)]
  obtain ⟨nd', hnd', _, hbd, _⟩ := hrel.2.2.2.2.1 i _ hcget
  have hndCoord : run.proper.nodes.getD i default = nd' := by
    have hA := (List.getElem?_eq_some_iff.mp
      (show run.proper.nodes[i]? = some nd' from by
        rw [← hdrop, OrderImpl.dropSynthetic_nodes]; exact hnd')).2
    have hB : run.proper.nodes.getD i default = run.proper.nodes[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hB, hA]
  rw [hndCoord]
  exact hbd.symm

/-- Every executed node is routed at or above the band top of a group top proxy's
band, as soon as its executed rank is at least the proxy's executed rank. -/
theorem componentRun_executed_ys_ge_top_band
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hv : cg.nodes[v]? = some nd) (hborder : nd.border = -2)
    (hvcg : v < cg.nodes.length)
    {i : Nat} (hi : i < run.proper.nodes.length)
    (hrk : rk run.proper.rank v ≤ rk run.proper.rank i) :
    run.ys.getD v 0 ≤ run.ys.getD i 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproj, hdrop, hrouting, _, hy, hys, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, _, hlayermem, hcov, _⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouting).1
  have hrel := proxyWidths_rel hproj
  have hlenCoord : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes, hrel.2.2.1]
  have hvc : v < run.proper.nodes.length := componentRun_original_nodes_covered hrun v hvcg
  have hic : i < run.coordinateProper.nodes.length := by omega
  have hcylen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    have hspec := (CoordsImpl.rankCoordsWith_spec hy).2.2.2.2.2.2
    rw [hspec, List.length_map, List.length_range]
  have hicYs : i < run.coordinateYs.length := by omega
  have hrkCoord := componentRun_rank_eq hrun v
  have hrkCoordI := componentRun_rank_eq hrun i
  have hyv0 := componentRun_group_proxy_ys_eq_top hrun hv hborder hvcg
  rw [hrkCoord] at hyv0
  have hvcov := hcov v hvc
  rw [hrkCoord] at hvcov
  have hicov := hcov i hi
  rw [hrkCoordI] at hicov
  have hrkLe : rk run.coordinateProper.rank v ≤ rk run.coordinateProper.rank i := by
    rw [← hrkCoord, ← hrkCoordI]
    exact hrk
  obtain ⟨lv, hlv, _, _⟩ := hvcov
  obtain ⟨li_, hli, hin, hri0⟩ := hicov
  have hbandTop := top_band_le hy ⟨_, hlv⟩ ⟨_, hli⟩
    (show (rk run.coordinateProper.rank v).toNat ≤ (rk run.coordinateProper.rank i).toNat
      from by omega)
  have hcoordget : run.coordinateProper.nodes[i]? =
      some (run.coordinateProper.nodes.getD i default) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hic]
  obtain ⟨ndi, hndi, _, hbdi, _⟩ := hrel.2.2.2.2.1 i _ hcoordget
  have hysi := proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
    (v := i) (nd := run.coordinateProper.nodes.getD i default) hcoordget hicYs
  rw [hys, ← hbdi] at hysi
  have hinband : run.top.getD (rk run.coordinateProper.rank i).toNat 0 ≤
      run.coordinateYs.getD i 0 := by
    have hrkIeq : rk run.coordinateProper.rank i = ((rk run.coordinateProper.rank i).toNat : Int) :=
      (Int.toNat_of_nonneg hri0).symm
    exact (rankAxis_node_in_band hy hli hin hic hrkIeq).1
  split at hysi
  · rw [hyv0, hysi]
    exact hbandTop
  · split at hysi
    · have hLH : 0 ≤ CoordsImpl.layerHeight run.coordinateProper
        (run.layers.getD (rk run.coordinateProper.rank i).toNat []) :=
        RouteImpl.layerHeight_nonneg run.coordinateProper _
      rw [hyv0, hysi]
      omega
    · rw [hyv0, hysi]
      omega

end Elegant.Layered.PipelineImpl

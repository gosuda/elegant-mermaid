import Elegant.Layered.RegionC5Boundary
import Elegant.Layered.GroupBottomBoundaryProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem c5SideMarkerInHull {cg : Graph} {run : Run} {t i : Nat}
    {node : ProperNode} (hn : run.proper.nodes[i]? = some node)
    (hb : node.node.border = -1 ∨ node.node.border = 1)
    (hp : node.node.clusterPath.getLast? = some (cg.nodes.getD t default).decl) :
    Labels.rectAt run.proper run.xs run.ys i ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some (cg.nodes.getD t default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
  apply List.mem_filterMap.mpr
  refine ⟨(node, i), List.mem_zipIdx_iff_getElem?.mpr hn, ?_⟩
  rcases hb with hb | hb <;> simp [hb, hp]

theorem regionGroupProxyPortX {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {v t : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2)
    (htop : (cg'.nodes.getD t default).border = -2)
    (howner : node.node.clusterPath.getLast? = some (cg'.nodes.getD t default).decl)
    {px : Int}
    (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    (frameRect P cg' run t).x ≤ px ∧
      px ≤ (frameRect P cg' run t).x + (frameRect P cg' run t).w := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, q0, _, _, hs⟩ := componentRunR_stages hrun
  have hplaced : placed.nodes[v]? = some node := by simpa only [hs.hCoordProper] using hnode
  have hfinal : run.proper.nodes = q0.nodes := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes]
  obtain ⟨owner, span, ho, hspan, _, _, hlo, hhi⟩ := proxyWidths_proxy_interval hs.hProxy hplaced hborder
  have hoEq := Option.some.inj (ho.symm.trans howner)
  obtain ⟨l, r, lo, hi, hl, hr, hbl, hbr, hol, hor, _, _, hxl, hxr⟩ :=
    proxySpan_endpoint_sources hspan
  have hside {i : Nat} {n : ProperNode} (hn : placed.nodes[i]? = some n)
      (hb : n.node.border = -1 ∨ n.node.border = 1) :
      run.proper.nodes[i]? = some n ∧ run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
    have hnot : ¬ (n.node.border = -2 ∨ n.node.border = 2) := by
      rcases hb with h | h <;> omega
    obtain ⟨hout, hx⟩ := (proxyWidths_rel hs.hProxy).2.2.2.2.2 i n hn hnot
    refine ⟨by simpa only [hfinal] using hout, ?_⟩
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
  obtain ⟨hl', hlx⟩ := hside hl hbl
  obtain ⟨hr', hrx⟩ := hside hr hbr
  have hleft := c5SideMarkerInHull (cg := cg') (t := t) hl' hbl (hol.trans (congrArg some hoEq))
  have hright := c5SideMarkerInHull (cg := cg') (t := t) hr' hbr (hor.trans (congrArg some hoEq))
  have hmin := boundsOf_minX_le_rect_x _ [] _ hleft
  have hmax := rect_right_le_boundsOf_right _ [] _ hright
  have hleftX : (Labels.rectAt run.proper run.xs run.ys l).x = span.lo := by
    rw [rectAt_eq_box]
    simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hl', hlx, hxl]
  have hrightX : (Labels.rectAt run.proper run.xs run.ys r).x +
      (Labels.rectAt run.proper run.xs run.ys r).w = span.hi := by
    rw [rectAt_eq_box]
    simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hr', hrx, hxr]
  rw [hleftX] at hmin
  rw [hrightX] at hmax
  change RouteImpl.leftOf run.proper run.xs v ≤ px ∧
    px ≤ RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v at hpx
  have hpLo : RouteImpl.leftOf run.proper run.xs v = span.lo := by
    simpa only [RouteImpl.leftOf, RouteImpl.nodeW, hfinal] using hlo
  have hpHi : RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v = span.hi := by
    simpa only [RouteImpl.leftOf, RouteImpl.nodeW, hfinal] using hhi
  simp only [frameRect, htop, show ((-2 : Int) != -2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  constructor <;> omega

theorem regionRunPortRectEndpointHeights {p : Proper} {ys : List Int} {v : Nat}
    {node : ProperNode} (hn : p.nodes[v]? = some node) (hd : node.dummy = false)
    (hb : node.node.border = -2 ∨ (node.node.border = 2 ∧ node.node.h = 0)) :
    RouteImpl.tailPortY p ys v = ys.getD v 0 ∧
      (RouteImpl.boxRect p [] ys v).y = ys.getD v 0 := by
  refine ⟨?_, rfl⟩
  rcases hb with htop | ⟨hbottom, hzero⟩
  · simp [RouteImpl.tailPortY, RouteImpl.frameKind, RouteImpl.yAt, hn, hd, htop]
  · simp [RouteImpl.tailPortY, RouteImpl.frameKind, RouteImpl.nodeH, RouteImpl.yAt,
      hn, hd, hbottom, hzero]

theorem regionGroupTopPortOfMemberY {P : Params} {cg : Graph} {run : Run} {top : Nat}
    {px : Int} (hb : (cg.nodes.getD top default).border = -2)
    (htop : top < run.proper.nodes.length)
    (hmember : (run.proper.nodes.getD top default).node.clusterPath.contains
      (cg.nodes.getD top default).decl = true)
    (hlower : ∀ q ∈ run.proper.nodes.zipIdx,
      q.1.node.clusterPath.contains (cg.nodes.getD top default).decl = true →
      run.ys.getD top 0 ≤ run.ys.getD q.2 0)
    (hdims : ProperDimsNonneg run.proper)
    (hx : (frameRect P cg run top).x ≤ px ∧
      px ≤ (frameRect P cg run top).x + (frameRect P cg run top).w) :
    Validator.onBoundary ⟨px, run.ys.getD top 0⟩ (frameRect P cg run top) := by
  have hy := frameRect_top_eq_of_members (P := P) hb hmember htop rfl hlower
  have hheight := (frameRect_dims_nonneg P cg run top hdims htop).2
  change _ ≤ px ∧ px ≤ _ ∧ _ ≤ run.ys.getD top 0 ∧ run.ys.getD top 0 ≤ _ ∧ _
  exact ⟨hx.1, hx.2, by omega, by omega, Or.inr (Or.inr (Or.inl hy.symm))⟩

theorem regionGroupBottomPortOfMemberY {P : Params} {cg : Graph} {run : Run}
    {top bottom : Nat} {nd : ProperNode} {px : Int}
    (hb : (cg.nodes.getD top default).border = -2)
    (htop : top < run.proper.nodes.length)
    (hbottom : run.proper.nodes[bottom]? = some nd)
    (hmember : nd.node.clusterPath.contains (cg.nodes.getD top default).decl = true)
    (hzero : nd.node.h = 0) (hyNonneg : 0 ≤ run.ys.getD bottom 0)
    (hupper : ∀ q ∈ run.proper.nodes.zipIdx,
      q.1.node.clusterPath.contains (cg.nodes.getD top default).decl = true →
      run.ys.getD q.2 0 + RouteImpl.nodeH run.proper q.2 ≤ run.ys.getD bottom 0)
    (hdims : ProperDimsNonneg run.proper)
    (hx : (frameRect P cg run top).x ≤ px ∧
      px ≤ (frameRect P cg run top).x + (frameRect P cg run top).w) :
    Validator.onBoundary ⟨px, run.ys.getD bottom 0⟩ (frameRect P cg run top) := by
  have hall : ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains (cg.nodes.getD top default).decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2) else none),
      r.y + r.h ≤ run.ys.getD bottom 0 := by
    intro r hr
    obtain ⟨q, hq, heq⟩ := List.mem_filterMap.mp hr
    by_cases hc : q.1.node.clusterPath.contains (cg.nodes.getD top default).decl = true
    · rw [ite_eq_left hc] at heq
      rw [← Option.some.inj heq, rectAt_eq_box]
      exact hupper q hq hc
    · rw [ite_eq_right hc] at heq
      cases heq
  have hmem : Labels.rectAt run.proper run.xs run.ys bottom ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD top default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2) else none) := by
    apply List.mem_filterMap.mpr
    have hpath : (cg.nodes.getD top default).decl ∈ nd.node.clusterPath :=
      List.contains_iff_mem.mp hmember
    have hcondition : (nd, bottom).1.node.clusterPath.contains
        (cg.nodes.getD top default).decl = true := by
      change nd.node.clusterPath.contains (cg.nodes.getD top default).decl = true
      exact List.contains_iff_mem.mpr hpath
    refine ⟨(nd, bottom), List.mem_zipIdx_iff_getElem?.mpr hbottom, ?_⟩
    rw [hcondition]
    simp
  have hY : (Labels.rectAt run.proper run.xs run.ys bottom).y +
      (Labels.rectAt run.proper run.xs run.ys bottom).h = run.ys.getD bottom 0 := by
    rw [rectAt_eq_box]
    simp only [RouteImpl.yAt, RouteImpl.nodeH, hbottom, hzero, Int.add_zero]
  have hy := frameRect_bottom_eq_of_members (P := P) hb hmem hY hyNonneg hall
  have hheight := (frameRect_dims_nonneg P cg run top hdims htop).2
  change _ ≤ px ∧ px ≤ _ ∧ _ ≤ run.ys.getD bottom 0 ∧ run.ys.getD bottom 0 ≤ _ ∧ _
  exact ⟨hx.1, hx.2, by omega, by omega, Or.inr (Or.inr (Or.inr hy.symm))⟩

theorem regionRunPortEndpointsR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {i : Nat} (hi : i < cg'.edges.length) {first last : Nat}
    (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last) :
    let tail := (RouteImpl.edgeAt run.proper first).tail
    let head := (RouteImpl.edgeAt run.proper last).head
    let tailRect := RouteImpl.boxRect run.proper run.xs run.ys tail
    let headRect := RouteImpl.boxRect run.proper run.xs run.ys head
    ∃ (rt : EdgeRoute) (px qx : Int),
      run.routes[i]? = some rt ∧
      tailRect.x ≤ px ∧ px ≤ tailRect.x + tailRect.w ∧
      headRect.x ≤ qx ∧ qx ≤ headRect.x + headRect.w ∧
      (if (cg'.edges.map (·.reversed)).getD i false then
        rt.points.head? = some ⟨qx, headRect.y⟩ ∧
        rt.points.getLast? = some ⟨px, RouteImpl.tailPortY run.proper run.ys tail⟩
      else
        rt.points.head? = some ⟨px, RouteImpl.tailPortY run.proper run.ys tail⟩ ∧
        rt.points.getLast? = some ⟨qx, headRect.y⟩) := by
  have hic : i < run.proper.chains.length := by
    rw [rcbProperChainsR hrun]
    exact hi
  obtain ⟨rt, hrt, horig, _⟩ := componentRunR_route_of_indexR hrun hic
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs⟩ := componentRunR_stages hrun
  have hmem : rt ∈ run.routes := List.mem_of_getElem? hrt
  have hfirst' : (RouteImpl.edgesOf run.proper rt.original).head? = some first := by
    simpa only [horig] using hfirst
  have hlast' : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last := by
    simpa only [horig] using hlast
  dsimp only
  rcases hs.hLanes with ⟨_, hl⟩ | ⟨_, hl⟩
  · obtain ⟨px, qx, _, _, hx1, hx2, hx3, hx4, hpoints⟩ :=
      route_endpoints_on_ports hl hs.hRoutes rt hmem first last hfirst' hlast'
    refine ⟨rt, px, qx, hrt, hx1, hx2, hx3, hx4, ?_⟩
    simpa only [horig, RouteImpl.tailPortY, RouteImpl.boxRect] using hpoints
  · obtain ⟨px, qx, _, _, hx1, hx2, hx3, hx4, hpoints⟩ :=
      rcbRouteWithLanesR_endpoints hl hs.hRoutes rt hmem first last hfirst' hlast'
    exact ⟨rt, px, qx, hrt, hx1, hx2, hx3, hx4, by simpa only [horig] using hpoints⟩

end Elegant.Layered.PipelineImpl

import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.LaneValidity

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem minimumNodeWidth_bounds (nodes : List ProperNode) (seed : Int) :
    let lo := nodes.foldl (fun w nd => min w nd.node.w) seed
    lo ≤ seed ∧ ∀ nd ∈ nodes, lo ≤ nd.node.w := by
  induction nodes generalizing seed with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨hle, hwidth⟩ := ih (min seed first.node.w)
    refine ⟨Int.le_trans hle (Int.min_le_left _ _), ?_⟩
    intro nd hnd
    rcases List.mem_cons.mp hnd with rfl | hnd
    · exact Int.le_trans hle (Int.min_le_right _ _)
    · exact hwidth nd hnd

private theorem sizeProperPorts_eq_self_of_lower_bound (P : Params) (p : Proper)
    (hport : P.portGap ≤ 0) (hwidth : ∀ nd ∈ p.nodes, P.portGap ≤ nd.node.w) :
    sizeProperPorts P p = p := by
  have hnodes : (sizeProperPorts P p).nodes = p.nodes := by
    apply List.ext_getElem?
    intro i
    cases hi : p.nodes[i]? with
    | none => simp [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx, hi]
    | some nd =>
      have hw := hwidth nd (List.mem_of_getElem? hi)
      have hmul (degree : Nat) : (((degree + 1 : Nat) : Int) * P.portGap) ≤ nd.node.w := by
        rw [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
        have hz := Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg degree) hport
        omega
      have hmax (degree : Nat) :
          max nd.node.w (((degree + 1 : Nat) : Int) * P.portGap) = nd.node.w :=
        Int.max_eq_left (hmul degree)
      simp only [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx, hi,
        Option.map_some, Nat.zero_add]
      split
      · rfl
      · simp only [hmax]
  exact congrArg (fun nodes => { p with nodes := nodes }) hnodes

/-- After applying the actual exact sizing, the remaining coordinate-graph
    transform has the usual title and border classification. The auxiliary
    port gap makes ordinary sizing an identity on the already-sized graph. -/
private theorem componentRunX_coordinate_source
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (sized : Proper) (params : Params),
      coordinateGraph params sized = run.coordinateProper ∧ NodeKeys cg sized := by
  obtain ⟨_, _, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ := componentRunX_spec hrun
  let sized := sizeProperPortsX P exact labeled
  let params : Params := { P with portGap := sized.nodes.foldl (fun w nd => min w nd.node.w) 0 }
  obtain ⟨hport, hwidth⟩ := minimumNodeWidth_bounds sized.nodes 0
  have hid : sizeProperPorts params sized = sized :=
    sizeProperPorts_eq_self_of_lower_bound params sized hport hwidth
  have hkeys : NodeKeys cg labeled := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  refine ⟨sized, params, ?_, ?_⟩
  · unfold coordinateGraph
    rw [hid]
    exact hc
  · intro v nd hv
    obtain ⟨orig, ho, hd, hb, hp⟩ := X_sizeProperPorts_node_origin P exact labeled hv
    rcases hkeys v orig ho with ⟨n, hn', hd', hb', hp'⟩ | ⟨hd', hb', hp'⟩
    · exact Or.inl ⟨n, hn', hd.trans hd', hb.trans hb', hp.trans hp'⟩
    · exact Or.inr ⟨hd.trans hd', hb.trans hb', hp.trans hp'⟩

private theorem componentRunX_bottom_source
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hv : RouteImpl.IsBottom run.proper v) :
    ∃ nd ∈ cg.nodes, nd.border = 2 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨sized, params, hcoord, hkeys⟩ := componentRunX_coordinate_source hrun
  obtain ⟨_, _, hlen, _, hnodes, _⟩ := proxyWidths_rel hproxy
  have hq0 : run.proper.nodes = q0.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  cases hlookup : run.proper.nodes[v]? with
  | none => exact absurd (Or.inr hv : RouteImpl.IsFrame run.proper v) (not_isFrame_of_none hlookup)
  | some actual =>
    have hactual := (isBottom_iff hlookup).mp hv
    have hvc : v < run.coordinateProper.nodes.length := by
      have hlt := (List.getElem?_eq_some_iff.mp hlookup).1
      rwa [hq0, hlen] at hlt
    obtain ⟨nd, hn⟩ : ∃ nd, run.coordinateProper.nodes[v]? = some nd :=
      ⟨_, List.getElem?_eq_getElem hvc⟩
    obtain ⟨dst, hd, _, hb, _⟩ := hnodes v nd hn
    have hd' : run.proper.nodes[v]? = some dst := by rwa [hq0]
    have he : dst = actual := Option.some.inj (hd'.symm.trans hlookup)
    have hb2 : nd.node.border = 2 := by rw [← hb, he]; exact hactual.2
    rw [← hcoord] at hn
    rcases coordinateGraph_lookup params sized hn with ⟨src, hs, _, hbs, _, _⟩ |
        ⟨_, hside⟩ | ⟨_, _, _, _, _, htitle, _⟩
    · rcases hkeys v src hs with ⟨original, ho, _, hbo, _⟩ | ⟨_, hzero, _⟩
      · exact ⟨original, List.mem_of_getElem? ho, hbo.symm.trans (hbs.symm.trans hb2)⟩
      · omega
    · rcases hside with he | he <;> omega
    · omega

/-- The reserved gap is the executed distance between bands after accounting
    for the router's slots. Outside the executing steps it remains at least
    the original rank gap. -/
def reservedRouteRankGap (P : Params) (run : Run) (k : Nat) : Int :=
  max (CoordsImpl.rankGapAt P.rankGap run.proper run.layers k)
    (run.top.getD (k + 1) 0 - run.top.getD k 0 -
      (run.layers.map (RouteImpl.layerHeight run.proper)).getD k 0 -
      P.slot * (run.routing.gaps.getD k default).slots)

theorem componentRunX_reserved_band_step
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {k : Nat} {layer : List Nat} (hlayer : run.layers[k]? = some layer)
    (hk : k + 1 < run.layers.length) :
    run.top.getD (k + 1) 0 = run.top.getD k 0 + RouteImpl.layerHeight run.proper layer +
      reservedRouteRankGap P run k + P.slot * (run.routing.gaps.getD k default).slots := by
  have hgen := hrun
  rw [componentRunX_eq_gen] at hgen
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrouting, _⟩ := componentRunX_spec hrun
  have hstep := componentRunGen_rank_step_lower
    (runHooksShift_exact P exactIds inp cg labels) hgen hk
  rw [hrouting] at hstep
  have hgap : reservedRouteRankGap P run k = run.top.getD (k + 1) 0 - run.top.getD k 0 -
      (run.layers.map (RouteImpl.layerHeight run.proper)).getD k 0 -
      P.slot * (run.routing.gaps.getD k default).slots := by
    unfold reservedRouteRankGap
    exact Int.max_eq_right (by omega)
  rw [hgap, RouteImpl.heights_getD hlayer]
  omega

/-- Bottom-row order obligation: no positive-height node occupies the
    inclusive bracket of two side markers of a bottom proxy on its row.
    This only concerns layer indices, marker ownership, and node heights. -/
def ExactBottomBracketVacant (run : Run) : Prop :=
  ∀ {layer : List Nat} {t left v right i j k owner : Nat} {proxy lnode rnode : ProperNode},
    layer ∈ run.layers → t ∈ layer → RouteImpl.IsBottom run.proper t →
    run.coordinateProper.nodes[t]? = some proxy → proxy.node.clusterPath.getLast? = some owner →
    layer[i]? = some left → layer[j]? = some v → layer[k]? = some right →
    run.coordinateProper.nodes[left]? = some lnode →
    run.coordinateProper.nodes[right]? = some rnode →
    (lnode.node.border = -1 ∨ lnode.node.border = 1) →
    (rnode.node.border = -1 ∨ rnode.node.border = 1) →
    lnode.node.clusterPath.getLast? = some owner → rnode.node.clusterPath.getLast? = some owner →
    i ≤ j → j ≤ k → RouteImpl.nodeH run.proper v = 0

set_option maxHeartbeats 1200000 in
/-- Coordinate facts for the actual reserved ranks. Only the bottom-row
    bracket exclusion is additional to parameter validity and source shape. -/
theorem componentRunX_reserved_coordFacts
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hP : P.Valid) (hshape : CgShape cg)
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    (hbottom : ExactBottomBracketVacant run) :
    RouteImpl.CoordFacts run.proper run.layers run.xs run.ys run.top run.routing
      (min P.nodeGap P.clusterPad) (reservedRouteRankGap P run) P.slot := by
  have hgen := hrun
  rw [componentRunX_eq_gen] at hgen
  obtain ⟨_, _, _, q0, cy, preTop, preYs, _, _, _, _, hcross, hproxy, hdrop,
    hroute, _, hry, hysp, hreserve, _, _, _⟩ := componentRunGen_spec hgen
  obtain ⟨sized, params, hcoord, hkeys⟩ := componentRunX_coordinate_source hrun
  obtain ⟨hng, hcp, _, _, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
  obtain ⟨_, hrank, hlen, _, hlookup, hsame⟩ := proxyWidths_rel hproxy
  obtain ⟨_, hsz, hmem, hcov, _⟩ := RouteImpl.layersOk_spec
    (RouteImpl.routeWithLanes_geometry hroute).1
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hlenRun : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hlen]
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank, hrank]
  have hnodeH (v : Nat) : RouteImpl.nodeH run.proper v = RouteImpl.nodeH run.coordinateProper v := by
    have he : RouteImpl.nodeH run.proper v = RouteImpl.nodeH q0 v := by
      simp only [RouteImpl.nodeH, hnodes]
    exact he.trans (nodeH_proxy hproxy v)
  have hheight (layer : List Nat) : RouteImpl.layerHeight run.proper layer =
      CoordsImpl.layerHeight run.coordinateProper layer := by
    have he : RouteImpl.layerHeight run.proper layer = RouteImpl.layerHeight q0 layer := by
      simp only [RouteImpl.layerHeight, RouteImpl.nodeH, hnodes]
    exact he.trans (layerHeight_proxy hproxy layer)
  have hsource (v : Nat) (hv : v < run.proper.nodes.length) :
      ∃ src dst, run.coordinateProper.nodes[v]? = some src ∧ run.proper.nodes[v]? = some dst ∧
        dst.dummy = src.dummy ∧ dst.node.border = src.node.border := by
    have hc : v < run.coordinateProper.nodes.length := by rwa [← hlenRun]
    obtain ⟨src, hs⟩ : ∃ nd, run.coordinateProper.nodes[v]? = some nd :=
      ⟨_, List.getElem?_eq_getElem hc⟩
    obtain ⟨dst, hd, hdummy, hborder, _⟩ := hlookup v src hs
    exact ⟨src, dst, hs, by rwa [hnodes], hdummy, hborder⟩
  have hsrcFlat {v : Nat} {nd : ProperNode} (hv : run.coordinateProper.nodes[v]? = some nd)
      (hb : nd.node.border = -2 ∨ nd.node.border = 2) : RouteImpl.nodeH run.proper v = 0 := by
    have hz := pc_frame_flat (P := params) (labeled := sized)
      (by rw [hcoord]; exact hv) hb
    rw [hnodeH v]
    simp only [RouteImpl.nodeH, hv, hz]
  have hflat (v : Nat) (hv : RouteImpl.IsFrame run.proper v) : RouteImpl.nodeH run.proper v = 0 := by
    cases hq : run.proper.nodes[v]? with
    | none => exact absurd hv (not_isFrame_of_none hq)
    | some _ =>
      obtain ⟨src, dst, hs, hd, _, hb⟩ := hsource v (List.getElem?_eq_some_iff.mp hq).1
      have hh := (isFrame_iff hd).mp hv
      rw [hb] at hh
      exact hsrcFlat hs hh.2
  have hnonproxy (v : Nat) (hv : v < run.proper.nodes.length)
      (hn : ¬ RouteImpl.IsFrame run.proper v) :
      ∃ nd, run.coordinateProper.nodes[v]? = some nd ∧ ¬ (nd.node.border = -2 ∨ nd.node.border = 2) := by
    obtain ⟨src, dst, hs, hd, hdummy, hborder⟩ := hsource v hv
    refine ⟨src, hs, ?_⟩
    intro hbad
    apply hn
    apply (isFrame_iff hd).mpr
    have hreal : src.dummy = false := by
      cases he : src.dummy with
      | false => rfl
      | true =>
        have hzero := pc_plain (P := params) hkeys (by rw [hcoord]; exact hs) he
        omega
    exact ⟨hdummy.trans hreal, by rwa [hborder]⟩
  have hrecord {v : Nat} {nd : ProperNode} (hv : run.coordinateProper.nodes[v]? = some nd)
      (hb : ¬ (nd.node.border = -2 ∨ nd.node.border = 2)) :
      run.proper.nodes[v]? = some nd ∧ run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
    obtain ⟨hn, hx⟩ := hsame v nd hv hb
    exact ⟨by rwa [hnodes], by simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]⟩
  have huniq (a b : Nat) (na nb : ProperNode)
      (ha : run.coordinateProper.nodes[a]? = some na) (hb : run.coordinateProper.nodes[b]? = some nb)
      (h3a : na.node.border = 3) (h3b : nb.node.border = 3)
      (hp : na.node.clusterPath = nb.node.clusterPath) : a = b :=
    pc_title_unique (P := params) hkeys hshape
      (by rw [hcoord]; exact ha) (by rw [hcoord]; exact hb) h3a h3b hp
  have hsep {layer : List Nat} {i j a b : Nat} {na nb : ProperNode}
      (hl : layer ∈ run.layers) (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
      (hna : run.coordinateProper.nodes[a]? = some na) (hnb : run.coordinateProper.nodes[b]? = some nb)
      (han : ¬ (na.node.border = -2 ∨ na.node.border = 2))
      (hbn : ¬ (nb.node.border = -2 ∨ nb.node.border = 2)) :
      RouteImpl.coordSep (min P.nodeGap P.clusterPad) run.proper a b ≤
        RouteImpl.xAt run.xs b - RouteImpl.xAt run.xs a := by
    have hs := CoordsImpl.cluster_all_pairs_separated hcross huniq layer hl i j a b na nb
      hij ha hb hna hnb (fun h => han (Or.inl h)) (fun h => han (Or.inr h))
      (fun h => hbn (Or.inl h)) (fun h => hbn (Or.inr h))
    obtain ⟨qa, xa⟩ := hrecord hna han
    obtain ⟨qb, xb⟩ := hrecord hnb hbn
    have hwa := CoordsImpl.nodeW_ge_width run.coordinateProper a
    have hwb := CoordsImpl.nodeW_ge_width run.coordinateProper b
    simp only [hna] at hwa
    simp only [hnb] at hwb
    simp only [RouteImpl.coordSep, RouteImpl.xAt, RouteImpl.nodeW, qa, qb, xa, xb]
    unfold CoordsImpl.coordSep at hs
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hs ⊢
    omega
  have hinterval {layer : List Nat} {i j a b : Nat} {na nb : ProperNode}
      (hl : layer ∈ run.layers) (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
      (hna : run.coordinateProper.nodes[a]? = some na) (hnb : run.coordinateProper.nodes[b]? = some nb)
      (han : ¬ (na.node.border = -2 ∨ na.node.border = 2))
      (hbn : ¬ (nb.node.border = -2 ∨ nb.node.border = 2)) :
      RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤
        RouteImpl.leftOf run.proper run.xs b := by
    have hs := hsep hl hij ha hb hna hnb han hbn
    simp only [RouteImpl.coordSep,
      Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hs
    simp only [RouteImpl.leftOf,
      Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)]
    omega
  have hrow {layer : List Nat} (hl : layer ∈ run.layers) {t v : Nat} (ht : t ∈ layer)
      (hv : v ∈ layer) (hf : RouteImpl.IsFrame run.proper t) (hpos : 0 < RouteImpl.nodeH run.proper v) :
      (RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
        RouteImpl.leftOf run.proper run.xs t ∨ RouteImpl.leftOf run.proper run.xs t ≤
        RouteImpl.leftOf run.proper run.xs v) ∧
      (RouteImpl.IsBottom run.proper t →
        RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t ≤
          RouteImpl.leftOf run.proper run.xs v ∨
        RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
          RouteImpl.leftOf run.proper run.xs t) := by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hl
    obtain ⟨htn, htk⟩ := hmem k layer hk t ht
    obtain ⟨hvn, _⟩ := hmem k layer hk v hv
    obtain ⟨proxy, tNode, hp, htNode, _, htb⟩ := hsource t htn
    obtain ⟨other, _, ho, _, _, _⟩ := hsource v hvn
    have hpb : proxy.node.border = -2 ∨ proxy.node.border = 2 := by
      have h := (isFrame_iff htNode).mp hf
      exact htb.symm ▸ h.2
    have hon : ¬ (other.node.border = -2 ∨ other.node.border = 2) := by
      intro hb
      have hz := hsrcFlat ho hb
      omega
    obtain ⟨owner, span, howner, hspan, _, _, hleft, hright⟩ :=
      proxyWidths_proxy_interval hproxy hp hpb
    obtain ⟨left, right, ln, rn, hlNode, hrNode, hlBorder, hrBorder, hlOwner, hrOwner,
      hlRank, hrRank, hlSpan, hrSpan⟩ := proxySpan_endpoint_sources hspan
    have hln : ¬ (ln.node.border = -2 ∨ ln.node.border = 2) := by
      rcases hlBorder with he | he <;> omega
    have hrn : ¬ (rn.node.border = -2 ∨ rn.node.border = 2) := by
      rcases hrBorder with he | he <;> omega
    obtain ⟨hlFinal, xl⟩ := hrecord hlNode hln
    obtain ⟨hrFinal, xr⟩ := hrecord hrNode hrn
    have hlEq : RouteImpl.leftOf run.proper run.xs t = RouteImpl.leftOf run.proper run.xs left := by
      have he : RouteImpl.leftOf run.proper run.xs t = span.lo := by
        simpa only [RouteImpl.leftOf, RouteImpl.nodeW, hnodes] using hleft
      rw [he, hlSpan]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hlFinal, xl]
    have hrEq : RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t =
        RouteImpl.leftOf run.proper run.xs right + RouteImpl.nodeW run.proper right := by
      have he : RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t = span.hi := by
        simpa only [RouteImpl.leftOf, RouteImpl.nodeW, hnodes] using hright
      rw [he, hrSpan]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hrFinal, xr]
    have sideMem {s : Nat} {nd : ProperNode} (hs : run.proper.nodes[s]? = some nd)
        (hr : rk run.coordinateProper.rank s = rk run.coordinateProper.rank t) : s ∈ layer := by
      obtain ⟨row, hrw, hm, _⟩ := hcov s (List.getElem?_eq_some_iff.mp hs).1
      rw [hranks, hr, ← hranks, htk] at hrw
      have he : row = layer := Option.some.inj (hrw.symm.trans hk)
      simpa only [he] using hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (sideMem hlFinal hlRank)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
    obtain ⟨r, hr⟩ := List.mem_iff_getElem?.mp (sideMem hrFinal hrRank)
    constructor
    · rcases Nat.lt_trichotomy j i with hji | hji | hij
      · left
        rw [hlEq]
        exact hinterval hl hji hj hi ho hlNode hon hln
      · have he : left = v := by
          rw [hji] at hj
          exact Option.some.inj (hi.symm.trans hj)
        right
        rw [hlEq, he]
        exact Int.le_refl _
      · have hs := hinterval hl hij hi hj hlNode ho hln hon
        have hw := (hsz left (List.getElem?_eq_some_iff.mp hlFinal).1).1
        exact Or.inr (by rw [hlEq]; omega)
    · intro hbot
      by_cases hji : j < i
      · right
        rw [hlEq]
        exact hinterval hl hji hj hi ho hlNode hon hln
      by_cases hrj : r < j
      · left
        rw [hrEq]
        exact hinterval hl hrj hr hj hrNode ho hrn hon
      have hz := hbottom hl ht hbot hp howner hi hj hr hlNode hrNode hlBorder hrBorder
        hlOwner hrOwner (by omega) (by omega)
      omega
  obtain ⟨_, _, _, _, _, _, htopShift, hyShift⟩ := (runHooksShift_exact P exactIds inp cg labels).shifts
    run.coordinateProper run.layers preYs preTop run.ys run.top hreserve
  obtain ⟨hcyLen, htopLen⟩ := CoordsImpl.rankCoordsWith_length hry
  have hyLen : preYs.length = cy.length := by rw [← hysp]; simp [proxyYs]
  obtain ⟨_, hrg, hslot, hhalf⟩ := hP
  have hgap (k : Nat) : CoordsImpl.rankGapAt P.rankGap run.proper run.layers k ≤
      reservedRouteRankGap P run k := Int.le_max_left _ _
  refine ⟨Int.le_min.mpr ⟨hng, hcp⟩,
    fun k => Int.le_trans (CoordsImpl.rankGapAt_nonneg (by omega) _ _ k) (hgap k),
    hslot, fun k => Int.le_trans (CoordsImpl.half_slot_le_rankGapAt hrg hhalf _ _ k) (hgap k),
    ?_, hflat, ?_, ?_, ?_, ?_, ?_⟩
  · intro layer hl i j a b hij ha hb hna hnb _
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hl
    obtain ⟨na, ha', han⟩ := hnonproxy a (hmem k layer hk a (List.mem_of_getElem? ha)).1 hna
    obtain ⟨nb, hb', hbn⟩ := hnonproxy b (hmem k layer hk b (List.mem_of_getElem? hb)).1 hnb
    exact hsep hl hij ha hb ha' hb' han hbn
  · intro k layer v hk hv htop
    obtain ⟨hvn, hrk⟩ := hmem k layer hk v hv
    obtain ⟨nd, final, hp, hfinal, _, hb⟩ := hsource v hvn
    have hbTop : nd.node.border = -2 := hb.symm.trans ((isTop_iff hfinal).mp htop).2
    have hrk' : rk run.coordinateProper.rank v = (k : Int) := hranks ▸ hrk
    have hidx : (run.coordinateProper.rank.getD v 0).toNat = k := by
      change (rk run.coordinateProper.rank v).toNat = k
      rw [hrk']
      rfl
    have hvcy : v < cy.length := by rwa [hcyLen, ← hlenRun]
    have hraw : preYs.getD v 0 = preTop.getD k 0 := by
      rw [← hysp, proxyYs_getD _ _ _ _ hp hvcy]
      simp [hbTop, hrk']
    have hys := hyShift v (by rwa [hyLen])
    rw [hidx, hraw] at hys
    have hkt : k < preTop.length := by rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hk).1
    change run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤ run.top.getD k 0
    rw [hys, hflat v (Or.inl htop), htopShift k hkt]
    omega
  · intro layer hl t v ht hv hf _ _ hpos
    exact (hrow hl ht hv (Or.inl hf) hpos).1
  · intro layer hl t v ht hv hf _ _ hpos
    exact (hrow hl ht hv (Or.inr hf) hpos).2 hf
  · intro k layer v hk hv hvn hrk
    have hvc : v < run.coordinateProper.nodes.length := by rwa [← hlenRun]
    have hrk' : rk run.coordinateProper.rank v = (k : Int) := hranks ▸ hrk
    have hband := (X_ReserveBands_holds exactIds hrun).1 k layer v hk hv hvc hrk'
    rw [hnodeH v, hheight layer]
    exact hband
  · intro k layer hk hnext
    exact componentRunX_reserved_band_step hrun hk hnext

theorem componentRunX_reserved_coordFacts_of_no_bottom
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hP : P.Valid) (hshape : CgShape cg)
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    (hnoBottom : ∀ nd ∈ cg.nodes, nd.border ≠ 2) :
    RouteImpl.CoordFacts run.proper run.layers run.xs run.ys run.top run.routing
      (min P.nodeGap P.clusterPad) (reservedRouteRankGap P run) P.slot := by
  apply componentRunX_reserved_coordFacts hP hshape hrun
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBottom
  obtain ⟨nd, hm, hb⟩ := componentRunX_bottom_source hrun hBottom
  exact (hnoBottom nd hm hb).elim

theorem SceneExecutionX.reservedRouteCoords
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    (hbottom : ExactBottomBracketVacant run) :
    RouteImpl.CoordFacts run.proper run.layers run.xs run.ys run.top run.routing
      (min execution.params.nodeGap execution.params.clusterPad)
      (reservedRouteRankGap execution.params run) execution.params.slot :=
  componentRunX_reserved_coordFacts (checkedParams_valid execution.checked)
    (componentCandidate_shape (components_nodup execution.graph comp hcomp)
      (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate)
    hrun hbottom

theorem SceneExecutionX.reservedRouteCoords_of_collapsed_groups
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    (hfixed : ∀ box ∈ inp.boxes, box.role = .group →
      inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true) :
    RouteImpl.CoordFacts run.proper run.layers run.xs run.ys run.top run.routing
      (min execution.params.nodeGap execution.params.clusterPad)
      (reservedRouteRankGap execution.params run) execution.params.slot := by
  apply componentRunX_reserved_coordFacts_of_no_bottom (checkedParams_valid execution.checked)
    (componentCandidate_shape (components_nodup execution.graph comp hcomp)
      (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate)
    hrun
  intro nd hm hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  obtain ⟨index, _, hsource⟩ := componentCandidate_nonplain_source hi (by omega)
  have hindex : index < execution.graph0.nodes.length := by
    rw [← exactGraph_length execution.graph_eq]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨original, hOriginal⟩ : ∃ node, execution.graph0.nodes[index]? = some node :=
    ⟨_, List.getElem?_eq_getElem hindex⟩
  obtain ⟨updated, hUpdated, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hOriginal
  have he : updated = nd := Option.some.inj (hUpdated.symm.trans hsource)
  rw [he] at hborder
  obtain ⟨effective, hEffective, hrole, _, _, _⟩ :=
    measuredGraph_bottom_origin execution.graph0_eq (List.mem_of_getElem? hOriginal)
      (hborder.symm.trans hb)
  rw [List.getElem?_map] at hEffective
  obtain ⟨box, hBox, hChange⟩ := Option.map_eq_some_iff.mp hEffective
  by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
  · have he : ({ box with role := .node } : ModelBox) = effective := by simpa [hf] using hChange
    rw [← he] at hrole
    cases hrole
  · have he : box = effective := by simpa [hf] using hChange
    exact hf (hfixed box (List.mem_of_getElem? hBox) (he ▸ hrole))

/-- The executed exact lane router misses an unrelated real proper node
    once bottom-row bracket exclusion has been established. -/
theorem componentRunX_route_avoids_real_of_bottom_bracket
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hP : P.Valid) (hshape : CgShape cg)
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    (hbottom : ExactBottomBracketVacant run)
    {rt : EdgeRoute} (hrt : rt ∈ run.routes) {start finish v : Nat}
    (hstart : (RouteImpl.edgesOf run.proper rt.original).head? = some start)
    (hfinish : (RouteImpl.edgesOf run.proper rt.original).getLast? = some finish)
    (hv : v < run.proper.nodes.length) (hreal : RouteImpl.IsReal run.proper v)
    (hfrom : v ≠ (RouteImpl.edgeAt run.proper start).tail)
    (hto : v ≠ (RouteImpl.edgeAt run.proper finish).head) :
    ¬ Polyline.hitsRect rt.points (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlanes, hrouting, hpoints⟩ := componentRunX_spec hrun
  have hcoords := componentRunX_reserved_coordFacts hP hshape hrun hbottom
  rw [← hrouting] at hcoords
  exact route_avoids_nodes (componentRunX_properShape hrun) hlanes hpoints hcoords
    rt hrt start finish hstart hfinish v hv hreal hfrom hto

end Elegant.Layered.PipelineImpl

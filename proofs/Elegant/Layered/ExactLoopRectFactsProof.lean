import Elegant.Layered.ExactLoopRectResidualsProof
import Elegant.Layered.ExactLoopRectProof
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.Coords
import Elegant.Layered.Route
import Elegant.Layered.ComponentRunGen

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl
open CoordsImpl

/-- Prefixed copy of the private `XBbs_nonproxy_record`
(`ExactBorderSpanRunFactsProof.lean`): exact proper nodes transfer unchanged
for non-proxy borders. Shape-free. -/
private theorem xlrf_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- Shape-free cluster separation for border-0 endpoints: a border-0 left
node cannot anchor a title, so the title-uniqueness hypothesis of
`cluster_all_pairs_separated` is discharged by contradiction. -/
private theorem xlrf_coordSep_zero {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {i j a b : Nat} {first second : ProperNode}
    (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hfirst : run.coordinateProper.nodes[a]? = some first)
    (hsecond : run.coordinateProper.nodes[b]? = some second)
    (hb0a : first.node.border = 0) (_hb0b : second.node.border = 0) :
    coordSep (min P.nodeGap P.clusterPad) run.coordinateProper a b ≤
      run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨hng, hcp, hr, hs, _⟩ := crossCoordsClusterWith_spec hcross
  have halfnonneg : ∀ v, 0 ≤ Int.fdiv (nodeW run.coordinateProper v) 2 := by
    intro v
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    exact Int.ediv_nonneg (nodeW_nonneg hs v) (by decide)
  have hna1 : first.node.border ≠ -2 := by omega
  have hna2 : first.node.border ≠ 2 := by omega
  have middle : ∀ k, k ≤ j → ∃ c, layer[k]? = some c := by
    intro k hkj
    have hj : j < layer.length := (List.getElem?_eq_some_iff.mp hb).1
    cases hc : layer[k]? with
    | none => have := List.getElem?_eq_none_iff.mp hc; omega
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := middle (i + 1) (by omega)
  have hcn : ∃ nc, run.coordinateProper.nodes[c]? = some nc := by
    cases he : run.coordinateProper.nodes[c]? with
    | none =>
      have := List.getElem?_eq_none_iff.mp he
      have hlt := layers_mem_lt hr hlayer hc
      omega
    | some nc => exact ⟨nc, rfl⟩
  obtain ⟨nc, hnc⟩ := hcn
  have hadj := cluster_balance_separated hcross layer hlayer i a c ha hc
  by_cases ht : ownTitleAnchor run.coordinateProper a c = true
  · obtain ⟨hatitle, _, _⟩ :=
      ownTitleAnchor_left_nonanchor hfirst hnc hna1 hna2 ht
    omega
  · have htf : ownTitleAnchor run.coordinateProper a c = false :=
      Bool.eq_false_iff.mpr ht
    have hg := clusterGap_ge_min (ng := P.nodeGap) (cp := P.clusterPad)
      run.coordinateProper a c htf
    unfold clusterSep coordSep at hadj
    unfold coordSep
    by_cases heq : i + 1 = j
    · have hcb : c = b := by
        rw [heq, hb] at hc
        exact Option.some.inj hc.symm
      subst hcb
      omega
    · have htail := cluster_zero_pairs_separated hcross layer hlayer (i + 1) j c b
        (by omega) hc hb
      have hw := halfnonneg c
      omega

/-- Narrow ordered intervals for border-0 endpoints over an arbitrary exact
run: shape-free via `xlrf_coordSep_zero`. Strictly narrower than
`XLrr_FixedSep` (both endpoints `= 0` instead of `≠ ±2`), true on all probes,
and sufficient for `XL_FixedDisjoint` whose witnesses are border-0. -/
private theorem xlrf_ordered_zero {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {i j a b : Nat} {first second : ProperNode}
    (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hfirst : run.coordinateProper.nodes[a]? = some first)
    (hsecond : run.coordinateProper.nodes[b]? = some second)
    (hb0a : first.node.border = 0) (hb0b : second.node.border = 0) :
    RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤
      RouteImpl.leftOf run.proper run.xs b := by
  have hsep := xlrf_coordSep_zero hrun hlayer hij ha hb hfirst hsecond hb0a hb0b
  obtain ⟨_, _, _, _, _, _, _, _, hcross0, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨hng, hcp, _, _, _⟩ := crossCoordsClusterWith_spec hcross0
  obtain ⟨hfinalFirst, hxa⟩ := xlrf_nonproxy_record hrun hfirst (by omega)
  obtain ⟨hfinalSecond, hxb⟩ := xlrf_nonproxy_record hrun hsecond (by omega)
  have hwa : RouteImpl.nodeW run.proper a =
      RouteImpl.nodeW run.coordinateProper a := by
    simp only [RouteImpl.nodeW, hfinalFirst, hfirst]
  have hwb : RouteImpl.nodeW run.proper b =
      RouteImpl.nodeW run.coordinateProper b := by
    simp only [RouteImpl.nodeW, hfinalSecond, hsecond]
  have hga : RouteImpl.nodeW run.coordinateProper a ≤
      nodeW run.coordinateProper a := nodeW_ge_width _ _
  have hgb : RouteImpl.nodeW run.coordinateProper b ≤
      nodeW run.coordinateProper b := nodeW_ge_width _ _
  have e : ∀ width : Int, Int.fdiv width 2 = width / 2 :=
    fun width => Int.fdiv_eq_ediv_of_nonneg width (by decide)
  unfold coordSep at hsep
  simp only [e] at hsep
  simp only [RouteImpl.leftOf, RouteImpl.xAt, hxa, hxb, hwa, hwb, e]
  omega

/-- Prefixed copy of `XLrr_original_plain_record`
(`ExactLoopRectResidualsProof.lean`): exact original plain nodes keep measured
widths as lower bounds. Shape-free. -/
private theorem xlrf_original_plain_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.node.border = 0 ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec h
  have hsource :=
    addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, _, hborder, hwidth, hheight⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper : run.proper.nodes[index]? = some actual :=
    (xlrf_nonproxy_record h hcoordinate (by omega)).1
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _⟩ := componentRunX_spec h
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Narrow ordered intervals for border-0 endpoints over an arbitrary exact
run: strictly narrower than `XLrr_FixedSep` (both endpoints `= 0`), true on
all probes, and sufficient for `XL_FixedDisjoint`. Proved shape-free. -/
theorem XLrr_fixedSep0_holds (exactIds : List String) :
    ∀ (P : Params) (inp : Input) (cg : Graph) (run : Run)
      (labels : List MeasuredLabel) (orderOptions : OrderOptions),
      componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run →
      ∀ (layer : List Nat) (i j a b : Nat) (first second : ProperNode),
        layer ∈ run.layers → i < j → layer[i]? = some a → layer[j]? = some b →
        run.coordinateProper.nodes[a]? = some first →
        run.coordinateProper.nodes[b]? = some second →
        first.node.border = 0 → second.node.border = 0 →
        RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤
          RouteImpl.leftOf run.proper run.xs b := by
  intro P inp cg run labels orderOptions hrun layer i j a b first second hlayer
    hij ha hb hfirst hsecond hb0a hb0b
  exact xlrf_ordered_zero hrun hlayer hij ha hb hfirst hsecond hb0a hb0b

theorem XL_fixedDisjoint_closed (exactIds : List String) :
    XL_FixedDisjoint exactIds := by
  intro P inp cg run labels orderOptions hrun u v nodeU nodeV hnodeU hnodeV
    hbU hbV hne
  have hcovered := componentRunX_original_nodes_covered hrun
  obtain ⟨actualU, hcoordU, hpropU, hbU0, _, _, _⟩ :=
    xlrf_original_plain_record hrun hnodeU hbU
  obtain ⟨actualV, hcoordV, hpropV, hbV0, _, _, _⟩ :=
    xlrf_original_plain_record hrun hnodeV hbV
  have hrunGen : componentRunGen P (sizeProperPortsX P (exactDecls exactIds inp))
      (reserveExactRanks cg (exactDecls exactIds inp) labels)
      (cg.nodes.zipIdx.filterMap fun q =>
        if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none)
      cg labels orderOptions = .ok run := by
    rw [← componentRunX_eq_gen]
    exact hrun
  have hshift := runHooksShift_exact P exactIds inp cg labels
  obtain ⟨hinBand, hdisjBands⟩ := hshift.bands hrunGen
  have hu' : u < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeU).1
  have hv' : v < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeV).1
  have huP : u < run.proper.nodes.length := hcovered u hu'
  have hvP : v < run.proper.nodes.length := hcovered v hv'
  have hgetU : cg.nodes.getD u default = nodeU := by
    rw [List.getD_eq_getElem?_getD, hnodeU]
    rfl
  have hgetV : cg.nodes.getD v default = nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hframeU : frameRect P cg run u = nodeRect cg run u := by
    unfold frameRect
    simp only []
    rw [hgetU, hbU]
    rfl
  have hframeV : frameRect P cg run v = nodeRect cg run v := by
    unfold frameRect
    simp only []
    rw [hgetV, hbV]
    rfl
  rw [hframeU, hframeV]
  have hrectU : nodeRect cg run u =
      ⟨run.xs.getD u 0 - Int.fdiv actualU.node.w 2, run.ys.getD u 0,
        actualU.node.w, actualU.node.h⟩ := by
    simp [nodeRect, hpropU]
  have hrectV : nodeRect cg run v =
      ⟨run.xs.getD v 0 - Int.fdiv actualV.node.w 2, run.ys.getD v 0,
        actualV.node.w, actualV.node.h⟩ := by
    simp [nodeRect, hpropV]
  obtain ⟨ranksG, p0G, labeledG, q0G, ypreG, tpreG, yspreG, hnG, hlG, hcoordG,
      hordG, hcrossG, hproxyG, hdropG, hrouteG, hr2G, hryG, hyspreG, hresG,
      hcyG, hroutesG, hexactG⟩ := componentRunGen_spec hrunGen
  obtain ⟨_, hrankG, hqlenG, _, _, _⟩ := proxyWidths_rel hproxyG
  have hnodes : run.proper.nodes = q0G.nodes := by rw [← hdropG]; rfl
  have hnodesLen : run.proper.nodes.length =
      run.coordinateProper.nodes.length := by rw [hnodes, hqlenG]
  have huC : u < run.coordinateProper.nodes.length := by omega
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdropG]; exact hrankG
  obtain ⟨ordG, hordOkG, hordLayersG⟩ := hordG
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hrouteG).1
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨lU, hlyU, huIn, hrkU⟩ := hcov u huP
  obtain ⟨lV, hlyV, hvIn, hrkV⟩ := hcov v hvP
  let rU : Nat := (rk run.proper.rank u).toNat
  let rV : Nat := (rk run.proper.rank v).toNat
  have hrkU' : rk run.proper.rank u = (rU : Int) := by
    have h := Int.toNat_of_nonneg hrkU
    exact h.symm
  have hrkV' : rk run.proper.rank v = (rV : Int) := by
    have h := Int.toNat_of_nonneg hrkV
    exact h.symm
  have hrkCoordU : rk run.coordinateProper.rank u = (rU : Int) := by
    rw [← hranks]; exact hrkU'
  have hrkCoordV : rk run.coordinateProper.rank v = (rV : Int) := by
    rw [← hranks]; exact hrkV'
  have hlyU' : run.layers[rU]? = some lU := hlyU
  have hlyV' : run.layers[rV]? = some lV := hlyV
  rcases Nat.lt_trichotomy rU rV with hlt | heq | hgt
  · have hbandU := hinBand rU lU u hlyU' huIn huC hrkCoordU
    have hbandV := hinBand rV lV v hlyV' hvIn hvC hrkCoordV
    have hbands := hdisjBands rU rV lU lV hlt hlyU' hlyV'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega
  · rw [heq] at hlyU'
    obtain hlVeq : lV = lU := Option.some.inj (hlyV'.symm.trans hlyU')
    rw [hlVeq] at hvIn
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp huIn
    obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hvIn
    have hnePV : pu ≠ pv := by
      intro heq'
      subst heq'
      exact hne (Option.some.inj (hpu.symm.trans hpv))
    have hlayerMem : lU ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyU'
      rw [← hmemEq]
      exact List.getElem_mem hmemLT
    rcases Nat.lt_or_gt_of_ne hnePV with hplt | hpgt
    · have hsep := xlrf_ordered_zero hrun hlayerMem hplt hpu hpv hcoordU
        hcoordV hbU0 hbV0
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
    · have hsep := xlrf_ordered_zero hrun hlayerMem hpgt hpv hpu hcoordV
        hcoordU hbV0 hbU0
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
  · have hbandU := hinBand rU lU u hlyU' huIn huC hrkCoordU
    have hbandV := hinBand rV lV v hlyV' hvIn hvC hrkCoordV
    have hbands := hdisjBands rV rU lV lU hgt hlyV' hlyU'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

/-- Closed corollary modulo current hypotheses. -/
theorem XL_topSamePart_closed (exactIds : List String)
    (hSplit : XLrr_TopSplit exactIds) :
    XL_TopSamePart exactIds :=
  XL_topSamePart_holds exactIds hSplit

end PipelineImpl
end Layered
end Elegant

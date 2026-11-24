import Elegant.Layered.ExactLoopEnvelopeLayerProof
import Elegant.Layered.ExactLoopRectFactsProof
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.CgShape

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-- Sides file: proves the two plain-owner same-rank cases. -/
private theorem XLEMS_trivial : True := trivial
/-- Pure x-gap: a footprint ending left of a box misses it. -/
private theorem XLEMS_rect_miss_right {fp rb : Rect}
    (h : fp.x + fp.w ≤ rb.x) : ¬ fp.meetsInterior rb := by
  unfold Rect.meetsInterior
  omega
/-- Pure x-gap, symmetric: a box ending left of the footprint misses it. -/
private theorem XLEMS_rect_miss_left {fp rb : Rect}
    (h : rb.x + rb.w ≤ fp.x) : ¬ fp.meetsInterior rb := by
  unfold Rect.meetsInterior
  omega
/-- Footprint width is nonnegative over an exact run, in both branches. -/
private theorem XLEMS_fp_width_nonneg {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (t : Nat) : 0 ≤ (if run.exact.contains t then Loops.exactExtent
      cg.slot (loopSizes cg.edges labels t cg.slot) else Loops.extent
      cg.slot (loopSizes cg.edges labels t cg.slot)) := by
  have hslot : 0 ≤ cg.slot := componentRunX_slot_nonneg hrun
  have hw : ∀ l ∈ loopSizes cg.edges labels t cg.slot, 0 ≤ l.width := by
    intro l hl
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hmax0 : ∀ (acc : Int), 0 ≤ acc → ∀ (ss : List LoopLabel),
      0 ≤ ss.foldl (fun w l => max w l.width) acc := by
    intro acc ha ss
    induction ss generalizing acc with
    | nil => exact ha
    | cons s rest ih =>
      simp only [List.foldl]
      exact ih _ (Int.le_trans ha (Int.le_max_left _ _))
  by_cases hex : run.exact.contains t = true
  · simp only [hex, ↓reduceIte]
    unfold Loops.exactExtent
    dsimp only
    split
    · exact hmax0 0 (Int.le_refl _) _
    · have hwide : 0 ≤ (loopSizes cg.edges labels t cg.slot).foldl
          (fun w l => max w l.width) 0 := hmax0 0 (Int.le_refl _) _
      have hnn : 0 ≤ cg.slot * (2 * (((loopSizes cg.edges labels t cg.slot).length : Int)) + 1) :=
        Int.mul_nonneg hslot (by omega)
      omega
  · have hcon : run.exact.contains t = false := Bool.eq_false_iff.mpr hex
    simp only [hcon, Bool.false_eq_true, ↓reduceIte]
    unfold Loops.extent
    have hterm : ∀ q ∈ (loopSizes cg.edges labels t cg.slot).zipIdx.map
        (fun q => cg.slot * ((q.2 : Int) + 2) + q.1.width), 0 ≤ q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      obtain ⟨_, hjlen, ha⟩ := List.mem_zipIdx hp
      have hmem : p.1 ∈ loopSizes cg.edges labels t cg.slot := by
        have h1 : p.2 < (loopSizes cg.edges labels t cg.slot).length := by omega
        have h2 : (loopSizes cg.edges labels t cg.slot)[p.2]? =
            some ((loopSizes cg.edges labels t cg.slot)[p.2]) :=
          List.getElem?_eq_getElem h1
        simp only [Nat.sub_zero] at ha
        rw [← ha] at h2
        exact List.mem_of_getElem? h2
      have hslot2 : 0 ≤ cg.slot * ((p.2 : Int) + 2) :=
        Int.mul_nonneg hslot (by omega)
      have hwp : 0 ≤ p.1.width := hw p.1 hmem
      omega
    have hfold : ∀ (acc : Int), 0 ≤ acc → ∀ (l : List Int),
        (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.foldl (· + ·) acc := by
      intro acc ha l hl
      induction l generalizing acc with
      | nil => exact ha
      | cons a rest ih =>
        simp only [List.foldl]
        exact ih _ (by have hha := hl a (List.mem_cons.mpr (Or.inl rfl)); omega)
          (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
    exact hfold 0 (Int.le_refl _) _ hterm
/-- Footprint origin from the owner frame equation (width part is definitional). -/
private theorem XLEMS_fp_of_frame {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {t : Nat}
    (hFr : frameRect default cg run t =
      RouteImpl.boxRect run.proper run.xs run.ys t) :
    (loopFootprintExt cg run labels t).x =
      (RouteImpl.boxRect run.proper run.xs run.ys t).x +
        (RouteImpl.boxRect run.proper run.xs run.ys t).w := by
  unfold loopFootprintExt
  simp only [hFr]
/-- Prefixed copy of `XLEML_nonproxy_record`: exact proper nodes transfer
for non-proxy borders. -/
private theorem XLEMS_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
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

/-- Prefixed copy of `XLEML_original_plain_record`: exact original plain
nodes keep their measured record through the coordinate phases. -/
private theorem XLEMS_original_plain_record {P : Params} {exact : List Nat}
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
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, _, hborder, hwidth, hheight⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := (XLEMS_nonproxy_record h hcoordinate (by rw [hborder]; decide)).1
  have hxs := (XLEMS_nonproxy_record h hcoordinate (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  exact hxs
/-- Narrower left residual: the left miss for `v` that is not an original
plain node. Covers synthetic markers/titles and non-zero borders; strictly
narrower than `XLEM_LeftMiss` (extra premise), true on every probe case
(all in-scope same-layer `v` there are original plain nodes, and every
footprint is disjoint). -/
def XLEM_LeftNonPlain (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (cg.nodes.getD e.tail default).border = 0 →
    (¬ ∃ nv, cg.nodes[v]? = some nv ∧ nv.border = 0) →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {pu pv : Nat}, layer[pu]? = some e.tail → layer[pv]? = some v → pv < pu →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)
/-- Left gap for original plain `v`: ordered intervals put `v` before `t`,
and the footprint starts at `t`'s right edge. -/
private theorem XLEMS_left_orig_gap (exactIds : List String)
    {P : Params} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels
      orderOptions = .ok run)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {pu pv t v : Nat} (hpu : layer[pu]? = some t)
    (hpv : layer[pv]? = some v) (hlt : pv < pu)
    {actualT actualV : ProperNode}
    (hcoordT : run.coordinateProper.nodes[t]? = some actualT)
    (hcoordV : run.coordinateProper.nodes[v]? = some actualV)
    (hb0T : actualT.node.border = 0) (hb0V : actualV.node.border = 0)
    (hfp : (loopFootprintExt cg run labels t).x =
      (RouteImpl.boxRect run.proper run.xs run.ys t).x +
        (RouteImpl.boxRect run.proper run.xs run.ys t).w)
    (hBW : 0 ≤ (RouteImpl.boxRect run.proper run.xs run.ys t).w) :
    (RouteImpl.boxRect run.proper run.xs run.ys v).x +
      (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤
      (loopFootprintExt cg run labels t).x := by
  have hord := XLrr_fixedSep0_holds exactIds P inp cg run labels
    orderOptions hrun layer pv pu v t actualV actualT hlayer hlt hpv hpu
    hcoordV hcoordT hb0V hb0T
  have eV : (RouteImpl.boxRect run.proper run.xs run.ys v).x +
      (RouteImpl.boxRect run.proper run.xs run.ys v).w =
      RouteImpl.leftOf run.proper run.xs v +
        RouteImpl.nodeW run.proper v := rfl
  have eT : (RouteImpl.boxRect run.proper run.xs run.ys t).x =
      RouteImpl.leftOf run.proper run.xs t := rfl
  omega
/-- Left case, proved modulo the non-plain residual. -/
theorem XLEM_leftMiss_holds (exactIds : List String)
    (hRes : XLEM_LeftNonPlain exactIds) : XLEM_LeftMiss exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0
    layer hlayer pu pv hpu hpv hlt
  by_cases hOrig : ∃ nv, cg.nodes[v]? = some nv ∧ nv.border = 0
  · obtain ⟨nv, hnv, hbv⟩ := hOrig
    subst hcg
    have hbd := sceneExecutionX_edges_bounded execution
    have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp
      candidate hcomp hbd (List.mem_of_getElem? hk)
    have hltCG : e.tail < (componentCandidate execution.graph comp candidate).nodes.length :=
      hbnd.1
    obtain ⟨nt, hnt⟩ : ∃ nt,
        (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some nt :=
      ⟨_, List.getElem?_eq_getElem hltCG⟩
    have hnb : nt.border = 0 := by
      have hget : (componentCandidate execution.graph comp candidate).nodes.getD e.tail
          default = nt := by
        rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
      rw [← hget]
      exact hB0
    have hcovered := componentRunX_original_nodes_covered hrun
    have htP : e.tail < run.proper.nodes.length := hcovered e.tail hltCG
    have hne2 : ((componentCandidate execution.graph comp candidate).nodes.getD e.tail
        default).border ≠ -2 := by
      have hget : (componentCandidate execution.graph comp candidate).nodes.getD e.tail
          default = nt := by
        rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
      rw [hget]
      omega
    have hFrBox := plain_frame_eq_boxRect default _ run e.tail htP hne2
    obtain ⟨actualT, hcoordT, hpropT, hb0T, _, _, _⟩ :=
      XLEMS_original_plain_record hrun hnt hnb
    obtain ⟨actualV, hcoordV, _, hb0V, _, _, _⟩ :=
      XLEMS_original_plain_record hrun hnv hbv
    have hBwEq : (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w =
        actualT.node.w := by
      simp only [RouteImpl.boxRect, RouteImpl.nodeW, hpropT]
    have hdims := componentRunX_dims_nonneg hrun
    have hBW : 0 ≤ (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w := by
      rw [hBwEq]
      exact (hdims e.tail actualT hpropT).1
    have hfp := XLEMS_fp_of_frame (labels := execution.measured) hFrBox
    have hgap := XLEMS_left_orig_gap exactIds hrun hlayer hpu hpv hlt
      hcoordT hcoordV hb0T hb0V hfp hBW
    exact XLEMS_rect_miss_left hgap
  · exact hRes inp o res execution comp candidate run orderOptions cg k e v
      hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0 hOrig hlayer
      hpu hpv hlt
/-- Narrower right residual: the right miss for `v` that is not an original
plain node. Strictly narrower than `XLEM_PlainRightMiss` (extra premise),
true on every probe case (all in-scope same-layer `v` there are original
plain nodes, and every footprint is disjoint). -/
def XLEM_PlainRightNonPlain (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (cg.nodes.getD e.tail default).border = 0 →
    (¬ ∃ nv, cg.nodes[v]? = some nv ∧ nv.border = 0) →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {pu pv : Nat}, layer[pu]? = some e.tail → layer[pv]? = some v → pu < pv →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)
/-- Prefixed copy of `XLEML_coord_loopExtent`: `coordinateGraphX` preserves
the loop extent of a plain anchor. -/
private theorem XLEMS_coord_loopExtent {P : Params} {exact : List Nat}
    {p : Proper} {i : Nat} {nd : ProperNode}
    (hp : p.nodes[i]? = some nd) (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.node.loopExtent = nd.node.loopExtent := by
  obtain ⟨sized, hs, hb', hle⟩ :
      ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
        sized.node.border = 0 ∧ sized.node.loopExtent = nd.node.loopExtent := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, hb, rfl⟩
    · refine ⟨_, rfl, hb, rfl⟩
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? =
        some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split
  · refine ⟨_, rfl, ?_⟩
    show sized.node.loopExtent = nd.node.loopExtent
    exact hle
  · exact ⟨_, rfl, hle⟩
/-- Original plain actuals keep the loop extent as well as dims. -/
private theorem XLEMS_actual_loopExtent {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      actual.node.loopExtent = node.loopExtent := by
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec h
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨outD, hdim, _, _, _, _⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  obtain ⟨outL, hloop, hle⟩ := XLEMS_coord_loopExtent hsource hplain
  have hdimC : run.coordinateProper.nodes[index]? = some outD := by
    rw [← hc]
    exact hdim
  have hloopC : run.coordinateProper.nodes[index]? = some outL := by
    rw [← hc]
    exact hloop
  have heq : outD = outL := Option.some.inj (hdimC.symm.trans hloopC)
  have hlabLoop : outL.node.loopExtent = node.loopExtent := hle
  refine ⟨outD, hdimC, ?_⟩
  rw [heq]
  exact hlabLoop
/-- Candidate nodes map from the graph; loop extents agree via `getD`. -/
private theorem XLEMS_candidate_loopExtent {g : Graph} {comp : List Nat}
    {candidate : Nat} {t : Nat} {nt : Node}
    (hnt : (componentCandidate g comp candidate).nodes[t]? = some nt)
    (hlt : t < (componentCandidate g comp candidate).nodes.length) :
    (componentCandidate g comp candidate).nodes.getD t default = nt ∧
      g.nodes.getD (comp.getD t 0) default = nt := by
  have hget : (componentCandidate g comp candidate).nodes.getD t default = nt := by
    rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
  have hcc : (componentCandidate g comp candidate).nodes =
      comp.map fun key => g.nodes.getD key default := by
    rw [componentCandidate_nodes]
    unfold componentGraph
    rfl
  have hlen : (componentCandidate g comp candidate).nodes.length = comp.length := by
    rw [hcc, List.length_map]
  have hvl : t < comp.length := by omega
  have hgetC : comp.getD t 0 = comp[t]'hvl := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvl,
      Option.getD_some]
  have h1 : (comp.map fun key => g.nodes.getD key default)[t]? = some nt := by
    rw [← hcc]
    exact hnt
  rw [List.getElem?_map] at h1
  have h2 : comp[t]? = some (comp.getD t 0) := by
    have h3 := List.getElem?_eq_getElem hvl
    rwa [← hgetC] at h3
  rw [h2, Option.map_some] at h1
  have hgv : g.nodes.getD (comp.getD t 0) default = nt := Option.some.inj h1
  exact ⟨hget, hgv⟩
/-- Prefixed copy of `XLEML_exact_bound`: exact-run membership bridge. -/
private theorem XLEMS_exact_bound {cg : Graph} {exact : List Nat} {t : Nat}
    (h : (cg.nodes.zipIdx.filterMap fun q =>
      if exact.contains q.1.decl then some q.2 else none).contains t = true) :
    t < cg.nodes.length ∧ exact.contains (cg.nodes.getD t default).decl = true := by
  have hm : t ∈ cg.nodes.zipIdx.filterMap fun q =>
      if exact.contains q.1.decl then some q.2 else none :=
    List.contains_iff_mem.mp h
  obtain ⟨q, hq, hfq⟩ := List.mem_filterMap.mp hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  rw [List.getElem?_zipIdx] at hi
  cases hni : cg.nodes[i]? with
  | none => simp [hni] at hi
  | some ni =>
    simp only [hni, Option.map_some, Nat.zero_add] at hi
    have hqq : (ni, i) = q := Option.some.inj hi
    rw [← hqq] at hfq
    dsimp only at hfq
    by_cases hc : exact.contains ni.decl = true
    · simp only [hc, ↓reduceIte] at hfq
      have hti : i = t := Option.some.inj hfq
      subst hti
      refine ⟨(List.getElem?_eq_some_iff.mp hni).1, ?_⟩
      rw [List.getD_eq_getElem?_getD, hni, Option.getD_some]
      exact hc
    · have hconj : exact.contains ni.decl = true ∧ i = t := by simpa using hfq
      exact absurd hconj.1 hc
/-- Prefixed copy of `X_self_run_exact_eq`: exact-run index list equation. -/
private theorem XLEMS_run_exact_eq {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    run.exact = cg.nodes.zipIdx.filterMap
      (fun q : Node × Nat => if exact.contains q.1.decl then some q.2 else none) := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, _, h⟩ := bind_ok h
  obtain ⟨p, _, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨lanes, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨shifted, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  rw [← he]
/-- Prefixed copy of `X_self_run_exact_mem_of_contains`. -/
private theorem XLEMS_run_exact_mem_of_contains {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hv : v < cg.nodes.length)
    (hmem : exact.contains ((cg.nodes[v]'hv).decl) = true) :
    v ∈ run.exact := by
  have heq := XLEMS_run_exact_eq h
  rw [heq]
  have hzipmem : ((cg.nodes[v]'hv), v) ∈ cg.nodes.zipIdx := by
    simpa using List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hv)
  apply List.mem_filterMap.mpr
  refine ⟨((cg.nodes[v]'hv), v), hzipmem, ?_⟩
  simp only [hmem, ↓reduceIte]
/-- Prefixed copy of `X_self_run_exact_not_mem_of_not_contains`. -/
private theorem XLEMS_run_exact_not_mem {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hv : v < cg.nodes.length)
    (hnot : run.exact.contains v = false) :
    exact.contains ((cg.nodes[v]'hv).decl) = false := by
  cases he : exact.contains ((cg.nodes[v]'hv).decl) with
  | true =>
    have hmem := XLEMS_run_exact_mem_of_contains h hv he
    have hcon2 : run.exact.contains v = true := by
      rw [List.contains_eq_mem]
      simp [hmem]
    rw [hcon2] at hnot
    contradiction
  | false => rfl
end PipelineImpl
end Layered
end Elegant

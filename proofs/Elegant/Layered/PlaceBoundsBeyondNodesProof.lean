import Elegant.Layered.LoopRectResidualsProof
import Elegant.Layered.CoordGraph
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ForeignNonGroupSpansProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Placement-bounds fit for beyond-range title copies

The `hfit` sliver of `loopRectTitleCopyReal_holds`
(`LoopRectResidualsProof.lean`): for an executed component run, every
non-dummy proper node `v` at or past the candidate length whose node rect has
positive width and height lies inside `placeBounds`. Executed probes
(`proofs/wip/Probe/TitleCopyFitProbe.lean`) show the only such nodes are the
border-`3` title copies, each inside its group frame; the fold covers every
candidate frame, so the fit follows by transitivity.

The universal (run-free) statement is false: with an empty candidate graph
and an arbitrary far-away proper node, `boundsOf [] [] = ⟨0, 0, 0, 0⟩` covers
nothing. The executed-run hypothesis below is the narrowest restatement the
`LoopRectTitleCopyReal` consumer can still use: at its use site the run
equation is in context.
-/

/-- Transfer a non-proxy proper-node record back to the coordinate phase.
`proxyWidths` only rewidths proxies (`-2`/`2`), so every other node survives
verbatim, with the same `xs` entry. -/
private theorem pbcp_coord_of_proper {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode}
    (hget : run.proper.nodes[v]? = some nd)
    (hborder : ¬ (nd.node.border = -2 ∨ nd.node.border = 2)) :
    run.coordinateProper.nodes[v]? = some nd ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hlen : v < run.coordinateProper.nodes.length := by
    have h1 := (List.getElem?_eq_some_iff.mp hget).1
    have h2 : run.proper.nodes.length = q0.nodes.length := by
      have hd := OrderImpl.dropSynthetic_nodes q0
      rw [← hdrop]
      exact congrArg List.length hd
    have h3 := (proxyWidths_rel hproxy).2.2.1
    omega
  obtain ⟨m', hm'⟩ : ∃ m', run.coordinateProper.nodes[v]? = some m' :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨nd'', hnd'', _, hbdr, _⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 v m' hm'
  have hnd''p : run.proper.nodes[v]? = some nd'' := by
    have hd := OrderImpl.dropSynthetic_nodes q0
    rw [← hdrop, hd]
    exact hnd''
  have heq : nd'' = nd := Option.some.inj (hnd''p.symm.trans hget)
  have hborder' : ¬ (m'.node.border = -2 ∨ m'.node.border = 2) := by
    rw [← hbdr, heq]
    exact hborder
  obtain ⟨hrec, hxs⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v m' hm' hborder'
  have hrecp : run.proper.nodes[v]? = some m' := by
    have hd := OrderImpl.dropSynthetic_nodes q0
    rw [← hdrop, hd]
    exact hrec
  have heq2 : m' = nd := Option.some.inj (hrecp.symm.trans hget)
  refine ⟨by rw [heq2] at hm'; exact hm', ?_⟩
  rw [List.getD_eq_getElem?_getD, hxs, Option.getD_some]

/-- Appended side markers have height `0` by construction. Same induction as
`addClusterBorders_extra`, with the height invariant. -/
private def pbcp_HInv (p : Proper) (s : Proper) : Prop :=
  ∃ extra : List ProperNode, s.nodes = p.nodes ++ extra ∧
    ∀ n ∈ extra, n.node.h = 0

private theorem pbcp_addClusterBorders_extra_h (p : Proper) (bw : Int) :
    ∃ extra : List ProperNode, (OrderImpl.addClusterBorders p bw).nodes =
      p.nodes ++ extra ∧ ∀ n ∈ extra, n.node.h = 0 := by
  unfold OrderImpl.addClusterBorders
  apply OrderImpl.foldl_inv (pbcp_HInv p) _ _ p ⟨[], by simp, by simp⟩
  intro out hout q _
  dsimp only
  split
  · exact hout
  · apply OrderImpl.foldl_inv (pbcp_HInv p) _ _ out hout
    intro state hstate offset _
    obtain ⟨extra, hx, hall⟩ := hstate
    let nl : ProperNode := OrderImpl.borderLeft q bw
    let nr : ProperNode := OrderImpl.borderRight q bw
    refine ⟨extra ++ [nl, nr], ?_, ?_⟩
    · simp [hx, List.append_assoc, nl, nr, OrderImpl.borderLeft,
        OrderImpl.borderRight]
    · intro n hn
      rcases List.mem_append.mp hn with hold | hnew
      · exact hall n hold
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
        rcases hnew with rfl | rfl
        · rfl
        · rfl

/-- Backward step through the in-place prefix: a coordinate node strictly
before the appended title/border region comes from the labelled graph with
the same dummy flag and border. -/
private theorem pbcp_inplace_origin {P : Params} {labeled : Proper}
    {v : Nat} {m' : ProperNode}
    (h : (coordinateGraph P labeled).nodes[v]? = some m')
    (hb3 : m'.node.border ≠ 3)
    (hlt : v < (titleReservations (sizeProperPorts P labeled)).nodes.length) :
    ∃ mL, labeled.nodes[v]? = some mL ∧ m'.dummy = mL.dummy ∧
      m'.node.border = mL.node.border := by
  have hmat := materialize_lookup _ h
  obtain ⟨m1, hm1, hd1, hb1, _, _⟩ := hmat
  have hclr : (clearProxyExtents (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes[v]? =
      some m1 := hm1
  rw [clearProxyExtents_nodes, List.getElem?_map,
    Option.map_eq_some_iff] at hclr
  obtain ⟨m2, hm2, hclearEq⟩ := hclr
  have hkeys2 := clearF_keys m2
  rw [hclearEq] at hkeys2
  obtain ⟨extra, hx, _⟩ := pbcp_addClusterBorders_extra_h
    (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW
  rw [hx, List.getElem?_append_left hlt] at hm2
  rw [titleReservations_nodes] at hm2 hlt
  have hlen := sizeProperPorts_length P labeled
  by_cases hv : v < (sizeProperPorts P labeled).nodes.length
  · rw [List.getElem?_append_left (by rwa [List.length_map]), List.getElem?_map,
      Option.map_eq_some_iff] at hm2
    obtain ⟨s, hs, htitleEq⟩ := hm2
    have hkey := sizeProperPorts_key P labeled v
    rw [hs] at hkey
    cases hL : labeled.nodes[v]? with
    | none => simp [hL] at hkey
    | some mL =>
      simp only [hL, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
      obtain ⟨hdL, hbL, _⟩ := hkey
      have ht := titleF_keys s
      rw [htitleEq] at ht
      exact ⟨mL, rfl, hd1.trans (hkeys2.1.trans (ht.1.trans hdL)),
        hb1.trans (hkeys2.2.1.trans (ht.2.1.trans hbL))⟩
  · have hge : (sizeProperPorts P labeled).nodes.length ≤ v := by omega
    rw [List.getElem?_append_right (by rwa [List.length_map]), List.getElem?_map,
      Option.map_eq_some_iff] at hm2
    obtain ⟨entry, _, hcopyEq⟩ := hm2
    have hcopyBorder : (copyF entry).node.border = 3 := rfl
    rw [hcopyEq] at hcopyBorder
    have hm1Border : m1.node.border = m2.node.border := hkeys2.2.1
    have hm1Border3 : m1.node.border = 3 := hm1Border.trans hcopyBorder
    have hm'Border3 : m'.node.border = 3 := hb1.trans hm1Border3
    exact absurd hm'Border3 hb3
  all_goals try omega

/-- Classification of a beyond-range non-dummy positive node: it is a
border-`3` title copy whose cluster path is its group candidate node's path,
recorded verbatim in the coordinate phase. -/
private theorem pbcp_title_of_beyond {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {v : Nat} {nd : ProperNode}
    (hlen : (componentCandidate execution.graph comp candidate).nodes.length ≤ v)
    (hget : run.proper.nodes[v]? = some nd) (hnd : nd.dummy = false)
    (hw : 0 < (nodeRect (componentCandidate execution.graph comp candidate)
      run v).w)
    (hh : 0 < (nodeRect (componentCandidate execution.graph comp candidate)
      run v).h) :
    ∃ (g : Nat) (nodeG : Node),
      (componentCandidate execution.graph comp candidate).nodes[g]? = some nodeG ∧
      g < (componentCandidate execution.graph comp candidate).nodes.length ∧
      nodeG.border = -2 ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = nodeG.clusterPath ∧
      run.coordinateProper.nodes[v]? = some nd ∧
      run.proper.nodes[v]? = some nd := by
  obtain ⟨_, labeled, _, hc, hkeys, _, _, _⟩ :=
    componentRun_prepared_titled_source execution.graph_eq hcomp hrun
  have hw' : 0 < nd.node.w := by
    rw [nodeRect_of_record hget] at hw
    exact hw
  have hh' : 0 < nd.node.h := by
    rw [nodeRect_of_record hget] at hh
    exact hh
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hlen' : v < run.coordinateProper.nodes.length := by
    have h1 := (List.getElem?_eq_some_iff.mp hget).1
    have h2 : run.proper.nodes.length = q0.nodes.length := by
      have hd := OrderImpl.dropSynthetic_nodes q0
      rw [← hdrop]
      exact congrArg List.length hd
    have h3 := (proxyWidths_rel hproxy).2.2.1
    omega
  obtain ⟨m', hm'⟩ : ∃ m', run.coordinateProper.nodes[v]? = some m' :=
    ⟨_, List.getElem?_eq_getElem hlen'⟩
  have hm'c : (coordinateGraph execution.params labeled).nodes[v]? = some m' := by
    rw [hc]
    exact hm'
  obtain ⟨nd'', hnd'', hdum, hbdr, _⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 v m' hm'
  have hnd''p : run.proper.nodes[v]? = some nd'' := by
    have hd := OrderImpl.dropSynthetic_nodes q0
    rw [← hdrop, hd]
    exact hnd''
  have heq : nd'' = nd := Option.some.inj (hnd''p.symm.trans hget)
  have hm'dum : m'.dummy = false := by
    rw [← hdum, heq]
    exact hnd
  have hm'bdr : m'.node.border = nd.node.border := by
    rw [← hbdr, heq]
  rcases coordinateGraph_lookup execution.params labeled hm'c with
    ⟨m, hm, hdumA, _, _, _⟩ | ⟨_, hbB⟩ | ⟨i, q, hq, _, hdumC, hbdrC, hpathC⟩
  · have hmFalse : m.dummy = false := by
      rw [← hdumA]
      exact hm'dum
    rcases hkeys v m hm with ⟨n, hn, _, _, _⟩ | ⟨hdummy, _, _⟩
    · rw [List.getElem?_eq_none (by omega)] at hn
      cases hn
    · rw [hdummy] at hmFalse
      exact absurd hmFalse (by decide)
  · have hborderN : ¬ (nd.node.border = -2 ∨ nd.node.border = 2) := by
      rw [← hm'bdr]
      rcases hbB with h | h <;> omega
    obtain ⟨hcoord, _⟩ := pbcp_coord_of_proper hrun hget hborderN
    have heqnd : nd = m' := Option.some.inj (hcoord.symm.trans hm')
    by_cases hlt : v <
      (titleReservations (sizeProperPorts execution.params labeled)).nodes.length
    · have hm'Border : m'.node.border ≠ 3 := by
        rcases hbB with h | h <;> omega
      obtain ⟨mL, hmL, hdL, _⟩ := pbcp_inplace_origin hm'c hm'Border hlt
      have hmLFalse : mL.dummy = false := by
        rw [← hdL]
        exact hm'dum
      rcases hkeys v mL hmL with ⟨n, hn, _, _, _⟩ | ⟨hdummy, _, _⟩
      · rw [List.getElem?_eq_none (by omega)] at hn
        cases hn
      · rw [hdummy] at hmLFalse
        exact absurd hmLFalse (by decide)
    · have hle : (titleReservations (sizeProperPorts execution.params labeled)).nodes.length ≤ v :=
        Nat.le_of_not_lt hlt
      have hmat := materialize_lookup _ hm'c
      obtain ⟨m1, hm1, _, _, hh1, _⟩ := hmat
      rw [clearProxyExtents_nodes, List.getElem?_map,
        Option.map_eq_some_iff] at hm1
      obtain ⟨m2, hm2, hclearEq⟩ := hm1
      obtain ⟨extra, hx, hall⟩ := pbcp_addClusterBorders_extra_h
        (titleReservations (sizeProperPorts execution.params labeled))
        execution.params.clusterBorderW
      rw [hx, List.getElem?_append_right hle] at hm2
      have hm2h : m2.node.h = 0 :=
        hall m2 (List.mem_of_getElem? hm2)
      have hk := clearF_keys m2
      rw [hclearEq] at hk
      rw [heqnd, hh1] at hh'
      rw [hk.2.2.2] at hh'
      rw [hm2h] at hh'
      omega
  · have hborderN : ¬ (nd.node.border = -2 ∨ nd.node.border = 2) := by
      rw [← hm'bdr, hbdrC]
      decide
    obtain ⟨hcoord, _⟩ := pbcp_coord_of_proper hrun hget hborderN
    have heqnd : nd = m' := Option.some.inj (hcoord.symm.trans hm')
    have hqreal : q.1.dummy = false := by
      rw [← hdumC]
      exact hm'dum
    have hpath : m'.node.clusterPath = q.1.node.clusterPath :=
      hpathC hqreal
    obtain ⟨hsized, hb2⟩ := titleNodes_spec hq
    obtain ⟨orig, horig, hdO, hbO, hpO⟩ :=
      sizeProperPorts_node_origin _ _ hsized
    have horigReal : orig.dummy = false := by
      rw [← hdO]
      exact hqreal
    rcases hkeys q.2 orig horig with ⟨n, hn, _, hbN, hpN⟩ | ⟨hdummy, _, _⟩
    · have hglt := (List.getElem?_eq_some_iff.mp hn).1
      have hborderG : n.border = -2 := by
        rw [← hbN, ← hbO]
        exact hb2
      have hborder3 : nd.node.border = 3 := by
        rw [heqnd]
        exact hbdrC
      have hndpath : nd.node.clusterPath = n.clusterPath := by
        rw [heqnd]
        exact hpath.trans (hpO.trans hpN)
      exact ⟨q.2, n, hn, hglt, hborderG, hborder3, hndpath, hcoord, hget⟩
    · rw [hdummy] at horigReal
      exact absurd horigReal (by decide)

/-- The placement-bounds fit: a beyond-range non-dummy positive node rect
lies inside `placeBounds`, via its group frame. -/
private theorem pbcp_placeBounds_fit {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {v : Nat} {nd : ProperNode}
    (hlen : (componentCandidate execution.graph comp candidate).nodes.length ≤ v)
    (hget : run.proper.nodes[v]? = some nd) (hnd : nd.dummy = false)
    (hw : 0 < (nodeRect (componentCandidate execution.graph comp candidate)
      run v).w)
    (hh : 0 < (nodeRect (componentCandidate execution.graph comp candidate)
      run v).h) :
    (placeBounds execution.params (componentCandidate execution.graph comp candidate)
      run execution.measured loops).minX ≤
      (nodeRect (componentCandidate execution.graph comp candidate) run v).x ∧
      (nodeRect (componentCandidate execution.graph comp candidate) run v).x +
      (nodeRect (componentCandidate execution.graph comp candidate) run v).w ≤
      (placeBounds execution.params (componentCandidate execution.graph comp candidate)
        run execution.measured loops).right ∧
    (placeBounds execution.params (componentCandidate execution.graph comp candidate)
      run execution.measured loops).minY ≤
      (nodeRect (componentCandidate execution.graph comp candidate) run v).y ∧
    (nodeRect (componentCandidate execution.graph comp candidate) run v).y +
      (nodeRect (componentCandidate execution.graph comp candidate) run v).h ≤
      (placeBounds execution.params (componentCandidate execution.graph comp candidate)
        run execution.measured loops).bottom := by
  obtain ⟨g, nodeG, hnodeG, hglt, hgroup, hb3, hpath, hcoord⟩ :=
    pbcp_title_of_beyond execution hcomp hrun hlen hget hnd hw hh
  let cg : Graph := componentCandidate execution.graph comp candidate
  obtain ⟨ord, left, right, horder, hlayers, hleft, hright, hbracket⟩ :=
    componentRun_group_title_bracket execution.graph_eq hcomp hrun hnodeG hgroup
      hcoord.1 hb3 hpath
  obtain ⟨origIdx, _, hgraphnode⟩ :=
    componentCandidate_nonplain_source hnodeG (by omega)
  obtain ⟨_, _, _, _, hpathG⟩ :=
    measuredGraph_group_origin execution.graph_eq hgraphnode hgroup
  have howner : nodeG.clusterPath.getLast? = some nodeG.decl := by
    rw [hpathG, List.getLast?_append]
    simp
  have hself : nodeG.clusterPath.contains nodeG.decl = true := by
    rw [hpathG]
    simp
  obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hmi hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  have hbL : (OrderImpl.borderLeft (titleF ⟨nodeG, false, none, false⟩, g)
      execution.params.clusterBorderW).node.border = -1 := rfl
  have hbR : (OrderImpl.borderRight (titleF ⟨nodeG, false, none, false⟩, g)
      execution.params.clusterBorderW).node.border = 1 := rfl
  have sepL := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp hrun
    hlayer hlt hli hmi hleft hcoord.1 (by omega) (by omega)
  have sepR := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp hrun
    hlayer htr hmi hri hcoord.1 hright (by omega) (by omega)
  obtain ⟨hleftRec, hleftX⟩ :=
    componentRun_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightRec, hrightX⟩ :=
    componentRun_border_record hrun hright (Or.inr rfl)
  obtain ⟨htitleRec, htitleX⟩ :=
    componentRun_nonproxy_record hrun hcoord.1 (by omega)
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hsizes := (crossCoordsClusterWith_spec hcross).2.2.2.1
  have hLw : 0 ≤ (Labels.rectAt run.proper run.xs run.ys left).w := by
    have eW : RouteImpl.nodeW run.proper left =
        (OrderImpl.borderLeft (titleF ⟨nodeG, false, none, false⟩, g)
          execution.params.clusterBorderW).node.w := by
      simp only [RouteImpl.nodeW, hleftRec]
    have hnn := (sizesNonneg_lookup hsizes left _ hleft).1
    simp only [rectAt_eq] at *
    omega
  have hRw : 0 ≤ (Labels.rectAt run.proper run.xs run.ys right).w := by
    have eW : RouteImpl.nodeW run.proper right =
        (OrderImpl.borderRight (titleF ⟨nodeG, false, none, false⟩, g)
          execution.params.clusterBorderW).node.w := by
      simp only [RouteImpl.nodeW, hrightRec]
    have hnn := (sizesNonneg_lookup hsizes right _ hright).1
    simp only [rectAt_eq] at *
    omega
  have eLx : (Labels.rectAt run.proper run.xs run.ys left).x =
      RouteImpl.leftOf run.proper run.xs left := by rw [rectAt_eq]
  have eLw : (Labels.rectAt run.proper run.xs run.ys left).w =
      RouteImpl.nodeW run.proper left := by rw [rectAt_eq]
  have eRx : (Labels.rectAt run.proper run.xs run.ys right).x =
      RouteImpl.leftOf run.proper run.xs right := by rw [rectAt_eq]
  have eRw : (Labels.rectAt run.proper run.xs run.ys right).w =
      RouteImpl.nodeW run.proper right := by rw [rectAt_eq]
  have eVx : (nodeRect cg run v).x = RouteImpl.leftOf run.proper run.xs v := by
    rw [nodeRect_of_record hget]
  have eVw : (nodeRect cg run v).w = nd.node.w := by
    rw [nodeRect_of_record hget]
  have eVy : (nodeRect cg run v).y = run.ys.getD v 0 := by
    rw [nodeRect_of_record hget]
  have eVh : (nodeRect cg run v).h = nd.node.h := by
    rw [nodeRect_of_record hget]
  have hLX : (Labels.rectAt run.proper run.xs run.ys left).x +
      (Labels.rectAt run.proper run.xs run.ys left).w ≤ (nodeRect cg run v).x := by
    rw [eLx, eLw, eVx]
    exact sepL
  have hNvw : RouteImpl.nodeW run.proper v = nd.node.w := by
    simp only [RouteImpl.nodeW, hget]
  have hRX : (nodeRect cg run v).x + (nodeRect cg run v).w ≤
      (Labels.rectAt run.proper run.xs run.ys right).x +
        (Labels.rectAt run.proper run.xs run.ys right).w := by
    rw [eRx, eRw, eVx, eVw, ← hNvw]
    omega
  have htitleRect : Labels.rectAt run.proper run.xs run.ys v =
      nodeRect cg run v := by
    simp only [Labels.rectAt, Labels.labelRect, nodeRect,
      RouteImpl.xAt, RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH,
      List.getD_eq_getElem?_getD, hget, Option.getD_some]
  let borders := run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some nodeG.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  let rects := run.proper.nodes.zipIdx.filterMap fun q =>
    if q.1.node.clusterPath.contains nodeG.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have hleftMem : Labels.rectAt run.proper run.xs run.ys left ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, left), List.mk_mem_zipIdx_iff_getElem?.mpr hleftRec, ?_⟩
    simp [OrderImpl.borderLeft, titleF, hgroup, howner]
  have hrightMem : Labels.rectAt run.proper run.xs run.ys right ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, right), List.mk_mem_zipIdx_iff_getElem?.mpr hrightRec, ?_⟩
    simp [OrderImpl.borderRight, titleF, hgroup, howner]
  have htitleMem : Labels.rectAt run.proper run.xs run.ys v ∈ rects := by
    apply List.mem_filterMap.mpr
    refine ⟨(nd, v), List.mk_mem_zipIdx_iff_getElem?.mpr hget, ?_⟩
    have hcond : (nd.node.clusterPath.contains nodeG.decl) = true := by
      rw [hpath]; exact hself
    show (if nd.node.clusterPath.contains nodeG.decl = true then
      some (Labels.rectAt run.proper run.xs run.ys v) else none) =
      some (Labels.rectAt run.proper run.xs run.ys v)
    exact ite_eq_left hcond
  have hframeX : (frameRect execution.params cg run g).x =
      (boundsOf borders []).minX := by
    show (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run g).x =
      (boundsOf borders []).minX
    simp only [frameRect, List.getD_eq_getElem?_getD, hnodeG, Option.getD_some, hgroup]
    rw [ite_eq_right (by decide)]
  have hframeY : (frameRect execution.params cg run g).y =
      (boundsOf rects []).minY := by
    show (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run g).y =
      (boundsOf rects []).minY
    simp only [frameRect, List.getD_eq_getElem?_getD, hnodeG, Option.getD_some, hgroup]
    rw [ite_eq_right (by decide)]
  have hframeW := frameRect_group_width_eq_horizontal_span (P := execution.params)
    (run := run) hnodeG hgroup
  have hframeH := frameRect_group_height_eq_vertical_span (P := execution.params)
    (run := run) hnodeG hgroup
  have hlo := boundsOf_minX_le_rect_x borders []
    (Labels.rectAt run.proper run.xs run.ys left) hleftMem
  have hhi := rect_right_le_boundsOf_right borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have htop := boundsOf_minY_le_rect_y rects []
    (Labels.rectAt run.proper run.xs run.ys v) htitleMem
  have hbot := rect_bottom_le_boundsOf_bottom rects []
    (Labels.rectAt run.proper run.xs run.ys v) htitleMem
  have hmemFrame : frameRect execution.params cg run g ∈
      (List.range cg.nodes.length).map (frameRect execution.params cg run) := by
    apply List.mem_map.mpr
    exact ⟨g, List.mem_range.mpr hglt, rfl⟩
  have hmemFold : frameRect execution.params cg run g ∈
      ((List.range cg.nodes.length).map (frameRect execution.params cg run) ++
      (((List.range cg.nodes.length).map
        (frameRect execution.params cg run)).zipIdx.map fun q =>
        ⟨q.1.x + q.1.w, q.1.y,
          Loops.extent cg.slot (loopSizes cg.edges execution.measured q.2 cg.slot),
          q.1.h⟩) ++
      labelBounds execution.params cg run execution.measured ++
      (componentTitles execution.params cg run).map (·.2)) := by
    apply List.mem_append.mpr
    left
    apply List.mem_append.mpr
    left
    apply List.mem_append.mpr
    left
    exact hmemFrame
  have hfit := boundsOf_contains_rect _
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))
    (frameRect execution.params cg run g) hmemFold
  simp only [placeBounds] at hfit ⊢
  obtain ⟨hbx1, hbx2, hby1, hby2⟩ := hfit
  rw [hframeX] at hbx1
  rw [hframeY] at hby1
  rw [htitleRect] at htop hbot
  have hrightEq : (boundsOf borders []).right =
      (frameRect execution.params cg run g).x +
        (frameRect execution.params cg run g).w := by
    rw [hframeX, hframeW]
    simp only [borders]
    omega
  have hbotEq : (boundsOf rects []).bottom =
      (frameRect execution.params cg run g).y +
        (frameRect execution.params cg run g).h := by
    rw [hframeY, hframeH]
    simp only [rects]
    omega
  have hleftLe : (Labels.rectAt run.proper run.xs run.ys left).x ≤
      (nodeRect cg run v).x := by
    have hw2 : (Labels.rectAt run.proper run.xs run.ys left).x ≤
        (Labels.rectAt run.proper run.xs run.ys left).x +
        (Labels.rectAt run.proper run.xs run.ys left).w := by omega
    exact Int.le_trans hw2 hLX
  refine ⟨Int.le_trans hbx1 (Int.le_trans hlo hleftLe),
    Int.le_trans hRX (Int.le_trans (hrightEq ▸ hhi) hbx2),
    Int.le_trans hby1 htop,
    Int.le_trans (hbotEq ▸ hbot) hby2⟩

/-- Local copy of `LoopRectResidualsProof.lrrPlaceWidth`. -/
private theorem pbcpPlaceWidth (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run 0 labels loops).width =
      (placeBounds P cg run labels loops).right -
        (placeBounds P cg run labels loops).minX := rfl

/-- Local copy of `LoopRectResidualsProof.lrrPlaceHeight`. -/
private theorem pbcpPlaceHeight (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run 0 labels loops).height =
      (placeBounds P cg run labels loops).bottom -
        (placeBounds P cg run labels loops).minY := rfl

/-- Closed title-copy seam: `LoopRectTitleCopyReal` from well-formedness and
framed parents, with the executed plain-frame disjointness residual. The
placement fit is `pbcp_placeBounds_fit`, proved above. The residual is
restricted to executed component runs (the use site below supplies the
execution, component, candidate, and run equation), since the run-free
universal over arbitrary `cg`/`run` pairs is false. -/
theorem loopRectTitleCopy_holds {inp : Input} {o : Options} {res : FamilyResult}
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (hsep : ∀ (execution : SceneExecution inp o res) (comp : List Nat)
      (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        orderOptions = .ok run →
      ∀ (v w : Nat) (nd : ProperNode) (member : Node),
      (componentCandidate execution.graph comp candidate).nodes.length ≤ v →
      run.proper.nodes[v]? = some nd → nd.dummy = false →
      0 < (nodeRect (componentCandidate execution.graph comp candidate) run v).w →
      0 < (nodeRect (componentCandidate execution.graph comp candidate) run v).h →
      (componentCandidate execution.graph comp candidate).nodes[w]? = some member →
      member.border = 0 →
      Disjoint (nodeRect (componentCandidate execution.graph comp candidate) run v)
        (nodeRect (componentCandidate execution.graph comp candidate) run w)) :
    LoopRectTitleCopyReal inp o res := by
  intro execution candidate run packed hpack c q hselected _area loops hpart hcomp hrun v hreal hn hpne hposW hposH
  have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length ≤ v :=
    List.getElem?_eq_none_iff.mp hn
  obtain ⟨nd, hnd⟩ := Option.ne_none_iff_exists.mp hpne
  have hnd' : run.proper.nodes[v]? = some nd := hnd.symm
  have hndFalse : nd.dummy = false := hreal nd hnd'
  have hgetV : (componentCandidate execution.graph q.1.1 candidate).nodes.getD v default =
      default := by
    rw [List.getD_eq_getElem?_getD, hn, Option.getD_none]
  have hbdef : (default : Node).border = 0 := rfl
  have hfrV : frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v =
      nodeRect (componentCandidate execution.graph q.1.1 candidate) run v :=
    frameRect_of_border_zero hgetV hbdef
  have hnposW : 0 < (nodeRect (componentCandidate execution.graph q.1.1 candidate) run v).w := by
    rw [← hfrV]
    exact hposW

  have hnposH : 0 < (nodeRect (componentCandidate execution.graph q.1.1 candidate) run v).h := by
    rw [← hfrV]
    exact hposH
  refine ⟨?_, ?_⟩
  · have hfitInst := pbcp_placeBounds_fit execution hcomp hrun
      (loops := loops) hlen hnd' hndFalse hnposW hnposH
    rw [← hfrV] at hfitInst
    have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
      zip_getElem?_left hselected
    have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
      rw [Pack.pack_count hpack, List.length_map]
    have hclen : c < packed.boxes.length := by
      have hlt := (List.getElem?_eq_some_iff.mp hmemc).1
      omega
    have hshelfC : packed.boxes[c]? = some q.2 :=
      (List.getElem?_zip_eq_some.mp hselected).2
    have hL : partRectT execution packed c (shiftRect (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX) (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY) (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v)) =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH (shiftRect q.2.x q.2.y
        (shiftRect (0 - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX)
          (0 - (placeBounds execution.params
          (componentCandidate execution.graph q.1.1 candidate) run execution.measured
          loops).minY)
          (frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
      unfold partRectT
      rw [hshelfC, Option.getD_some]
    have hS : shelfRectT execution packed c =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH q.2) := by
      unfold shelfRectT
      rw [hshelfC, Option.getD_some]
    rw [hL, hS]
    refine orient_transport_contained ?_
    have hboxEq : packed.boxes[c] = q.2 :=
      Option.some.inj ((List.getElem?_eq_getElem hclen).symm.trans hshelfC)
    have hmapLen : c < (execution.componentsAcc.parts.map fun q =>
        Pack.Item.mk q.2.width q.2.height q.2.area).length := by
      rw [List.length_map]
      exact (List.getElem?_eq_some_iff.mp hmemc).1
    have hpartget : execution.componentsAcc.parts[c] = q.1 :=
      (List.getElem?_eq_some_iff.mp hmemc).2
    have hitem : (execution.componentsAcc.parts.map fun q =>
        Pack.Item.mk q.2.width q.2.height q.2.area)[c] =
        Pack.Item.mk q.1.2.width q.1.2.height q.1.2.area := by
      rw [List.getElem_map, hpartget]
    obtain ⟨hsw, hsh⟩ := packShelfDims hpack hclen hmapLen
    have hW : q.2.w = (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).right - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX := by
      have e1 : q.2.w = packed.boxes[c].w := by rw [hboxEq]
      have hPW : q.1.2.width = (placeComponent execution.params
          (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
          loops).width := by rw [hpart]
      rw [e1, hsw, hitem, hPW, pbcpPlaceWidth]
    have hH : q.2.h = (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).bottom - (placeBounds execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY := by
      have e1 : q.2.h = packed.boxes[c].h := by rw [hboxEq]
      have hPH : q.1.2.height = (placeComponent execution.params
          (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
          loops).height := by rw [hpart]
      rw [e1, hsh, hitem, hPH, pbcpPlaceHeight]
    simp only [shiftRect, Rect.Contained]
    omega
  · intro w member hnodeW hbW
    have hsepInst := hsep execution q.1.1 candidate run (candidateOrder candidate)
      hcomp hrun v w nd member hlen hnd' hndFalse hnposW hnposH hnodeW hbW
    have hgetW : (componentCandidate execution.graph q.1.1 candidate).nodes.getD w default =
        member := by
      rw [List.getD_eq_getElem?_getD, hnodeW, Option.getD_some]
    have hfrW : frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w =
        nodeRect (componentCandidate execution.graph q.1.1 candidate) run w :=
      frameRect_of_border_zero hgetW hbW
    rw [hfrV, hfrW]
    exact hsepInst

end PipelineImpl
end Layered
end Elegant

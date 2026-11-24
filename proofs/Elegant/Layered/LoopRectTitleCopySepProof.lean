import Elegant.Layered.PlaceBoundsBeyondNodesProof
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.LoopRectResidualsProof
import Elegant.Layered.LoopRectRealClosed
import Elegant.Layered.CoordGraph
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Coords

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Executed title-copy/plain disjointness, closing `loopRectTitleCopy_holds`

The residual `hsep` of `loopRectTitleCopy_holds`
(`PlaceBoundsBeyondNodesProof.lean`) is now restricted to executed component
runs. This module proves that restricted fact and delivers
`loopRectTitleCopy_closed` with exactly the seam type `loopRectTitleCopy` of
`LayeredSeams`, from `WellFormed` and `framedParents` only.

The unrestricted run-free universal over arbitrary `cg`/`run` pairs is false:
retargeting one executed beyond-range rect onto a plain rect keeps every
premise true while the rects coincide
(`proofs/wip/Probe/TitleCopySepProbe.lean`, `tamper` row: all premises true,
`rectEq=true`, `disj=false`). The same probe shows the executed fact true on
every (beyond-range positive non-dummy, plain) pair of the probed runs
(`pairs=12 bad=0` on the nested three-deep input, vacuously `pairs=0` on the
single-node input).

Proof route: the copy side reuses the title-copy classification below (a
beyond-range non-dummy positive node is a border-`3` title copy recorded
verbatim in the coordinate phase); the plain side uses the original plain
record; both sides then join the rank-band / ordered-interval argument of
`componentRun_positions_disjoint` (`RankSiblingDisjoint.lean`).
-/

/-- Transfer a non-proxy proper-node record back to the coordinate phase.
`proxyWidths` only rewidths proxies (`-2`/`2`), so every other node survives
verbatim, with the same `xs` entry. -/
private theorem tcs_coord_of_proper {P : Params} {cg : Graph} {run : Run}
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
private def tcs_HInv (p : Proper) (s : Proper) : Prop :=
  ∃ extra : List ProperNode, s.nodes = p.nodes ++ extra ∧
    ∀ n ∈ extra, n.node.h = 0

private theorem tcs_addClusterBorders_extra_h (p : Proper) (bw : Int) :
    ∃ extra : List ProperNode, (OrderImpl.addClusterBorders p bw).nodes =
      p.nodes ++ extra ∧ ∀ n ∈ extra, n.node.h = 0 := by
  unfold OrderImpl.addClusterBorders
  apply OrderImpl.foldl_inv (tcs_HInv p) _ _ p ⟨[], by simp, by simp⟩
  intro out hout q _
  dsimp only
  split
  · exact hout
  · apply OrderImpl.foldl_inv (tcs_HInv p) _ _ out hout
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
private theorem tcs_inplace_origin {P : Params} {labeled : Proper}
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
  obtain ⟨extra, hx, _⟩ := tcs_addClusterBorders_extra_h
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
private theorem tcs_title_of_beyond {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
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
    obtain ⟨hcoord, _⟩ := tcs_coord_of_proper hrun hget hborderN
    have heqnd : nd = m' := Option.some.inj (hcoord.symm.trans hm')
    by_cases hlt : v <
      (titleReservations (sizeProperPorts execution.params labeled)).nodes.length
    · have hm'Border : m'.node.border ≠ 3 := by
        rcases hbB with h | h <;> omega
      obtain ⟨mL, hmL, hdL, _⟩ := tcs_inplace_origin hm'c hm'Border hlt
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
      obtain ⟨extra, hx, hall⟩ := tcs_addClusterBorders_extra_h
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
    obtain ⟨hcoord, _⟩ := tcs_coord_of_proper hrun hget hborderN
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

/-- Executed disjointness of a beyond-range positive non-dummy title copy
from every in-range plain frame: the plain side uses the original plain
record, the copy side uses the title classification above, and both sides
join the rank-band / ordered-interval argument of
`componentRun_positions_disjoint`. -/
private theorem tcs_title_plain_disjoint
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {v w : Nat} {nd : ProperNode} {member : Node}
    (hlen : (componentCandidate execution.graph comp candidate).nodes.length ≤ v)
    (hget : run.proper.nodes[v]? = some nd) (hnd : nd.dummy = false)
    (hposW : 0 < (nodeRect (componentCandidate execution.graph comp candidate)
      run v).w)
    (hposH : 0 < (nodeRect (componentCandidate execution.graph comp candidate)
      run v).h)
    (hnodeW : (componentCandidate execution.graph comp candidate).nodes[w]? =
      some member)
    (hbW : member.border = 0) :
    Disjoint (nodeRect (componentCandidate execution.graph comp candidate)
      run v)
      (nodeRect (componentCandidate execution.graph comp candidate)
      run w) := by
  have hwlt : w < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnodeW).1
  obtain ⟨actualW, hcoordW, hpropW, _, hbW0, _, _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnodeW hbW
  obtain ⟨_, _, _, _, _, hb3, _, hcoordV, _⟩ :=
    tcs_title_of_beyond execution hcomp hrun hlen hget hnd hposW hposH
  have hbV : ¬ (nd.node.border = -2 ∨ nd.node.border = 2) := by
    rw [hb3]
    decide
  have hne : w ≠ v := by omega
  have hcovered := componentRun_original_nodes_covered hrun
  have hwP : w < run.proper.nodes.length := hcovered w hwlt
  have hvP : v < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  have hrectV : nodeRect (componentCandidate execution.graph comp candidate)
      run v =
      ⟨run.xs.getD v 0 - Int.fdiv nd.node.w 2, run.ys.getD v 0,
        nd.node.w, nd.node.h⟩ := by
    simp [nodeRect, hget]
  have hrectW : nodeRect (componentCandidate execution.graph comp candidate)
      run w =
      ⟨run.xs.getD w 0 - Int.fdiv actualW.node.w 2, run.ys.getD w 0,
        actualW.node.w, actualW.node.h⟩ := by
    simp [nodeRect, hpropW]
  obtain ⟨_, _, _, q0, _, _, _, hord, _, hproxy, hdrop, hroute,
    _, hry, hys, _⟩ := componentRun_spec hrun
  obtain ⟨ord, hordOk, hordLayers⟩ := hord
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hrank, hqlen, _, _, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have hwC : w < run.coordinateProper.nodes.length := by omega
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact hrank
  obtain ⟨_, _, _, _, _, _, hy⟩ :=
    CoordsImpl.rankCoordsWith_spec hry
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    rw [hy]; simp
  have hwCy : w < run.coordinateYs.length := by omega
  have hvCy : v < run.coordinateYs.length := by omega
  have hysEqW : run.ys.getD w 0 = run.coordinateYs.getD w 0 := by
    rw [← hys, proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      hcoordW hwCy, hbW0]
    rfl
  have hysEqV : run.ys.getD v 0 = run.coordinateYs.getD v 0 := by
    rw [← hys, proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      hcoordV hvCy, hb3]
    rfl
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨lW, hlyW, hwIn, hrkW⟩ := hcov w hwP
  obtain ⟨lV, hlyV, hvIn, hrkV⟩ := hcov v hvP
  let rW : Nat := (rk run.proper.rank w).toNat
  let rV : Nat := (rk run.proper.rank v).toNat
  have hrkWdef : rW = (rk run.proper.rank w).toNat := rfl
  have hrkVdef : rV = (rk run.proper.rank v).toNat := rfl
  have hrkW' : rk run.proper.rank w = (rW : Int) := by
    have h := Int.toNat_of_nonneg hrkW
    exact h.symm
  have hrkV' : rk run.proper.rank v = (rV : Int) := by
    have h := Int.toNat_of_nonneg hrkV
    exact h.symm
  have hrkCoordW : rk run.coordinateProper.rank w = (rW : Int) := by
    rw [← hranks]; exact hrkW'
  have hrkCoordV : rk run.coordinateProper.rank v = (rV : Int) := by
    rw [← hranks]; exact hrkV'
  have hlyW' : run.layers[rW]? = some lW := hlyW
  have hlyV' : run.layers[rV]? = some lV := hlyV
  rcases Nat.lt_trichotomy rW rV with hlt | heq | hgt
  · have hbandW := rankAxis_node_in_band hry hlyW' hwIn hwC hrkCoordW
    have hbandV := rankAxis_node_in_band hry hlyV' hvIn hvC hrkCoordV
    have hbands := rankAxis_bands_disjoint hry rW rV lW lV hlt hlyW' hlyV'
    have hnodeHW : CoordsImpl.nodeH run.coordinateProper w = actualW.node.h := by
      simp [CoordsImpl.nodeH, hcoordW]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = nd.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hrectV, hrectW]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega
  · rw [heq] at hlyW'
    obtain hlVeq : lV = lW := Option.some.inj (hlyV'.symm.trans hlyW')
    rw [hlVeq] at hvIn
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp hwIn
    obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hvIn
    have hnePV : pu ≠ pv := by
      intro heq'
      subst heq'
      exact hne (Option.some.inj (hpu.symm.trans hpv))
    have hlayerMem : lW ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyW'
      rw [← hmemEq]
      exact List.getElem_mem hmemLT
    rcases Nat.lt_or_gt_of_ne hnePV with hplt | hpgt
    · have hsep := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp hrun
        (layer := lW) hlayerMem
        hplt hpu hpv hcoordW hcoordV
        (by simp [hbW0]) (by rw [hb3]; decide)
      have hnodeWW : RouteImpl.nodeW run.proper w = actualW.node.w := by
        simp [RouteImpl.nodeW, hpropW]
      have hnodeWV : RouteImpl.nodeW run.proper v = nd.node.w := by
        simp [RouteImpl.nodeW, hget]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWW, hnodeWV] at hsep
      rw [hrectV, hrectW]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
    · have hsep := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp hrun
        (layer := lW) hlayerMem
        hpgt hpv hpu hcoordV hcoordW
        (by rw [hb3]; decide) (by simp [hbW0])
      have hnodeWW : RouteImpl.nodeW run.proper w = actualW.node.w := by
        simp [RouteImpl.nodeW, hpropW]
      have hnodeWV : RouteImpl.nodeW run.proper v = nd.node.w := by
        simp [RouteImpl.nodeW, hget]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWW, hnodeWV] at hsep
      rw [hrectV, hrectW]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
  · have hbandW := rankAxis_node_in_band hry hlyW' hwIn hwC hrkCoordW
    have hbandV := rankAxis_node_in_band hry hlyV' hvIn hvC hrkCoordV
    have hbands := rankAxis_bands_disjoint hry rV rW lV lW hgt hlyV' hlyW'
    have hnodeHW : CoordsImpl.nodeH run.coordinateProper w = actualW.node.h := by
      simp [CoordsImpl.nodeH, hcoordW]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = nd.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hrectV, hrectW]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

/-- Closed title-copy seam: `LoopRectTitleCopyReal` from well-formedness and
framed parents, discharging the executed plain-frame disjointness residual
proved above. -/
theorem loopRectTitleCopy_closed (inp : Input) (o : Options) (res : FamilyResult)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
    LoopRectTitleCopyReal inp o res :=
  loopRectTitleCopy_holds hwf hfp
    (fun execution _comp _candidate _run _orderOptions hcomp hrun _v _w _nd _member hlen hget hnd hw hh hnodeW hbW =>
      tcs_title_plain_disjoint execution hcomp hrun hlen hget hnd hw hh hnodeW hbW)

end PipelineImpl
end Layered
end Elegant

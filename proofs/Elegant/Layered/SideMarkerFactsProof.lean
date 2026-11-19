import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Order

set_option autoImplicit false

/-!
# The side-marker facts of the non-group span seam.

`ForeignNonGroupSpansProof` leaves three residuals about the marker pairs of
one group declaration at one rank:

* `BracketMarkersAtRank` — a bracketed rank carries a left/right marker pair;
* `SideMarkerSpanAligned` — same-side markers share one `x`-span with
  nonnegative right edge, and a left marker lies left of a same-rank right
  marker;
* `PlainClearOfSideMarker` — a plain node off the group lies beyond the pair.

This module proves the alignment conjunct and the nonnegative right edge
outright, and proves the three facts from three named single-phase residuals:

* `SideMarkerRankCover` (rank assignment): the `Int`-native form of the
  bracket conclusion;
* `SideMarkerPairOrdered` (layer order): the left marker precedes the right
  marker in their common layer;
* `PlainOutsideMarkerPair` (layer order): a plain node off the group lies
  outside the marker pair in their common layer.

The `Int` rank form is load-bearing for `bracketMarkersAtRank`: the goal's
`Nat`/`toNat` bracketing converts to it through rank nonnegativity
(`layersOk_spec` coverage).  `hspans` is retained for the prescribed seam-bundle
shape; the rank cover carries the marker content.
-/

namespace Elegant.Layered.PipelineImpl

/-! ## Executed-run transfers -/

/-- The final rank assignment is the coordinate rank assignment. -/
theorem proper_rank_eq_coordinate {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) :
    run.proper.rank = run.coordinateProper.rank := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  rw [← hdrop, OrderImpl.dropSynthetic_rank]
  exact hrankEq

/-- A non-proxy record of the final run is the same coordinate record. -/
theorem coordinateProper_of_proper_nonsynthetic {P : Params} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hb : nd.node.border ≠ -2 ∧ nd.node.border ≠ 2) :
    run.coordinateProper.nodes[v]? = some nd := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, _, hlen, _, hpresAll, hpresSame⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq0v : q0.nodes[v]? = some nd := by rw [← hnodes]; exact hv
  have hlenv : v < run.coordinateProper.nodes.length := by
    have hlt : v < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0v).1
    omega
  obtain ⟨nd', hnd'⟩ : ∃ nd', run.coordinateProper.nodes[v]? = some nd' :=
    ⟨_, List.getElem?_eq_getElem hlenv⟩
  obtain ⟨nd'', hnd'', _, hborderEq, _⟩ := hpresAll v nd' hnd'
  have hnn : nd'' = nd := Option.some.inj (hnd''.symm.trans hq0v)
  have hbeq : nd'.node.border = nd.node.border := by rw [← hborderEq, hnn]
  have hnd'nproxy : ¬ (nd'.node.border = -2 ∨ nd'.node.border = 2) := by
    rw [hbeq]
    exact fun h => h.elim hb.1 hb.2
  obtain ⟨hqSame, _⟩ := hpresSame v nd' hnd' hnd'nproxy
  have hsame : nd' = nd := Option.some.inj (hqSame.symm.trans hq0v)
  rw [hsame] at hnd'
  exact hnd'

/-- A side marker keeps its cross-coordinate centre through proxy widths. -/
theorem coordinateXs_of_proper_marker {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hb : nd.node.border = -1 ∨ nd.node.border = 1) :
    run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  have hnproxy : nd.node.border ≠ -2 ∧ nd.node.border ≠ 2 := by
    rcases hb with h | h <;> constructor <;> intro hc <;> omega
  have hcp := coordinateProper_of_proper_nonsynthetic hrun hv hnproxy
  exact (componentRun_border_record hrun hcp hb).2

/-- Every final node has nonnegative placed width. -/
theorem proper_nodeW_nonneg {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} (hv : v < run.proper.nodes.length) :
    0 ≤ RouteImpl.nodeW run.proper v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hok := (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hsz, _, _, _⟩ := RouteImpl.layersOk_spec hok
  exact (hsz v hv).1

 /-- A layer looked up by its own index belongs to the layer list. -/

theorem layer_getD_mem {run : Run}
    {k : Nat} (hk : k < run.layers.length) :
    run.layers.getD k [] ∈ run.layers := by
  have hkk : run.layers[k]? = some run.layers[k] := List.getElem?_eq_getElem hk
  have heq : run.layers.getD k [] = run.layers[k] := by
    simp only [List.getD_eq_getElem?_getD, hkk, Option.getD_some]
  rw [heq]
  exact List.getElem_mem hk

 /-! ## Residuals, one pipeline phase step each -/

 /-- Residual (border-construction span): the anchor lookups backing the
 per-rank marker pairs, plus the member-rank coverage the fold needs.  The
 titled top/bottom pair is what `coordinateGraph_rank_pair` consumes
 (cf. `ForeignRankPairAnchors`); the two `toNat` bounds say the bracketing
 members lie inside the anchor span, which has no lemma for arbitrary
 borders.  Pinned to the three execution equations (`labeled` is bound
 inside by its coordinate equation). -/
def SideMarkerAnchorCover : Prop :=
   ∀ {P : Params} {inp : Input} {o : Options}
     {lines : List (List Measure.Line)} {graph : Graph},
     measuredGraph P inp o lines = .ok graph →
     lines.length = inp.boxes.length →
     WellFormed (inputModel inp o) →
     framedParents inp = true →
     ∀ {comp : List Nat}, comp ∈ components graph →
     ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
       {orderOptions : OrderOptions},
     componentRun P (componentCandidate graph comp candidate) labels
       orderOptions = .ok run →
     ∀ {decl : Nat} {low high : Nat} {lowNd highNd : ProperNode},
       run.proper.nodes[low]? = some lowNd →
       lowNd.node.clusterPath.contains decl = true →
       run.proper.nodes[high]? = some highNd →
       highNd.node.clusterPath.contains decl = true →
       ∃ (labeled : Proper),
         coordinateGraph P labeled = run.coordinateProper ∧
         (titleReservations (sizeProperPorts P labeled)).nodes.length =
           (titleReservations (sizeProperPorts P labeled)).rank.length ∧
         ∃ (top bottom : ProperNode × Nat),
           top ∈ (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx ∧
           top.1.node.border = -2 ∧
           top.1.node.clusterPath.getLast? = some decl ∧
           (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
             (fun entry => entry.1.node.border == 2 &&
               entry.1.node.clusterPath == top.1.node.clusterPath) =
               some bottom ∧
           (rk (titleReservations (sizeProperPorts P labeled)).rank top.2).toNat ≤
             (rk run.proper.rank low).toNat ∧
           (rk run.proper.rank high).toNat ≤
             (rk (titleReservations (sizeProperPorts P labeled)).rank
               bottom.2).toNat

 /-- Residual (border construction): two side markers of one declaration share
 the anchor's full cluster path.  This is the executed `addClusterBorders`
 emission content (the fold copies the anchor path onto each per-rank pair,
 cf. `addClusterBorders_side_source`); unfolding `borderStep` to the
 same-anchor conclusion has no lemma. -/
def SideMarkerSamePath : Prop :=
   ∀ {P : Params} {inp : Input} {o : Options}
     {lines : List (List Measure.Line)} {graph : Graph},
     measuredGraph P inp o lines = .ok graph →
     ∀ {comp : List Nat}, comp ∈ components graph →
     ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
       {orderOptions : OrderOptions},
     componentRun P (componentCandidate graph comp candidate) labels
       orderOptions = .ok run →
     ∀ {decl m m' : Nat} {marker marker' : ProperNode},
       run.coordinateProper.nodes[m]? = some marker →
       marker.node.border = -1 →
       marker.node.clusterPath.getLast? = some decl →
       run.coordinateProper.nodes[m']? = some marker' →
       marker'.node.border = 1 →
       marker'.node.clusterPath.getLast? = some decl →
       marker.node.clusterPath = marker'.node.clusterPath

 /-- Residual (coordinates): `nodePath` unfolds to the cluster path on
 border-`0` nodes of the executed coordinate graph.  For non-dummy nodes this
 is `nodePath_of_node`; for dummy nodes it is the `materializeDummyPaths`
 equation plus chain-endpoint stability, which has no lemma. -/
def PlainNodePathEq : Prop :=
   ∀ {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions},
     componentRun P cg labels orderOptions = .ok run →
     ∀ {v : Nat} {nd : ProperNode},
       run.coordinateProper.nodes[v]? = some nd →
       nd.node.border = 0 →
       OrderImpl.nodePath run.coordinateProper v = nd.node.clusterPath

 /-- An element strictly between two members of an infix `S` of a nodup list
 `l` is itself a member of `S` (copied from `BracketInsidePremisesProof`,
 whose copy is file-private). -/
 private theorem smf_mem_of_between_infix {α : Type} {l S : List α} {a b c : α}
     {li vi ri : Nat}
     (hnd : l.Nodup) (h : S.IsInfix l)
     (ha : a ∈ S) (hb : b ∈ S)
     (hli : l[li]? = some a) (hvi : l[vi]? = some c) (hri : l[ri]? = some b)
     (hlt : li < vi) (hgt : vi < ri) : c ∈ S := by
   obtain ⟨s, t, hs⟩ := h
   subst hs
   have hnd' := List.nodup_append.mp hnd
   have hsS : ∀ x ∈ s, ∀ y ∈ S, x ≠ y :=
     (List.nodup_append.mp hnd'.1).2.2
   have hSt : ∀ x ∈ s ++ S, ∀ y ∈ t, x ≠ y := hnd'.2.2
   have hlen : (s ++ S).length = s.length + S.length := List.length_append ..
   have hliS : s.length ≤ li ∧ li < (s ++ S).length := by
     constructor
     · by_cases hle : s.length ≤ li
       · exact hle
       · have hlt' : li < s.length := by omega
         have hlook : ((s ++ S) ++ t)[li]? = s[li]? := by
           rw [List.getElem?_append_left (by omega),
             List.getElem?_append_left hlt']
         rw [hlook] at hli
         exact (hsS a (List.mem_of_getElem? hli) a ha rfl).elim
     · by_cases hle : (s ++ S).length ≤ li
       · have hlook : ((s ++ S) ++ t)[li]? = t[li - (s ++ S).length]? :=
           List.getElem?_append_right hle
         rw [hlook] at hli
         exact (hSt a (List.mem_append_right s ha) a (List.mem_of_getElem? hli)
           rfl).elim
       · have hlt' : li < (s ++ S).length := by omega
         exact hlt'
   have hriS : s.length ≤ ri ∧ ri < (s ++ S).length := by
     constructor
     · by_cases hle : s.length ≤ ri
       · exact hle
       · have hlt' : ri < s.length := by omega
         have hlook : ((s ++ S) ++ t)[ri]? = s[ri]? := by
           rw [List.getElem?_append_left (by omega),
             List.getElem?_append_left hlt']
         rw [hlook] at hri
         exact (hsS b (List.mem_of_getElem? hri) b hb rfl).elim
     · by_cases hle : (s ++ S).length ≤ ri
       · have hlook : ((s ++ S) ++ t)[ri]? = t[ri - (s ++ S).length]? :=
           List.getElem?_append_right hle
         rw [hlook] at hri
         exact (hSt b (List.mem_append_right s hb) b (List.mem_of_getElem? hri)
           rfl).elim
       · have hlt' : ri < (s ++ S).length := by omega
         exact hlt'
   have hviS : s.length ≤ vi ∧ vi < (s ++ S).length := by
     constructor <;> omega
   have hlook : ((s ++ S) ++ t)[vi]? = S[vi - s.length]? := by
     rw [List.getElem?_append_left hviS.2,
       List.getElem?_append_right (by omega : s.length ≤ vi)]
   rw [hlook] at hvi
   exact List.mem_of_getElem? hvi

 /-- A prefix ending in `d` forces `d` into any list it prefixes (copied from
 `ForeignClusterFactsProof`, avoiding a cross-seam import). -/
 private theorem smf_prefix_last_mem_contains {pref l : List Nat} {d : Nat}
     (hpre : pref.isPrefixOf l = true) (hlast : pref.getLast? = some d) :
     l.contains d = true := by
   apply List.contains_iff_mem.mpr
   have hmem : d ∈ pref := List.mem_of_getLast? hlast
   have hprefix : pref <+: l := List.isPrefixOf_iff_prefix.mp hpre
   obtain ⟨t, rfl⟩ := hprefix
   exact List.mem_append.mpr (Or.inl hmem)

/-! ## The three side-marker facts -/

 /-- The bracketed rank carries the declaration's marker pair: the anchor
 cover supplies the titled pair and the member-rank bounds, the construction
 emits the pair at every covered rank (`coordinateGraph_rank_pair`), and the
 coordinate equation transports it to the executed run. -/
theorem bracketMarkersAtRank (hgrp : SideMarkerAnchorCover) : BracketMarkersAtRank := by
   intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run labels orderOptions
     hrun decl r low high lowNd highNd hlow hcontainLow hlerk hhigh hcontainHigh
     hhrer
   obtain ⟨labeled, hc, haligned, top, bottom, htop, hbordTop, hlastTop, hfindBot,
       hloBnd, hhiBnd⟩ :=
     hgrp hgraph hlines hwf hfp hcomp hrun hlow hcontainLow hhigh hcontainHigh
   obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
     coordinateGraph_rank_pair P labeled haligned htop hbordTop hfindBot (rank := r)
       (by omega) (by omega)
   rw [hc] at hleft hright hleftRank hrightRank
   refine ⟨left, right, _, _, hleft, rfl, hlastTop, ?_, hright, rfl, hlastTop, ?_⟩ <;>
     simp only [rk, List.getD_eq_getElem?_getD, hleftRank, hrightRank,
       Option.getD_some]

 /-- Same-side markers share one `x`-span (from the chain alignment), every
 marker right edge is nonnegative (nonnegative centres plus width), and the
 left marker lies left of the same-rank right marker: same-path markers are
 ordered by the executed border ends, lifted through pairwise separation. -/
theorem sideMarkerSpanAligned (halign : ForeignBorderChainXAligned)
     (hsame : SideMarkerSamePath) : SideMarkerSpanAligned := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions
    hrun decl m m' marker marker' hmem hborder hgetLast hmem' hborder'
    hgetLast'
  have hns : marker.node.border ≠ -2 ∧ marker.node.border ≠ 2 := by
    rcases hborder with h | h <;> constructor <;> intro hc <;> omega
  have hns' : marker'.node.border ≠ -2 ∧ marker'.node.border ≠ 2 := by
    rcases hborder' with h | h <;> constructor <;> intro hc <;> omega
  have hcp := coordinateProper_of_proper_nonsynthetic hrun hmem hns
  have hcp' := coordinateProper_of_proper_nonsynthetic hrun hmem' hns'
  have hrank := proper_rank_eq_coordinate hrun
  refine ⟨?_, ?_, ?_⟩
  · intro hsameSide
    have hlast : marker.node.clusterPath.getLast? =
        marker'.node.clusterPath.getLast? := by
      rw [hgetLast, hgetLast']
    exact halign hgraph hcomp hrun hcp hcp' hborder hborder' hsameSide hlast
  · have hxs := coordinateXs_of_proper_marker hrun hmem hborder
    have hcenter : 0 ≤ run.coordinateXs.getD m 0 :=
      fbs_coordinate_centers_nonneg hrun m
    have hw : 0 ≤ RouteImpl.nodeW run.proper m :=
      proper_nodeW_nonneg hrun (List.getElem?_eq_some_iff.mp hmem).1
    have hwEq : RouteImpl.nodeW run.proper m = marker.node.w := by
      simp only [RouteImpl.nodeW, hmem]
    have hw' : 0 ≤ marker.node.w := hwEq ▸ hw
    have e : ∀ width : Int, Int.fdiv width 2 = width / 2 :=
      fun width => Int.fdiv_eq_ediv_of_nonneg width (by decide)
    simp only [RouteImpl.leftOf, RouteImpl.xAt, e, hxs, hwEq]
    omega
  · intro hord
    obtain ⟨hbL, hbR, hrankEq⟩ := hord

    have hrkcp : rk run.coordinateProper.rank m =
        rk run.coordinateProper.rank m' := by
      rw [← hrank]
      exact hrankEq
    obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _, _,
      _⟩ := componentRun_spec hrun
    have hlay : OrderImpl.lay run.coordinateProper m =
        OrderImpl.lay run.coordinateProper m' := by
      simp only [OrderImpl.lay, hrkcp]
    obtain ⟨hltM, hmemM⟩ :=
      ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord
        horder hcp
    obtain ⟨_, hmemM'⟩ :=
      ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord
        horder hcp'
    have hlt : OrderImpl.lay run.coordinateProper m < run.layers.length := by
      rw [← hlayers]
      exact hltM
    have hlayer := layer_getD_mem (run := run) hlt
    have hmemL : m ∈ run.layers.getD (OrderImpl.lay run.coordinateProper m) [] := by
      rw [← hlayers]
      exact hmemM
    have hmemR : m' ∈ run.layers.getD (OrderImpl.lay run.coordinateProper m) [] := by
      rw [hlay, ← hlayers]
      exact hmemM'
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmemL
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemR
    have hpathEq := hsame hgraph hcomp hrun hcp hbL hgetLast hcp' hbR hgetLast'
    have hpre : marker.node.clusterPath <+: marker'.node.clusterPath := by
      rw [hpathEq]
      exact List.prefix_rfl
    have horder' : OrderImpl.order run.coordinateProper orderOptions =
        .ok run.layers := by
      simp [OrderImpl.order, horder, hlayers]
    have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
    have hdm : marker.dummy = false := by
      cases hd : marker.dummy with
      | false => rfl
      | true =>
        have h0 := hwf.2.2 m marker hcp hd
        omega
    have hdm' : marker'.dummy = false := by
      cases hd : marker'.dummy with
      | false => rfl
      | true =>
        have h0 := hwf.2.2 m' marker' hcp' hd
        omega
    have hne : m ≠ m' := by
      intro heq
      have hmm : marker = marker' :=
        Option.some.inj ((heq ▸ hcp).symm.trans hcp')
      rw [hmm] at hbL
      omega
    have hltij : i < j :=
       (OrderImpl.order_border_ends run.coordinateProper orderOptions run.layers
         horder' hwf (run.layers.getD (OrderImpl.lay run.coordinateProper m) []) hlayer
         i j m m' marker marker' hi hj hcp hcp' hne hdm hdm' hpre).1 hbL
    have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayer
      hltij hi hj hcp hcp'
      (by intro h; rcases h with h1 | h2 <;> omega)
      (by intro h; rcases h with h1 | h2 <;> omega)
    have hwL : 0 ≤ RouteImpl.nodeW run.proper m :=
      proper_nodeW_nonneg hrun (List.getElem?_eq_some_iff.mp hmem).1
    have hwR : 0 ≤ RouteImpl.nodeW run.proper m' :=
      proper_nodeW_nonneg hrun (List.getElem?_eq_some_iff.mp hmem').1
    exact ⟨by omega, by omega⟩

 /-- A plain node off the group lies beyond the marker pair: same-path markers
 bracket one contiguous block, the plain is outside it, and pairwise
 separation lifts the order to `x`-spans. -/
theorem plainClearOfSideMarker (hsame : SideMarkerSamePath)
     (hpath : PlainNodePathEq) : PlainClearOfSideMarker := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions
    hrun decl v mL mR plain nL nR hmemV hborderV hnotmem hmemL hborderL hgetL
    hmemR hborderR hgetR hrankL hrankR
  have hnsV : plain.node.border ≠ -2 ∧ plain.node.border ≠ 2 := by
    constructor <;> intro hc <;> omega
  have hnsL : nL.node.border ≠ -2 ∧ nL.node.border ≠ 2 := by
    constructor <;> intro hc <;> omega
  have hnsR : nR.node.border ≠ -2 ∧ nR.node.border ≠ 2 := by
    constructor <;> intro hc <;> omega
  have hcpV := coordinateProper_of_proper_nonsynthetic hrun hmemV hnsV
  have hcpL := coordinateProper_of_proper_nonsynthetic hrun hmemL hnsL
  have hcpR := coordinateProper_of_proper_nonsynthetic hrun hmemR hnsR
  have hrank := proper_rank_eq_coordinate hrun
  have hrkL : rk run.coordinateProper.rank mL = rk run.coordinateProper.rank v := by
    rw [← hrank]
    exact hrankL
  have hrkR : rk run.coordinateProper.rank mR = rk run.coordinateProper.rank v := by
    rw [← hrank]
    exact hrankR
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _, _,
    _⟩ := componentRun_spec hrun
  have hlayL : OrderImpl.lay run.coordinateProper mL =
      OrderImpl.lay run.coordinateProper v := by
    simp only [OrderImpl.lay, hrkL]
  have hlayR : OrderImpl.lay run.coordinateProper mR =
      OrderImpl.lay run.coordinateProper v := by
    simp only [OrderImpl.lay, hrkR]
  obtain ⟨hltV, hmemVV⟩ :=
    ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord horder
      hcpV
  obtain ⟨_, hmemLL⟩ :=
    ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord horder
      hcpL
  obtain ⟨_, hmemRR⟩ :=
    ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord horder
      hcpR
  have hlt : OrderImpl.lay run.coordinateProper v < run.layers.length := by
    rw [← hlayers]
    exact hltV
  have hlayer := layer_getD_mem (run := run) hlt
  have hLL : mL ∈ run.layers.getD (OrderImpl.lay run.coordinateProper v) [] := by
    rw [← hlayL, ← hlayers]
    exact hmemLL
  have hVV : v ∈ run.layers.getD (OrderImpl.lay run.coordinateProper v) [] := by
    rw [← hlayers]
    exact hmemVV
  have hRR : mR ∈ run.layers.getD (OrderImpl.lay run.coordinateProper v) [] := by
    rw [← hlayR, ← hlayers]
    exact hmemRR
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hLL
  obtain ⟨iv, hiv⟩ := List.mem_iff_getElem?.mp hVV
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hRR
  have hpathEq := hsame hgraph hcomp hrun hcpL hborderL hgetL hcpR hborderR hgetR
  have horder' : OrderImpl.order run.coordinateProper orderOptions =
      .ok run.layers := by
    simp [OrderImpl.order, horder, hlayers]
  have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  have hdmL : nL.dummy = false := by
    cases hd : nL.dummy with
    | false => rfl
    | true =>
      have h0 := hwf.2.2 mL nL hcpL hd
      omega
  have hdmR : nR.dummy = false := by
    cases hd : nR.dummy with
    | false => rfl
    | true =>
      have h0 := hwf.2.2 mR nR hcpR hd
      omega
  have hnpL : OrderImpl.nodePath run.coordinateProper mL =
      nL.node.clusterPath :=
    OrderImpl.nodePath_of_nondummy hcpL hdmL
  have hnpR : OrderImpl.nodePath run.coordinateProper mR =
      nR.node.clusterPath :=
    OrderImpl.nodePath_of_nondummy hcpR hdmR
  have hnpV : OrderImpl.nodePath run.coordinateProper v =
      plain.node.clusterPath :=
    hpath hrun hcpV hborderV
  have hSinfix : ((run.layers.getD (OrderImpl.lay run.coordinateProper v) []).filter (fun x => nL.node.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper x))).IsInfix (run.layers.getD (OrderImpl.lay run.coordinateProper v) []) :=
    OrderImpl.order_clusters_contiguous run.coordinateProper orderOptions
      run.layers horder' (run.layers.getD (OrderImpl.lay run.coordinateProper v) []) hlayer
      nL.node.clusterPath
  have hmLS : mL ∈ (run.layers.getD (OrderImpl.lay run.coordinateProper v) []).filter (fun x => nL.node.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper x)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_of_getElem? hi, ?_⟩
    rw [hnpL]
    exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hmRS : mR ∈ (run.layers.getD (OrderImpl.lay run.coordinateProper v) []).filter (fun x => nL.node.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper x)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_of_getElem? hj, ?_⟩
    rw [hnpR, ← hpathEq]
    exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hlayerO : (run.layers.getD (OrderImpl.lay run.coordinateProper v) []) ∈ ord.layers := by rw [hlayers]; exact hlayer
  have hspec : OrderImpl.Layering run.coordinateProper ord.layers :=
    (OrderImpl.orderWithBudget_spec run.coordinateProper orderOptions ord horder).1
  have hndlayer : (run.layers.getD (OrderImpl.lay run.coordinateProper v) []).Nodup :=
    OrderImpl.layering_mem_nodup hspec hlayerO
  rcases Nat.lt_trichotomy iv i with h | h | h
  · exact Or.inl (componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
      hlayer h hiv hi hcpV hcpL
      (by intro h; rcases h with h1 | h2 <;> omega)
      (by intro h; rcases h with h1 | h2 <;> omega))
  · subst h
    have hvv : v = mL := Option.some.inj (hiv.symm.trans hi)
    rw [hvv] at hcpV
    have hpn : plain = nL := Option.some.inj (hcpV.symm.trans hcpL)
    have hF : False := by rw [hpn] at hborderV; omega
    exact False.elim hF
  · rcases Nat.lt_trichotomy j iv with h2 | h2 | h2
    · exact Or.inr (componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
        hlayer h2 hj hiv hcpR hcpV
        (by intro h; rcases h with h1 | h2 <;> omega)
        (by intro h; rcases h with h1 | h2 <;> omega))
    · subst h2
      have hvv : v = mR := Option.some.inj (hiv.symm.trans hj)
      rw [hvv] at hcpV
      have hpn : plain = nR := Option.some.inj (hcpV.symm.trans hcpR)
      have hF : False := by rw [hpn] at hborderV; omega
      exact False.elim hF
    · have hvinS : v ∈ (run.layers.getD (OrderImpl.lay run.coordinateProper v) []).filter (fun x => nL.node.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper x)) :=
      smf_mem_of_between_infix hndlayer hSinfix hmLS hmRS hi hiv hj h h2
      rw [List.mem_filter] at hvinS
      obtain ⟨_, hpreV⟩ := hvinS
      rw [hnpV] at hpreV
      have hcon : plain.node.clusterPath.contains decl = true :=
        smf_prefix_last_mem_contains hpreV hgetL
      rw [hcon] at hnotmem
      cases hnotmem


end Elegant.Layered.PipelineImpl

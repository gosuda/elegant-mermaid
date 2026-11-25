import Elegant.Layered.ExactForeignNonGroupSpansProof
import Elegant.Layered.ExactC8aTopLookupDummyProof
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.SideMarkerFactsProof
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.Order

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact side-marker facts: bracket, plain, side over `componentRunX`

Leaf defs `XN_BracketMarkersAtRank` (`c8aBracket`), `XN_PlainClearOfSideMarker`
(`c8aPlain`), `XN_SideMarkerSpanAligned` (`c8aSide`) from
`ExactForeignNonGroupSpansProof.lean`, proved by replaying the plain
`SideMarkerFactsProof` / `SideMarkerPathsProof` chain over `componentRunX`.

Probe evidence: `proofs/wip/Probe/ExactC8aSpansTProbe.lean` evaluates the
bracket span pairs, layer order, and anchor existence on seven executed
`componentRunX` runs with zero violations on framed inputs;
`proofs/wip/Probe/BorderMarkerProbe.lean` checkers B (plain) and C (side) run
the same `x`-interval logic on executed runs. A new probe
`proofs/wip/Probe/ExactC8aMarkersTProbe.lean` (this task) replays checkers A/B/C
over `componentRunX` on six inputs (sibling groups, nested groups, self-loop,
empty group, zero-size fixed box with `exactIds ["G1"]`, ill-formed input):
plain `P` and side `S` show zero violations on all executed runs
(`P=18/0`, `S=642/0`); bracket `B` shows zero violations on all framed inputs
and three hits only on the unframed zero-size input (`framedParents = false`,
so the `XN_BracketMarkersAtRank` premises are vacuous there). No falsifying
witness under the stated premises was found, so the replay proceeds. -/

/-- File-unique prefix for all private helpers in this module. -/
private theorem xsmf_side_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some node)
    (hdummy : node.dummy = false)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    (coordinateGraphX P exact source).nodes[index]? = some node := by
  have hnotProxy :
      (node.node.border == -2 || node.node.border == 2) = false := by
    rcases hborder with h | h <;> rw [h] <;> decide
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some node := by
    simp only [clearProxyExtents, List.getElem?_map, hnode, Option.map_some]
    simp only [hnotProxy, Bool.false_eq_true, ↓reduceIte]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some,
    Nat.zero_add, hdummy, Bool.false_eq_true, ↓reduceIte]

/-- Exact rank pair with file-unique prefix (copy of `XSc8a_rank_pair`). -/
private theorem xsmf_rank_pair (P : Params) (exact : List Nat) (source : Proper)
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤ rank)
    (hhi : rank ≤ (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat) :
    ∃ left right : Nat,
      (coordinateGraphX P exact source).nodes[left]? =
        some ⟨{ decl := top.1.node.decl, w := P.clusterBorderW, h := 0, clusterPath := top.1.node.clusterPath, border := -1 }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).nodes[right]? =
        some ⟨{ decl := top.1.node.decl, w := P.clusterBorderW, h := 0, clusterPath := top.1.node.clusterPath, border := 1, loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).rank[left]? = some (rank : Int) ∧
      (coordinateGraphX P exact source).rank[right]? = some (rank : Int) := by
  obtain ⟨left, right, hl, hr, hrl, hrr⟩ :=
    addClusterBorders_rank_pair (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW haligned htop hborder hbottom hlo hhi
  refine ⟨left, right, xsmf_side_record hl rfl (Or.inl rfl), xsmf_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr

/-- Bracket markers at rank over exact runs: closed, via the closed anchor
cover (`XSc8a_anchorCover_closed'`) and the rank-pair emission. -/
theorem XN_bracketMarkersAtRank_holds (exactIds : List String) :
    XN_BracketMarkersAtRank exactIds := by
  intro P inp o lines measured graph0 graph h0 h hlines hwf hfp comp hcomp candidate run labels orderOptions hrun decl r low high lowNd highNd hlow hcontainLow hlerk hhigh hcontainHigh hhrer
  obtain ⟨labeled, hc, haligned, top, bottom, htop, hbordTop, hlastTop, hfindBot, hloBnd, hhiBnd⟩ :=
    XSc8a_anchorCover_closed' exactIds h0 h hlines hwf hfp hcomp hrun hlow hcontainLow hhigh hcontainHigh
  have hlo : (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat ≤ r :=
    Nat.le_trans hloBnd hlerk
  have hhi : r ≤ (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bottom.2).toNat :=
    Nat.le_trans hhrer hhiBnd
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    xsmf_rank_pair P (exactDecls exactIds inp) labeled haligned htop hbordTop hfindBot hlo hhi
  rw [hc] at hleft hright hleftRank hrightRank
  refine ⟨left, right, _, _, hleft, rfl, hlastTop, ?_, hright, rfl, hlastTop, ?_⟩ <;>
    simp only [rk, List.getD_eq_getElem?_getD, hleftRank, hrightRank, Option.getD_some]
/-- A non-proxy record of the exact final run is the same coordinate record
(copy of `coordinateProper_of_proper_nonsynthetic` over `componentRunX_spec`). -/
private theorem xsmf_proper_nonsynthetic {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hb : nd.node.border ≠ -2 ∧ nd.node.border ≠ 2) :
    run.coordinateProper.nodes[v]? = some nd := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
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
/-- The final rank assignment is the coordinate rank assignment over exact runs. -/
private theorem xsmf_rank_eq {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
    run.proper.rank = run.coordinateProper.rank := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  rw [← hdrop, OrderImpl.dropSynthetic_rank]
  exact hrankEq
/-- Exact border-marker records transfer with cross centres (copy of
`XSc8a_border_record` with file-unique prefix). -/
private theorem xsmf_border_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- An exact side marker keeps its cross-coordinate centre through proxy widths. -/
private theorem xsmf_xs_marker {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hb : nd.node.border = -1 ∨ nd.node.border = 1) :
    run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  have hnproxy : nd.node.border ≠ -2 ∧ nd.node.border ≠ 2 := by
    rcases hb with h | h <;> constructor <;> intro hc <;> omega
  have hcp := xsmf_proper_nonsynthetic hrun hv hnproxy
  exact (xsmf_border_record hrun hcp hb).2
/-- Every exact final node has nonnegative placed width. -/
private theorem xsmf_nodeW_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hv : v < run.proper.nodes.length) :
    0 ≤ RouteImpl.nodeW run.proper v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _⟩ := componentRunX_spec hrun
  have hok := (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hsz, _, _, _⟩ := RouteImpl.layersOk_spec hok
  exact (hsz v hv).1
/-- Exact coordinate borders are well formed via the public exact bundle. -/
private theorem xsmf_bordersWellFormed {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  obtain ⟨_, labeled, _, hc, _, hready, _, _, _⟩ := X_cg_run_bundle h0 h hcomp hrun
  rw [← hc]
  unfold coordinateGraphX
  apply materializeDummyPaths_bordersWellFormed
  apply clearProxyExtents_bordersWellFormed
  exact OrderImpl.addClusterBorders_bordersWellFormed _ _ hready
/-- Every exact cross-coordinate centre is nonnegative (copy of
`XSc8a_centers_nonneg` with file-unique prefix). -/
private theorem xsmf_centers_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
    ∀ v : Nat, 0 ≤ run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨-, -, -, -, hcase⟩ := crossCoordsClusterWith_spec hcross
  rcases hcase with ⟨-, hxs⟩ | ⟨x0, x1, x2, x3, hpass, hxs⟩
  · rw [hxs]
    intro v
    simp
  · rw [hxs]
    unfold CoordsImpl.crossClusterPasses at hpass
    split at hpass
    · simp at hpass
    · next _ _ =>
      split at hpass
      · simp at hpass
      · dsimp only at hpass
        split at hpass
        · simp at hpass
        · next y0 h0 =>
          split at hpass
          · simp at hpass
          · next y1 h1 =>
            split at hpass
            · simp at hpass
            · next y2 h2 =>
              split at hpass
              · simp at hpass
              · next y3 h3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hpass
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hpass
                have hsz0 : y0.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h0).1
                have hsz1 : y1.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h1).1
                have hsz2 : y2.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h2).1
                have hsz3 : y3.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h3).1
                have hnn0 := (fbs_cluster_pass_nonneg h0).2
                have hnn1 := (fbs_cluster_pass_nonneg h1).2
                have hnn2 := (fbs_cluster_pass_nonneg h2).2
                have hnn3 := (fbs_cluster_pass_nonneg h3).2
                obtain ⟨o0, o1, o2, o3⟩ := fbs_balanceOffsets_nonneg y0 y1 y2 y3
                intro v
                by_cases hv : v < run.coordinateProper.nodes.length
                · rw [CoordsImpl.balanceValues_getD _ _ _ _ _ hv]
                  exact fbs_bal4_nonneg (by have := hnn0 v (by omega); omega)
                    (by have := hnn1 v (by omega); omega)
                    (by have := hnn2 v (by omega); omega)
                    (by have := hnn3 v (by omega); omega)
                · have hlen : (CoordsImpl.balanceValues run.coordinateProper.nodes.length y0 y1
                        y2 y3).length = run.coordinateProper.nodes.length := by
                    simp [CoordsImpl.balanceValues]
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
                  exact Int.le_refl 0
/-- Canonical cluster path of an executed exact side marker (copy of
`XSc8a_sideCanon` with file-unique prefix). -/
private theorem xsmf_sideCanon {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {a : Nat} {na : ProperNode} {decl : Nat}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hside : na.node.border = -1 ∨ na.node.border = 1)
    (hlast : na.node.clusterPath.getLast? = some decl) :
    ∃ box : ModelBox,
      inp.boxes[decl]? = some box ∧
      na.node.clusterPath = Compound.path inp.boxes box ++ [decl] := by
  obtain ⟨_, labeled, _, hc, hk, hready, _, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hcoordinate : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[a]? =
      some na := by
    rw [hc]; exact hna
  have horiginal := X_side_original hready hcoordinate hside
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal) hside
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp htop
  have hget : (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hbord : top.1.node.border = -2 := by simpa using hcond
  rcases X_titled_node_origin hk hget with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hbord
    rcases hk top.2 orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨boxG, hboxG, hpathG⟩ := X_cg_group_box h0 h hbn hbnB
      have hlastG : bn.clusterPath.getLast? = some bn.decl := by
        rw [hpathG, List.getLast?_append]; simp
      have hnaLast : na.node.clusterPath.getLast? = some bn.decl := by
        rw [hpath, hpp, hnp]; exact hlastG
      have hdeclEq : bn.decl = decl :=
        Option.some.inj (hnaLast.symm.trans hlast)
      rw [hdeclEq] at hboxG
      refine ⟨boxG, hboxG, ?_⟩
      rw [hpath, hpp, hnp, hpathG, hdeclEq]
    · rw [hb0] at horigB; omega
  · rw [hb3] at hbord; omega
/-- Two exact side markers of one declaration share the anchor path (proved
outright; used by both plain and side mains). -/
private theorem xsmf_samePath_of {exactIds : List String} :
    ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl m m' : Nat} {marker marker' : ProperNode},
      run.coordinateProper.nodes[m]? = some marker →
      marker.node.border = -1 →
      marker.node.clusterPath.getLast? = some decl →
      run.coordinateProper.nodes[m']? = some marker' →
      marker'.node.border = 1 →
      marker'.node.clusterPath.getLast? = some decl →
      marker.node.clusterPath = marker'.node.clusterPath := by
  intro P inp o lines measured graph0 graph h0 h comp hcomp candidate run labels
    orderOptions hrun decl m m' marker marker' hmem hborder hgetLast hmem'
    hborder' hgetLast'
  obtain ⟨boxL, hboxL, hpathL⟩ :=
    xsmf_sideCanon h0 h hcomp hrun hmem (Or.inl hborder) hgetLast
  obtain ⟨boxR, hboxR, hpathR⟩ :=
    xsmf_sideCanon h0 h hcomp hrun hmem' (Or.inr hborder') hgetLast'
  have hbox : boxL = boxR := Option.some.inj (hboxL.symm.trans hboxR)
  rw [hpathL, hpathR, hbox]
/-- An element strictly between two members of an infix `S` of a nodup list
is itself a member of `S` (copy of `smf_mem_of_between_infix`). -/
private theorem xsmf_mem_of_between_infix {α : Type} {l S : List α} {a b c : α}
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
/-- A prefix ending in `d` forces `d` into any list it prefixes. -/
private theorem xsmf_prefix_last_mem {pref l : List Nat} {d : Nat}
    (hpre : pref.isPrefixOf l = true) (hlast : pref.getLast? = some d) :
    l.contains d = true := by
  apply List.contains_iff_mem.mpr
  have hmem : d ∈ pref := List.mem_of_getLast? hlast
  have hprefix : pref <+: l := List.isPrefixOf_iff_prefix.mp hpre
  obtain ⟨t, rfl⟩ := hprefix
  exact List.mem_append.mpr (Or.inl hmem)
/-- Narrower path residual for the plain fact: `nodePath` unfolds to the
cluster path on border-`0` coordinate nodes of an exact run. Strictly narrower
than `XN_PlainClearOfSideMarker` (paths only, no `xs` intervals); the companion
same-path fact is proved privately in this file (`xsmf_samePath_of`). -/
def XN_PlainNodePathResidual (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v : Nat} {nd : ProperNode},
      run.coordinateProper.nodes[v]? = some nd →
      nd.node.border = 0 →
      OrderImpl.nodePath run.coordinateProper v = nd.node.clusterPath
/-- A plain node off the group lies beyond the marker pair over exact runs,
from the path residual plus the proved same-path fact. -/
theorem XN_plainClearOfSideMarker_of_path (exactIds : List String)
    (hpath : XN_PlainNodePathResidual exactIds) :
    XN_PlainClearOfSideMarker exactIds := by
  intro P inp o lines measured graph0 graph h0 hg comp hcomp candidate run labels
    orderOptions hrun decl v mL mR plain nL nR hmemV hborderV hnotmem hmemL
    hborderL hgetL hmemR hborderR hgetR hrankL hrankR
  have hnsV : plain.node.border ≠ -2 ∧ plain.node.border ≠ 2 := by
    constructor <;> intro hc <;> omega
  have hnsL : nL.node.border ≠ -2 ∧ nL.node.border ≠ 2 := by
    constructor <;> intro hc <;> omega
  have hnsR : nR.node.border ≠ -2 ∧ nR.node.border ≠ 2 := by
    constructor <;> intro hc <;> omega
  have hcpV := xsmf_proper_nonsynthetic hrun hmemV hnsV
  have hcpL := xsmf_proper_nonsynthetic hrun hmemL hnsL
  have hcpR := xsmf_proper_nonsynthetic hrun hmemR hnsR
  have hrank := xsmf_rank_eq hrun
  have hrkL : rk run.coordinateProper.rank mL = rk run.coordinateProper.rank v := by
    rw [← hrank]; exact hrankL
  have hrkR : rk run.coordinateProper.rank mR = rk run.coordinateProper.rank v := by
    rw [← hrank]; exact hrankR
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hlayL : OrderImpl.lay run.coordinateProper mL =
      OrderImpl.lay run.coordinateProper v := by
    simp only [OrderImpl.lay, hrkL]
  have hlayR : OrderImpl.lay run.coordinateProper mR =
      OrderImpl.lay run.coordinateProper v := by
    simp only [OrderImpl.lay, hrkR]
  obtain ⟨hltV, hmemVV⟩ :=
    ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord horder hcpV
  obtain ⟨_, hmemLL⟩ :=
    ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord horder hcpL
  obtain ⟨_, hmemRR⟩ :=
    ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord horder hcpR
  have hlt : OrderImpl.lay run.coordinateProper v < run.layers.length := by
    rw [← hlayers]; exact hltV
  have hlayer := layer_getD_mem (run := run) hlt
  have hLL : mL ∈ run.layers.getD (OrderImpl.lay run.coordinateProper v) [] := by
    rw [← hlayL, ← hlayers]; exact hmemLL
  have hVV : v ∈ run.layers.getD (OrderImpl.lay run.coordinateProper v) [] := by
    rw [← hlayers]; exact hmemVV
  have hRR : mR ∈ run.layers.getD (OrderImpl.lay run.coordinateProper v) [] := by
    rw [← hlayR, ← hlayers]; exact hmemRR
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hLL
  obtain ⟨iv, hiv⟩ := List.mem_iff_getElem?.mp hVV
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hRR
  have hpathEq := xsmf_samePath_of h0 hg hcomp hrun hcpL hborderL hgetL hcpR
    hborderR hgetR
  have horder' : OrderImpl.order run.coordinateProper orderOptions =
      .ok run.layers := by
    simp [OrderImpl.order, horder, hlayers]
  have hwf := xsmf_bordersWellFormed h0 hg hcomp hrun
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
    hpath h0 hg hcomp hrun hcpV hborderV
  have hSinfix : ((run.layers.getD (OrderImpl.lay run.coordinateProper v) []).filter
      (fun x => nL.node.clusterPath.isPrefixOf
        (OrderImpl.nodePath run.coordinateProper x))).IsInfix
      (run.layers.getD (OrderImpl.lay run.coordinateProper v) []) :=
    OrderImpl.order_clusters_contiguous run.coordinateProper orderOptions
      run.layers horder' (run.layers.getD (OrderImpl.lay run.coordinateProper v) [])
      hlayer nL.node.clusterPath
  have hmLS : mL ∈ (run.layers.getD (OrderImpl.lay run.coordinateProper v) []).filter
      (fun x => nL.node.clusterPath.isPrefixOf
        (OrderImpl.nodePath run.coordinateProper x)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_of_getElem? hi, ?_⟩
    rw [hnpL]
    exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hmRS : mR ∈ (run.layers.getD (OrderImpl.lay run.coordinateProper v) []).filter
      (fun x => nL.node.clusterPath.isPrefixOf
        (OrderImpl.nodePath run.coordinateProper x)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_of_getElem? hj, ?_⟩
    rw [hnpR, ← hpathEq]
    exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hlayerO : (run.layers.getD (OrderImpl.lay run.coordinateProper v) []) ∈
      ord.layers := by rw [hlayers]; exact hlayer
  have hspec : OrderImpl.Layering run.coordinateProper ord.layers :=
    (OrderImpl.orderWithBudget_spec run.coordinateProper orderOptions ord horder).1
  have hndlayer : (run.layers.getD (OrderImpl.lay run.coordinateProper v) []).Nodup :=
    OrderImpl.layering_mem_nodup hspec hlayerO
  rcases Nat.lt_trichotomy iv i with h | h | h
  · exact Or.inl (XB_orderedIntervals_holds exactIds h0 hg hcomp hrun hlayer
      h hiv hi hcpV hcpL
      (by intro h; rcases h with h1 | h2 <;> omega)
      (by intro h; rcases h with h1 | h2 <;> omega))
  · subst h
    have hvv : v = mL := Option.some.inj (hiv.symm.trans hi)
    rw [hvv] at hcpV
    have hpn : plain = nL := Option.some.inj (hcpV.symm.trans hcpL)
    have hF : False := by rw [hpn] at hborderV; omega
    exact False.elim hF
  · rcases Nat.lt_trichotomy j iv with h2 | h2 | h2
    · exact Or.inr (XB_orderedIntervals_holds exactIds h0 hg hcomp hrun hlayer
        h2 hj hiv hcpR hcpV
        (by intro h; rcases h with h1 | h2 <;> omega)
        (by intro h; rcases h with h1 | h2 <;> omega))
    · subst h2
      have hvv : v = mR := Option.some.inj (hiv.symm.trans hj)
      rw [hvv] at hcpV
      have hpn : plain = nR := Option.some.inj (hcpV.symm.trans hcpR)
      have hF : False := by rw [hpn] at hborderV; omega
      exact False.elim hF
    · have hvinS : v ∈ (run.layers.getD (OrderImpl.lay run.coordinateProper v) []).filter
          (fun x => nL.node.clusterPath.isPrefixOf
            (OrderImpl.nodePath run.coordinateProper x)) :=
        xsmf_mem_of_between_infix hndlayer hSinfix hmLS hmRS hi hiv hj h h2
      rw [List.mem_filter] at hvinS
      obtain ⟨_, hpreV⟩ := hvinS
      rw [hnpV] at hpreV
      have hcon : plain.node.clusterPath.contains decl = true :=
        xsmf_prefix_last_mem hpreV hgetL
      rw [hcon] at hnotmem
      cases hnotmem

/-- Same-side markers share one `x`-span with nonnegative right edge, and a
left marker lies left of the same-rank right marker over exact runs, from the
chain residual plus the proved same-path fact. -/
theorem XN_sideMarkerSpanAligned_of_chain (exactIds : List String)
    (hchain : X_ForeignBorderChainXAligned exactIds) :
    XN_SideMarkerSpanAligned exactIds := by
  intro P inp o lines measured graph0 graph h0 hg hlines hmodelWf hfp comp hcomp
    candidate run labels orderOptions hrun decl m m' marker marker' hmem
    hborder hgetLast hmem' hborder' hgetLast'
  have hns : marker.node.border ≠ -2 ∧ marker.node.border ≠ 2 := by
    rcases hborder with h | h <;> constructor <;> intro hc <;> omega
  have hns' : marker'.node.border ≠ -2 ∧ marker'.node.border ≠ 2 := by
    rcases hborder' with h | h <;> constructor <;> intro hc <;> omega
  have hcp := xsmf_proper_nonsynthetic hrun hmem hns
  have hcp' := xsmf_proper_nonsynthetic hrun hmem' hns'
  have hrank := xsmf_rank_eq hrun
  refine ⟨?_, ?_, ?_⟩
  · intro hsameSide
    have hlast : marker.node.clusterPath.getLast? =
        marker'.node.clusterPath.getLast? := by
      rw [hgetLast, hgetLast']
    exact hchain h0 hg hlines hmodelWf hfp hcomp hrun hcp hcp' hborder hborder'
      hsameSide hlast
  · have hxs := xsmf_xs_marker hrun hmem hborder
    have hcenter : 0 ≤ run.coordinateXs.getD m 0 :=
      xsmf_centers_nonneg hrun m
    have hw : 0 ≤ RouteImpl.nodeW run.proper m :=
      xsmf_nodeW_nonneg hrun (List.getElem?_eq_some_iff.mp hmem).1
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
    obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
      componentRunX_spec hrun
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
    have hpathEq := xsmf_samePath_of h0 hg hcomp hrun hcp hbL hgetLast hcp' hbR
      hgetLast'
    have hpre : marker.node.clusterPath <+: marker'.node.clusterPath := by
      rw [hpathEq]
      exact List.prefix_rfl
    have horder' : OrderImpl.order run.coordinateProper orderOptions =
        .ok run.layers := by
      simp [OrderImpl.order, horder, hlayers]
    have hwf := xsmf_bordersWellFormed h0 hg hcomp hrun
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
    have hsep := XB_orderedIntervals_holds exactIds h0 hg hcomp hrun hlayer
      hltij hi hj hcp hcp'
      (by intro h; rcases h with h1 | h2 <;> omega)
      (by intro h; rcases h with h1 | h2 <;> omega)
    have hwL : 0 ≤ RouteImpl.nodeW run.proper m :=
      xsmf_nodeW_nonneg hrun (List.getElem?_eq_some_iff.mp hmem).1
    have hwR : 0 ≤ RouteImpl.nodeW run.proper m' :=
      xsmf_nodeW_nonneg hrun (List.getElem?_eq_some_iff.mp hmem').1
    exact ⟨by omega, by omega⟩
end PipelineImpl
end Layered
end Elegant

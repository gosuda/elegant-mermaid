import Elegant.Layered.TitleCopySpanFacts
import Elegant.Layered.BottomSeamsRank
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.BracketInsidePremisesProof
import Elegant.Layered.BracketInsideStructuralFacts
import Elegant.Layered.BottomSeamsStructural
import Elegant.Layered.BottomClearanceNesting
import Elegant.Layered.CoordGraph
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.PipelineFacts
import Elegant.Layered.BottomClearanceExistence
import Elegant.Layered.GroupTopRankResidualsProof
import Elegant.Layered.BottomNestedRankProof
import Elegant.Layered.RouteProxyStart

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Title-copy span premise of the bracket seam

`titleCopySpanClearStrict` (`BottomClearanceInside.lean`) asks that a border-`3`
title copy sharing a bottom proxy's rank keep its x-span disjoint from the
proxy span. The proof splits on the copy's cluster path:

* equal paths (the copy's anchor sits in the proxy's own group): the copy's
  rank entry is its anchor's rank (`coordinateGraph_title_rank_source`), and
  `componentRun_group_top_lt_bottom` lifts the anchor strictly below the
  group's bottom proxy, so the shared-rank hypothesis is impossible;
* strict extension (the anchor is nested below the proxy's group): this needs
  the iterated `componentRun_nested_bottom_lt_outer_bottom` chain along the
  declaration path. That chain is kept as the residual
  `TitleCopyNestedStrictPrefix` below: it is true for executed layouts, it is
  strictly simpler than the goal (stronger path hypothesis), and every
  variable it constrains is pinned by `measuredGraph` or the executed run.
-/

/-- Residual: a border-`3` copy whose path strictly extends a bottom proxy's
path cannot share the proxy's rank. True for executed layouts by iterating
`componentRun_nested_bottom_lt_outer_bottom` from the proxy's group down to
the copy's anchor (whose rank entry the copy inherits): each step pushes the
child bottom strictly below the parent bottom, and `componentRun_group_top_lt_bottom`
lifts the anchor strictly below its own bottom. Every variable is pinned by
the `measuredGraph` equation and the executed `componentRun`. -/
def TitleCopyNestedStrictPrefix (P : Params) (graph : Graph) : Prop :=
  ∀ {inp : Input} {o : Options} {lines : List (List Measure.Line)},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
    ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
    ∀ t v : Nat,
      (run.coordinateProper.nodes.getD t default).dummy = false →
      (run.coordinateProper.nodes.getD t default).node.border = 2 →
      (run.coordinateProper.nodes.getD v default).node.border = 3 →
      (run.coordinateProper.nodes.getD t default).node.clusterPath <+:
        (run.coordinateProper.nodes.getD v default).node.clusterPath →
      (run.coordinateProper.nodes.getD v default).node.clusterPath ≠
        (run.coordinateProper.nodes.getD t default).node.clusterPath →
      rk run.coordinateProper.rank v ≠ rk run.coordinateProper.rank t

/-- Equal-path case: a title copy whose path equals a bottom proxy's path
cannot share the proxy's rank. The copy inherits its anchor's rank, the
anchor is a `-2` node with the proxy's path hence its declaration, and the
anchor ranks strictly below the proxy's bottom marker. -/
theorem titleCopyNestedRank_equal {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {t v : Nat}
    (htdummy : (run.coordinateProper.nodes.getD t default).dummy = false)
    (htborder : (run.coordinateProper.nodes.getD t default).node.border = 2)
    (hvborder : (run.coordinateProper.nodes.getD v default).node.border = 3)
    (hpath : (run.coordinateProper.nodes.getD v default).node.clusterPath =
      (run.coordinateProper.nodes.getD t default).node.clusterPath) :
    rk run.coordinateProper.rank v ≠ rk run.coordinateProper.rank t := by
  obtain ⟨rr, normalized, labeled, hrr, hn, hl, hcoord, _⟩ :=
    componentRun_ranked_source hrun
  have hk : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩ := by
    intro index node hnode
    exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  have hranks : ∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
      labeled.rank[index]? = some rank := by
    intro index rank hrank
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hrank
  cases hvt : run.coordinateProper.nodes[t]? with
  | none =>
      rw [List.getD_eq_getElem?_getD, hvt, Option.getD_none] at htborder
      have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
      omega
  | some ndT =>
      have htD : run.coordinateProper.nodes.getD t default = ndT := by
        simp only [List.getD_eq_getElem?_getD, hvt, Option.getD_some]
      rw [htD] at htdummy htborder hpath
      cases hvv : run.coordinateProper.nodes[v]? with
      | none =>
          rw [List.getD_eq_getElem?_getD, hvv, Option.getD_none] at hvborder
          have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
          omega
      | some ndV =>
          have hvD : run.coordinateProper.nodes.getD v default = ndV := by
            simp only [List.getD_eq_getElem?_getD, hvv, Option.getD_some]
          rw [hvD] at hvborder hpath
          have hvC : (coordinateGraph P labeled).nodes[v]? = some ndV := by
            rw [hcoord]; exact hvv
          obtain ⟨origIdx, orig, hOrigLook, hOrigBorder, hOrigReal, _,
              hTitlePath, hRankEq⟩ :=
            coordinateGraph_title_rank_source hk hshape haligned hvC hvborder
          have htC : (coordinateGraph P labeled).nodes[t]? = some ndT := by
            rw [hcoord]; exact hvt
          rcases coordinateGraph_lookup P labeled htC with
            ⟨m, hm, hdT, hbT, hpT, _⟩ | ⟨_, hbS⟩ | ⟨_, _, _, _, _, hbQ, _⟩
          · have hmReal : m.dummy = false := by rw [← hdT]; exact htdummy
            have hmBorder : m.node.border = 2 := hbT.symm.trans htborder
            have hmPath : m.node.clusterPath = ndT.node.clusterPath :=
              (hpT hmReal).symm
            rcases hk t m hm with
              ⟨nT, hnT, _, hbN, hpN⟩ | ⟨hdM, _, _⟩
            case inl =>
              have hnTBorder : nT.border = 2 := hbN.symm.trans hmBorder
              have hnTPath : nT.clusterPath = ndT.node.clusterPath :=
                hpN.symm.trans hmPath
              rcases hk origIdx orig hOrigLook with
                ⟨nA, hnA, _, hbA, hpA⟩ | ⟨hdA, _, _⟩
              case inl =>
                have hnABorder : nA.border = -2 := hbA.symm.trans hOrigBorder
                have hnAPath : nA.clusterPath = ndV.node.clusterPath :=
                  (hTitlePath.trans hpA).symm
                have hpathEq : nA.clusterPath = nT.clusterPath := by
                  rw [hnAPath, hpath, hnTPath]
                have htLen : t < (componentCandidate graph comp candidate).nodes.length :=
                  (List.getElem?_eq_some_iff.mp hnT).1
                have haLen : origIdx <
                    (componentCandidate graph comp candidate).nodes.length :=
                  (List.getElem?_eq_some_iff.mp hnA).1
                have hrt : rk (coordinateGraph P labeled).rank t = rk rr.ranks t :=
                  prepared_coordinate_original_rk hrr hranks htLen
                have hrvCoord : rk run.coordinateProper.rank v =
                    rk labeled.rank origIdx := by
                  rw [← hcoord]; exact hRankEq
                obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
                  (g := Compound.rankingGraph
                    (componentCandidate graph comp candidate)) (r := rr.ranks)
                  (by simp only [RankImpl.rank, hrr])
                have hlength : rr.ranks.length =
                    (componentCandidate graph comp candidate).nodes.length :=
                  hinvariant.1
                have hrrLookup : rr.ranks[origIdx]? =
                    some rr.ranks[origIdx] :=
                  List.getElem?_eq_getElem (by omega)
                have hlabLookup := hranks origIdx _ hrrLookup
                have hlabRk : rk labeled.rank origIdx = rr.ranks[origIdx] := by
                  simp only [rk, List.getD_eq_getElem?_getD, hlabLookup,
                    Option.getD_some]
                have hrrRk : rk rr.ranks origIdx = rr.ranks[origIdx] := by
                  simp only [rk, List.getD_eq_getElem?_getD, hrrLookup,
                    Option.getD_some]
                have hrv : rk run.coordinateProper.rank v = rk rr.ranks origIdx := by
                  rw [hrvCoord, hlabRk, ← hrrRk]
                have hrtRun : rk run.coordinateProper.rank t = rk rr.ranks t := by
                  rw [← hcoord]; exact hrt
                obtain ⟨cA, hcA, hgA⟩ :=
                  componentCandidate_nonplain_source hnA (by omega)
                obtain ⟨cT, hcT, hgT⟩ :=
                  componentCandidate_nonplain_source hnT (by omega)
                have hdecl : nT.decl = nA.decl := by
                  have hmemT : nT ∈ graph.nodes :=
                    List.mem_of_getElem? hgT
                  have hiff := measuredGraph_group_bottom_path_iff_decl hgraph
                    hgA hnABorder hmemT hnTBorder
                  exact hiff.mp hpathEq.symm
                have hfind := componentCandidate_bottom_find_eq hgraph hcomp hnT hnTBorder
                rw [hdecl] at hfind
                obtain ⟨rr2, _, hrr2, _, _, _, _, hmain⟩ :=
                  componentRun_group_top_lt_bottom hgraph hcomp hrun
                have hrrEq : rr = rr2 := by
                  have e2 := hrr2
                  rw [hrr] at e2
                  exact Except.ok.inj e2
                have hle0 := hmain origIdx nA (nT, t) hnA hnABorder hfind
                rw [← hrrEq] at hle0
                have hle : rk rr.ranks origIdx + 1 ≤ rk rr.ranks t := hle0
                have hne : rk rr.ranks origIdx ≠ rk rr.ranks t := by omega
                rw [← hrv, ← hrtRun] at hne
                exact hne
              case inr =>
                rw [hdA] at hOrigReal
                cases hOrigReal
            case inr =>
              rw [hdM] at hmReal
              cases hmReal
          · rcases hbS with hbS | hbS <;> omega
          · omega

/-- `TitleCopyNestedRank` for an executed measured graph, modulo the strict-prefix
residual. The equal-path case is `titleCopyNestedRank_equal`; the strict case is
exactly `TitleCopyNestedStrictPrefix`. -/
theorem titleCopyNestedRank {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hstrict : TitleCopyNestedStrictPrefix P graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {t v : Nat}
    (htdummy : (run.coordinateProper.nodes.getD t default).dummy = false)
    (htborder : (run.coordinateProper.nodes.getD t default).node.border = 2)
    (hvborder : (run.coordinateProper.nodes.getD v default).node.border = 3)
    (hpath : (run.coordinateProper.nodes.getD v default).node.clusterPath =
        (run.coordinateProper.nodes.getD t default).node.clusterPath ∨
      (run.coordinateProper.nodes.getD t default).node.clusterPath <+:
        (run.coordinateProper.nodes.getD v default).node.clusterPath) :
    rk run.coordinateProper.rank v ≠ rk run.coordinateProper.rank t := by
  rcases hpath with heq | hpref
  · exact titleCopyNestedRank_equal hgraph hcomp hrun htdummy htborder hvborder heq
  · by_cases heq : (run.coordinateProper.nodes.getD v default).node.clusterPath =
        (run.coordinateProper.nodes.getD t default).node.clusterPath
    · exact titleCopyNestedRank_equal hgraph hcomp hrun htdummy htborder hvborder heq
    · exact hstrict hgraph hlines hwf hframed comp hcomp candidate run labels orderOptions hrun t v
        htdummy htborder hvborder hpref heq

/-- The bracket-seam field for title copies, for every executed component run.
Outside the proxy's bracket the ordered-interval separation gives the
disjunction directly; strictly inside, `componentRun_inside_prefix` extends the
proxy's path along the copy's node path and `titleCopyNestedRank` contradicts
the shared rank. -/
theorem titleCopySpanClearStrict_of_execution {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hstrict : TitleCopyNestedStrictPrefix P graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {t v : Nat}
    (htdummy : (run.coordinateProper.nodes.getD t default).dummy = false)
    (htborder : (run.coordinateProper.nodes.getD t default).node.border = 2)
    (hvborder : (run.coordinateProper.nodes.getD v default).node.border = 3)
    (_hheight : 0 < RouteImpl.nodeH run.proper v)
    (hrankEq : rk run.coordinateProper.rank v = rk run.coordinateProper.rank t) :
    RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t ≤
        RouteImpl.leftOf run.proper run.xs v ∨
      RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
        RouteImpl.leftOf run.proper run.xs t := by
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _⟩ :=
    componentRun_spec hrun
  obtain ⟨proxy, htp⟩ : ∃ x, run.coordinateProper.nodes[t]? = some x := by
    cases hx : run.coordinateProper.nodes[t]? with
    | none =>
        rw [List.getD_eq_getElem?_getD, hx, Option.getD_none] at htborder
        have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
        omega
    | some x => exact ⟨x, rfl⟩
  obtain ⟨htLen, _⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder htp
  obtain ⟨other, hv0⟩ : ∃ x, run.coordinateProper.nodes[v]? = some x := by
    cases hx : run.coordinateProper.nodes[v]? with
    | none =>
        rw [List.getD_eq_getElem?_getD, hx, Option.getD_none] at hvborder
        have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
        omega
    | some x => exact ⟨x, rfl⟩
  have htGetD : run.coordinateProper.nodes.getD t default = proxy := by
    simp only [List.getD_eq_getElem?_getD, htp, Option.getD_some]
  have hvGetD : run.coordinateProper.nodes.getD v default = other := by
    simp only [List.getD_eq_getElem?_getD, hv0, Option.getD_some]
  have htBorder : proxy.node.border = -2 ∨ proxy.node.border = 2 := by
    right
    rw [← htGetD]; exact htborder
  have hvNotProxy : ¬(other.node.border = -2 ∨ other.node.border = 2) := by
    intro hc
    rcases hc with hc | hc
    · rw [hvGetD] at hvborder
      omega
    · rw [hvGetD] at hvborder
      omega
  have hlayTV : OrderImpl.lay run.coordinateProper t =
      OrderImpl.lay run.coordinateProper v := by
    unfold OrderImpl.lay
    rw [hrankEq]
  obtain ⟨_, hvIn0⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hv0
  rw [← hlayTV] at hvIn0
  have hlayLen : OrderImpl.lay run.coordinateProper t < run.layers.length := by
    rw [← hlayers]; exact htLen
  have hlayer : run.layers[OrderImpl.lay run.coordinateProper t]? =
      some (run.layers[OrderImpl.lay run.coordinateProper t]'(hlayLen)) :=
    List.getElem?_eq_getElem hlayLen
  have hlayerMem : run.layers[OrderImpl.lay run.coordinateProper t]'(hlayLen) ∈
      run.layers :=
    List.getElem_mem hlayLen
  have hvMem : v ∈ run.layers[OrderImpl.lay run.coordinateProper t]'(hlayLen) := by
    have h1 := hvIn0
    simp only [hlayers, hlayer, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  obtain ⟨owner, leftIndex, rightIndex, left, right, ownerEq, hleft, hright,
      _, _, hleftBorder, hrightBorder, hleftOwner, hrightOwner,
      hleftRank, hrightRank, hleftEq, hrightEq⟩ :=
    componentRun_proxy_border_extrema hrun htp htBorder
  have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
    rcases hleftBorder with hb | hb <;> omega
  have hrightNotProxy : ¬(right.node.border = -2 ∨ right.node.border = 2) := by
    rcases hrightBorder with hb | hb <;> omega
  have hlayL : OrderImpl.lay run.coordinateProper leftIndex =
      OrderImpl.lay run.coordinateProper t := by
    unfold OrderImpl.lay
    rw [hleftRank]
  have hlayR : OrderImpl.lay run.coordinateProper rightIndex =
      OrderImpl.lay run.coordinateProper t := by
    unfold OrderImpl.lay
    rw [hrightRank]
  obtain ⟨_, hleftMemOrd⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hleft
  obtain ⟨_, hrightMemOrd⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hright
  rw [hlayL] at hleftMemOrd
  rw [hlayR] at hrightMemOrd
  have hleftMem : leftIndex ∈
      run.layers[OrderImpl.lay run.coordinateProper t]'(hlayLen) := by
    have h1 := hleftMemOrd
    simp only [hlayers, hlayer, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  have hrightMem : rightIndex ∈
      run.layers[OrderImpl.lay run.coordinateProper t]'(hlayLen) := by
    have h1 := hrightMemOrd
    simp only [hlayers, hlayer, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  obtain ⟨leftPos, hleftPos⟩ := List.mem_iff_getElem?.mp hleftMem
  obtain ⟨rightPos, hrightPos⟩ := List.mem_iff_getElem?.mp hrightMem
  obtain ⟨vPos, hvPos⟩ := List.mem_iff_getElem?.mp hvMem
  have hleftGD : run.coordinateProper.nodes.getD leftIndex default = left := by
    simp only [List.getD_eq_getElem?_getD, hleft, Option.getD_some]
  have hrightGD : run.coordinateProper.nodes.getD rightIndex default = right := by
    simp only [List.getD_eq_getElem?_getD, hright, Option.getD_some]
  obtain ⟨_, _, labeledS, _, hnS, hlS, hcoordS, _⟩ :=
    componentRun_ranked_source hrun
  have hkS : NodeKeys (componentCandidate graph comp candidate) labeledS :=
    addLabelNodes_keys _ _ _ (normalize_keys hnS) hlS
  have halignedS : labeledS.nodes.length = labeledS.rank.length := by
    rw [← addLabelNodes_node_length hlS, (Labels.addLabelNodes_metadata hlS).2.1]
    exact (normalize_node_rank_alignment hnS).1
  have hshapeS : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hvborder' : other.node.border = 3 := by rw [← hvGetD]; exact hvborder
  have hvCS : (coordinateGraph P labeledS).nodes[v]? = some other := by
    rw [hcoordS]; exact hv0
  obtain ⟨_, _, _, _, _, hvDummyF, _, _⟩ :=
    coordinateGraph_title_rank_source hkS hshapeS halignedS hvCS hvborder'
  have hside := sidePathEq_of_measuredGraph hgraph comp hcomp candidate run labels
    orderOptions hrun t
  obtain ⟨hleftPath, hleftDummy⟩ := hside leftIndex htborder
    (by rw [hleftGD]; exact hleftBorder)
    (by rw [htGetD, hleftGD]; exact ownerEq.trans hleftOwner.symm)
  obtain ⟨hrightPath, hrightDummy⟩ := hside rightIndex htborder
    (by rw [hrightGD]; exact hrightBorder)
    (by rw [htGetD, hrightGD]; exact ownerEq.trans hrightOwner.symm)
  have hnest := titleCopyNestedRank hgraph hlines hwf hframed hstrict hcomp hrun htdummy htborder
    hvborder
  have hip := componentRun_inside_prefix hgraph hcomp hrun proxy.node.clusterPath
  rcases Nat.lt_trichotomy vPos leftPos with hlt | heq | hgt
  case inl =>
    have hsep : RouteImpl.leftOf run.proper run.xs v +
        RouteImpl.nodeW run.proper v ≤
        RouteImpl.leftOf run.proper run.xs leftIndex :=
      componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayerMem hlt
        hvPos hleftPos hv0 hleft hvNotProxy hleftNotProxy
    rw [← hleftEq] at hsep
    exact Or.inr hsep
  case inr.inl =>
    have hvEqL : v = leftIndex := by
      rw [heq] at hvPos
      rw [hleftPos] at hvPos
      exact Option.some.inj hvPos.symm
    subst hvEqL
    rw [hleftGD] at hvborder
    rcases hleftBorder with hb | hb <;> omega
  case inr.inr =>
    rcases Nat.lt_trichotomy vPos rightPos with hlt2 | heq2 | hgt2
    case inl =>
      exfalso
      have hltBound : leftPos < vPos := by omega
      have hipRule := hip.2 _ hlayerMem leftPos vPos rightPos leftIndex rightIndex v
        hleftPos hvPos hrightPos hltBound hlt2
        (by rw [hleftGD]; exact hleftBorder)
        (by rw [hleftPath]; rw [htGetD])
        hleftDummy
        (by rw [hrightGD]; exact hrightBorder)
        (by rw [hrightPath]; rw [htGetD])
        hrightDummy
        (by rw [hvGetD]; exact hvDummyF)
      have hnp : OrderImpl.nodePath run.coordinateProper v =
          other.node.clusterPath := by
        unfold OrderImpl.nodePath
        rw [hvGetD]
        simp [hvDummyF]
      rw [hnp] at hipRule
      have htPath : proxy.node.clusterPath =
          (run.coordinateProper.nodes.getD t default).node.clusterPath := by
        rw [htGetD]
      have hvPath : other.node.clusterPath =
          (run.coordinateProper.nodes.getD v default).node.clusterPath := by
        rw [hvGetD]
      have hpref : (run.coordinateProper.nodes.getD t default).node.clusterPath <+:
          (run.coordinateProper.nodes.getD v default).node.clusterPath := by
        rw [← htPath, ← hvPath]
        exact hipRule
      have hne := hnest (Or.inr hpref)
      omega
    case inr.inl =>
      have hvEqR : v = rightIndex := by
        rw [heq2] at hvPos
        rw [hrightPos] at hvPos
        exact Option.some.inj hvPos.symm
      subst hvEqR
      rw [hrightGD] at hvborder
      rcases hrightBorder with hb | hb <;> omega
    case inr.inr =>
      have hsep : RouteImpl.leftOf run.proper run.xs rightIndex +
          RouteImpl.nodeW run.proper rightIndex ≤
          RouteImpl.leftOf run.proper run.xs v :=
        componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayerMem hgt2
          hrightPos hvPos hright hv0 hrightNotProxy hvNotProxy
      rw [← hrightEq] at hsep
      exact Or.inl hsep

/-- Copy of `bnr_cg_path_last` (`BottomNestedRankProof.lean`, itself mirroring
`cg_path_last` in `GroupTopRankResidualsProof.lean`): a cluster path ending in
`d` has last element `d`. -/
private theorem tcp_cg_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp

/-- Copy of `bnr_cg_group_box` (`BottomNestedRankProof.lean`, mirroring
`cg_group_box` in `GroupTopRankResidualsProof.lean`): a candidate `-2` node path
source in input boxes. -/
private theorem tcp_cg_group_box {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨_, ho, hsource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin hgraph hsource hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  rw [← hdecl] at hbox
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap] at hpath
  exact hpath

/-- `boxLines` produces one line block per input box (copy of `dummy_lines_length`
in `DummyRowClearProof.lean`). -/
private theorem tcp_lines_length {m : Measure.Metric} {target : Int}
    {inp : Input} {lines : List (List Measure.Line)}
    (h : boxLines m target inp = .ok lines) : lines.length = inp.boxes.length := by
  unfold boxLines at h
  have hlen := (mapM_getElem? _ _ _ h).1
  have hzip : (inp.boxes.zipIdx).length = inp.boxes.length := List.length_zipIdx
  omega

/-- The strict-prefix residual holds for every measured graph: a border-`3` copy
whose path strictly extends a bottom proxy's path cannot share the proxy's rank.
Strong induction mirroring `cg_nested_top_rank`
(`GroupTopRankResidualsProof.lean`) is already closed by
`bottomNestedBottomRankLe_wf` (`BottomNestedRankProof.lean`, via
`Compound.path_ancestor_prefix` and `candidate_parent_top_exists`): the copy
inherits its `-2` anchor's rank (`coordinateGraph_title_rank_source`); the anchor
ranks strictly below its own bottom (`componentRun_group_top_lt_bottom`); that
inner bottom ranks at or below the outer bottom (`bottomNestedBottomRankLe_wf`);
equal declarations collapse the two bottoms (`componentCandidate_bottom_find_eq`).
`bnr_cg_scope_prefix`-style membership is rebuilt from the outer-top last
(`tcp_cg_path_last`/`tcp_cg_group_box`) and the borrowed bottom path identity
(`componentCandidate_bottom_lookup_keys`). -/
theorem titleCopyNestedStrictPrefix {P : Params} {graph : Graph} :
    TitleCopyNestedStrictPrefix P graph := by
  intro inp o lines hgraph hlines hwf hframed comp hcomp candidate run labels
    orderOptions hrun t v htdummy htborder hvborder hpref hne
  obtain ⟨rr, normalized, labeled, hrr, hn, hl, hcoord, _⟩ :=
    componentRun_ranked_source hrun
  have hk : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩ := by
    intro index node hnode
    exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  have hranks : ∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
      labeled.rank[index]? = some rank := by
    intro index rank hrank
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hrank
  cases hvt : run.coordinateProper.nodes[t]? with
  | none =>
      rw [List.getD_eq_getElem?_getD, hvt, Option.getD_none] at htborder
      have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
      omega
  | some ndT =>
      have htD : run.coordinateProper.nodes.getD t default = ndT := by
        simp only [List.getD_eq_getElem?_getD, hvt, Option.getD_some]
      rw [htD] at htdummy htborder hpref hne
      cases hvv : run.coordinateProper.nodes[v]? with
      | none =>
          rw [List.getD_eq_getElem?_getD, hvv, Option.getD_none] at hvborder
          have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
          omega
      | some ndV =>
          have hvD : run.coordinateProper.nodes.getD v default = ndV := by
            simp only [List.getD_eq_getElem?_getD, hvv, Option.getD_some]
          rw [hvD] at hvborder hpref hne
          have hvC : (coordinateGraph P labeled).nodes[v]? = some ndV := by
            rw [hcoord]; exact hvv
          obtain ⟨origIdx, orig, hOrigLook, hOrigBorder, hOrigReal, _,
              hTitlePath, hRankEq⟩ :=
            coordinateGraph_title_rank_source hk hshape haligned hvC hvborder
          have htC : (coordinateGraph P labeled).nodes[t]? = some ndT := by
            rw [hcoord]; exact hvt
          rcases coordinateGraph_lookup P labeled htC with
            ⟨m, hm, hdT, hbT, hpT, _⟩ | ⟨_, hbS⟩ | ⟨_, _, _, _, _, hbQ, _⟩
          · have hmReal : m.dummy = false := by rw [← hdT]; exact htdummy
            have hmBorder : m.node.border = 2 := hbT.symm.trans htborder
            have hmPath : m.node.clusterPath = ndT.node.clusterPath :=
              (hpT hmReal).symm
            rcases hk t m hm with
              ⟨nT, hnT, _, hbN, hpN⟩ | ⟨hdM, _, _⟩
            case inl =>
              have hnTBorder : nT.border = 2 := hbN.symm.trans hmBorder
              have hnTPath : nT.clusterPath = ndT.node.clusterPath :=
                hpN.symm.trans hmPath
              rcases hk origIdx orig hOrigLook with
                ⟨nA, hnA, _, hbA, hpA⟩ | ⟨hdA, _, _⟩
              case inl =>
                have hnABorder : nA.border = -2 := hbA.symm.trans hOrigBorder
                have hnAPath : nA.clusterPath = ndV.node.clusterPath :=
                  (hTitlePath.trans hpA).symm
                have hpreCand : nT.clusterPath <+: nA.clusterPath := by
                  rw [hnTPath, hnAPath]
                  exact hpref
                have hneCand : nA.clusterPath ≠ nT.clusterPath := by
                  intro heq
                  apply hne
                  rw [← hnAPath, ← hnTPath, heq]
                have htLen : t < (componentCandidate graph comp candidate).nodes.length :=
                  (List.getElem?_eq_some_iff.mp hnT).1
                have haLen : origIdx <
                    (componentCandidate graph comp candidate).nodes.length :=
                  (List.getElem?_eq_some_iff.mp hnA).1
                have hrt : rk (coordinateGraph P labeled).rank t = rk rr.ranks t :=
                  prepared_coordinate_original_rk hrr hranks htLen
                have hrvCoord : rk run.coordinateProper.rank v =
                    rk labeled.rank origIdx := by
                  rw [← hcoord]; exact hRankEq
                obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
                  (g := Compound.rankingGraph
                    (componentCandidate graph comp candidate)) (r := rr.ranks)
                  (by simp only [RankImpl.rank, hrr])
                have hlength : rr.ranks.length =
                    (componentCandidate graph comp candidate).nodes.length :=
                  hinvariant.1
                have hrrLookup : rr.ranks[origIdx]? =
                    some rr.ranks[origIdx] :=
                  List.getElem?_eq_getElem (by omega)
                have hlabLookup := hranks origIdx _ hrrLookup
                have hlabRk : rk labeled.rank origIdx = rr.ranks[origIdx] := by
                  simp only [rk, List.getD_eq_getElem?_getD, hlabLookup,
                    Option.getD_some]
                have hrrRk : rk rr.ranks origIdx = rr.ranks[origIdx] := by
                  simp only [rk, List.getD_eq_getElem?_getD, hrrLookup,
                    Option.getD_some]
                have hrv : rk run.coordinateProper.rank v = rk rr.ranks origIdx := by
                  rw [hrvCoord, hlabRk, ← hrrRk]
                have hrtRun : rk run.coordinateProper.rank t = rk rr.ranks t := by
                  rw [← hcoord]; exact hrt
                obtain ⟨Bpair, hBfind⟩ :=
                  componentRun_cg_bottom_find hgraph hlines hcomp hnA hnABorder
                obtain ⟨Tpair, hTfind⟩ :=
                  componentRun_cg_top_of_bottom hgraph hlines hcomp hnT hnTBorder
                have hBpred := List.find?_some hBfind
                simp only [Bool.and_eq_true, beq_iff_eq] at hBpred
                obtain ⟨hBborder, hBdecl⟩ := hBpred
                have hBmem : Bpair ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
                  List.mem_of_find?_eq_some hBfind
                have hBlook : (componentCandidate graph comp candidate).nodes[Bpair.2]? =
                    some Bpair.1 :=
                  List.mem_zipIdx_iff_getElem?.mp hBmem
                have hTpred := List.find?_some hTfind
                simp only [Bool.and_eq_true, beq_iff_eq] at hTpred
                obtain ⟨hTborder, hTpath⟩ := hTpred
                have hTmem : Tpair ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
                  List.mem_of_find?_eq_some hTfind
                have hTlook : (componentCandidate graph comp candidate).nodes[Tpair.2]? =
                    some Tpair.1 :=
                  List.mem_zipIdx_iff_getElem?.mp hTmem
                obtain ⟨oTN, hcompTN, hsrcTN⟩ :=
                  componentCandidate_nonplain_source hnT (by omega)
                obtain ⟨oTO, hcompTO, hsrcTO⟩ :=
                  componentCandidate_nonplain_source hTlook (by omega)
                have hmemTN : nT ∈ graph.nodes :=
                  List.mem_of_getElem? hsrcTN
                have hiffOT := measuredGraph_group_bottom_path_iff_decl hgraph
                  hsrcTO hTborder hmemTN hnTBorder
                have hOTdecl : nT.decl = Tpair.1.decl := hiffOT.mp hTpath.symm
                have hlookupEq :=
                  componentCandidate_bottom_lookup_keys hgraph hnA hnABorder
                have hpathFind : ((componentCandidate graph comp candidate).nodes.zipIdx.find?
                    fun entry => entry.1.border == 2 &&
                      entry.1.clusterPath == nA.clusterPath) = some Bpair :=
                  hlookupEq.trans hBfind
                have hpathPred := List.find?_some hpathFind
                simp only [Bool.and_eq_true, beq_iff_eq] at hpathPred
                obtain ⟨_, hIBPath⟩ := hpathPred
                obtain ⟨obox, hobox, hopath⟩ :=
                  tcp_cg_group_box hgraph hTlook hTborder
                have hOTLast : Tpair.1.clusterPath.getLast? = some Tpair.1.decl :=
                  tcp_cg_path_last hopath
                have hOTMem : Tpair.1.decl ∈ Tpair.1.clusterPath :=
                  List.mem_of_getLast? hOTLast
                have hpreOT : Tpair.1.clusterPath <+: nA.clusterPath := by
                  rw [hTpath]
                  exact hpreCand
                have hOTMemIA : Tpair.1.decl ∈ nA.clusterPath :=
                  List.IsPrefix.mem hOTMem hpreOT
                have hOTMemIB : Tpair.1.decl ∈ Bpair.1.clusterPath := by
                  rw [hIBPath]
                  exact hOTMemIA
                have hcontains : Bpair.1.clusterPath.contains Tpair.1.decl = true :=
                  List.contains_iff_mem.mpr hOTMemIB
                obtain ⟨rr2, _, hrr2, _, _, _, _, hmain⟩ :=
                  componentRun_group_top_lt_bottom hgraph hcomp hrun
                have hrrEq : rr = rr2 := by
                  have e2 := hrr2
                  rw [hrr] at e2
                  exact Except.ok.inj e2
                have hle0 := hmain origIdx nA Bpair hnA hnABorder hBfind
                rw [← hrrEq] at hle0
                by_cases hdeclEq : nA.decl = nT.decl
                · have hfindOB :=
                    componentCandidate_bottom_find_eq hgraph hcomp hnT hnTBorder
                  rw [hdeclEq] at hBfind
                  have hBeq : Bpair = (nT, t) :=
                    Option.some.inj (hBfind.symm.trans hfindOB)
                  have hB2 : Bpair.2 = t := congrArg Prod.snd hBeq
                  rw [hB2] at hle0
                  have hneRR : rk rr.ranks origIdx ≠ rk rr.ranks t := by omega
                  rw [← hrv, ← hrtRun] at hneRR
                  exact hneRR
                · have hneOT : Bpair.1.decl ≠ Tpair.1.decl := by
                    rw [hBdecl]
                    intro hcon
                    exact hdeclEq (hcon.trans hOTdecl.symm)
                  have hrank := bottomNestedBottomRankLe_wf hgraph hlines hwf hframed
                    hcomp hrun hnT hTlook hnTBorder hTborder hOTdecl hBlook
                    hBborder hneOT hcontains
                  have hBlen : Bpair.2 <
                      (componentCandidate graph comp candidate).nodes.length :=
                    (List.getElem?_eq_some_iff.mp hBlook).1
                  have heB := prepared_coordinate_original_rk (P := P) hrr hranks hBlen
                  rw [hcoord] at heB
                  have hleRR : rk rr.ranks Bpair.2 ≤ rk rr.ranks t := by omega
                  have hlt : rk rr.ranks origIdx + 1 ≤ rk rr.ranks t := by omega
                  have hneRR : rk rr.ranks origIdx ≠ rk rr.ranks t := by omega
                  rw [← hrv, ← hrtRun] at hneRR
                  exact hneRR
              case inr =>
                rw [hdA] at hOrigReal
                cases hOrigReal
            case inr =>
              rw [hdM] at hmReal
              cases hmReal
          · rcases hbS with hbS | hbS <;> omega
          · omega

/-- The `LayeredSeams.titleCopySpan` field for executed runs: the seam premise
is discharged by `titleCopyNestedStrictPrefix` and
`titleCopySpanClearStrict_of_execution`. The execution supplies the
`measuredGraph` equation and the line count (`tcp_lines_length` over
`execution.lines_eq`). -/
theorem titleCopySpanClearStrict_executed {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res) :
    titleCopySpanClearStrict execution.params execution.graph := by
  have hgraph : measuredGraph execution.params inp o execution.lines = .ok execution.graph :=
    execution.graph_eq
  have hlines : execution.lines.length = inp.boxes.length :=
    tcp_lines_length execution.lines_eq
  have hstrict : TitleCopyNestedStrictPrefix execution.params execution.graph :=
    titleCopyNestedStrictPrefix
  intro comp hcomp candidate run labels orderOptions hrun t v htdummy htborder
    hvborder hheight hrankEq
  exact titleCopySpanClearStrict_of_execution hgraph hlines hwf hframed hstrict hcomp hrun
    htdummy htborder hvborder hheight hrankEq

end Elegant.Layered.PipelineImpl

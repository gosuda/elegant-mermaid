import Elegant.Layered.GroupTopRankResidualsProof
import Elegant.Layered.BottomSyntheticRankProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ### Chain-rank lift for edge dummies

An edge dummy inserted by `NormalizeImpl.normalizeEdge` lies on the chain of
the original edge it subdivides. `componentRun_dummy_path_chain_source`
places the dummy between its endpoint ranks and carries the common endpoint
path to the dummy (`commonPath_member_both` inside its proof);
`componentRun_labeled_chain_rank_positions` makes the rank contiguity exact.
The bracket below lifts this to executed `run.proper` dummies and feeds both
the group-top residual (`GroupTopDummyRankLe`, via the lower endpoint and
`groupTopSubtreeRankCg`) and the bottom residual (`BottomDummyRankLe`, via
the upper endpoint and `bottomOrigRankLe`). -/

/-- Executed proper ranks agree with coordinate ranks index-wise. -/
private theorem proper_rank_eq_local {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) (x : Nat) :
    rk run.proper.rank x = rk run.coordinateProper.rank x := by
  have h : run.proper.rank = run.coordinateProper.rank := by
    obtain ⟨_, _, _, q0, _, _, _, _, _, hprox, hdrop, _, _, _, _, _⟩ :=
      componentRun_spec hrun
    obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hprox
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  rw [h]

/-- An executed proper dummy has the same record in the coordinate graph. -/
private theorem proper_to_coordinate_dummy {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {pn : ProperNode}
    (hp : run.proper.nodes[i]? = some pn) (hd : pn.dummy = true) :
    ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = true ∧
      cn.node.border = pn.node.border ∧ cn.node.clusterPath = pn.node.clusterPath := by
  obtain ⟨_, _, labeled, q0, hn, hl, hc, _, _, hprox, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq0i : q0.nodes[i]? = some pn := by rw [← hnodes]; exact hp
  have hlen : q0.nodes.length = run.coordinateProper.nodes.length :=
    (proxyWidths_rel hprox).2.2.1
  have hiC : i < run.coordinateProper.nodes.length := by
    have hi0 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0i).1
    omega
  obtain ⟨cn, hcn⟩ : ∃ cn, run.coordinateProper.nodes[i]? = some cn :=
    ⟨_, List.getElem?_eq_getElem hiC⟩
  obtain ⟨nd', hnd', hddum, _, _⟩ :=
    (proxyWidths_rel hprox).2.2.2.2.1 i cn hcn
  have hndEq : nd' = pn := Option.some.inj (hnd'.symm.trans hq0i)
  have hcnDum : cn.dummy = true := by rw [← hddum, hndEq]; exact hd
  have hK : NodeKeys cg labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hcnL : (coordinateGraph P labeled).nodes[i]? = some cn := by
    rw [hc]; exact hcn
  have hbord0 : cn.node.border = 0 := pc_plain hK hcnL hcnDum
  have hnp : ¬ (cn.node.border = -2 ∨ cn.node.border = 2) := by
    rw [hbord0]; decide
  obtain ⟨hsame, _⟩ := (proxyWidths_rel hprox).2.2.2.2.2 i cn hcn hnp
  have hcnEq : cn = pn := Option.some.inj (hsame.symm.trans hq0i)
  exact ⟨cn, hcn, hcnDum, by rw [hcnEq], by rw [hcnEq]⟩

/-- Labeled nodes and ranks stay aligned through normalize and label nodes. -/
private theorem labeled_rank_aligned {cg : Graph}
    {rr : RankImpl.RankResult} {normalized labeled : Proper}
    {labels : List MeasuredLabel}
    (hnormalize : normalize cg rr.ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled) :
    labeled.nodes.length = labeled.rank.length := by
  have h1 := addLabelNodes_node_length hlabels
  have h2 := congrArg List.length (Labels.addLabelNodes_metadata hlabels).2.1
  have h3 := (normalize_node_rank_alignment hnormalize).1
  omega

/-- Coordinate ranks agree with labeled ranks index-wise. -/
private theorem coord_rank_eq {P : Params} {labeled : Proper} {run : Run}
    (hcoord : coordinateGraph P labeled = run.coordinateProper)
    (haligned : labeled.nodes.length = labeled.rank.length)
    {x : Nat} (hx : x < labeled.nodes.length) :
    rk run.coordinateProper.rank x = rk labeled.rank x := by
  have hxr : x < labeled.rank.length := by omega
  have hlab : labeled.rank[x]? = some (labeled.rank[x]'hxr) :=
    List.getElem?_eq_getElem hxr
  have hcoo : run.coordinateProper.rank[x]? = some (labeled.rank[x]'hxr) := by
    rw [← hcoord]
    exact coordinateGraph_rank_record hlab
  simp only [rk, List.getD_eq_getElem?_getD, hlab, hcoo, Option.getD_some]

/-- Prepared (materialization-input) nodes keep their labeled cluster path. -/
private theorem prepared_path_eq {P : Params} {labeled : Proper}
    {j : Nat} {pn : ProperNode}
    (hlab : labeled.nodes[j]? = some pn) :
    ∃ qn, (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes[j]? =
      some qn ∧ qn.node.clusterPath = pn.node.clusterPath := by
  have hj : j < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hlab).1
  have hlen1 : (sizeProperPorts P labeled).nodes.length = labeled.nodes.length :=
    sizeProperPorts_length P labeled
  have hs1 := sizeProperPorts_key P labeled j
  rw [hlab] at hs1
  obtain ⟨m1, hm1, htrip⟩ : ∃ m1, (sizeProperPorts P labeled).nodes[j]? = some m1 ∧
      (m1.dummy, m1.node.border, m1.node.clusterPath) =
        (pn.dummy, pn.node.border, pn.node.clusterPath) := by
    cases hs : (sizeProperPorts P labeled).nodes[j]? with
    | none => simp [hs] at hs1
    | some m1 =>
      simp only [hs, Option.map_some, Option.some.injEq] at hs1
      exact ⟨m1, rfl, hs1⟩
  have hp1 : m1.node.clusterPath = pn.node.clusterPath := by
    have h3 := congrArg (fun t : Bool × Int × List Nat => t.2.2) htrip
    simpa using h3
  have hm2 : (titleReservations (sizeProperPorts P labeled)).nodes[j]? =
      some (titleF m1) := by
    have hJ : j < ((sizeProperPorts P labeled).nodes.map titleF).length := by
      rw [List.length_map, hlen1]; exact hj
    rw [titleReservations_nodes, List.getElem?_append_left hJ, List.getElem?_map, hm1,
      Option.map_some]
  have hp2 : (titleF m1).node.clusterPath = pn.node.clusterPath := by
    rw [(titleF_keys m1).2.2.1]; exact hp1
  have hlen2 : (titleReservations (sizeProperPorts P labeled)).nodes.length =
      (sizeProperPorts P labeled).nodes.length +
        ((titleNodes (sizeProperPorts P labeled)).map copyF).length := by
    rw [titleReservations_nodes, List.length_append, List.length_map, List.length_map]
  have hj2 : j < (titleReservations (sizeProperPorts P labeled)).nodes.length := by
    omega
  obtain ⟨extra, hx, _⟩ :=
    addClusterBorders_extra (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW
  have hm3 : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW).nodes[j]? =
      (titleReservations (sizeProperPorts P labeled)).nodes[j]? := by
    rw [hx]; exact List.getElem?_append_left hj2
  have hm4 : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes[j]? =
      some (clearF (titleF m1)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hm3, hm2, Option.map_some]
  have hp4 : (clearF (titleF m1)).node.clusterPath = pn.node.clusterPath := by
    rw [(clearF_keys (titleF m1)).2.2.1]; exact hp2
  exact ⟨_, hm4, hp4⟩

/-- Every executed proper dummy lies on its original edge's chain between its
endpoint ranks, and both endpoint candidate paths carry the dummy's owner.
The endpoints are the original edge tail (lower rank) and head (upper rank). -/
theorem dummy_chain_bracket {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < run.proper.nodes.length)
    (hdummy : (run.proper.nodes.getD i default).dummy = true)
    {owner : Nat} (howner : owner ∈ (run.proper.nodes.getD i default).node.clusterPath) :
    ∃ (index : Nat) (edge : Edge),
      cg.edges[index]? = some edge ∧
      edge.tail ≠ edge.head ∧
      edge.tail < cg.nodes.length ∧ edge.head < cg.nodes.length ∧
      rk run.coordinateProper.rank edge.tail ≤ rk run.coordinateProper.rank i ∧
      rk run.coordinateProper.rank i ≤ rk run.coordinateProper.rank edge.head ∧
      ∃ (nA nB : Node),
        cg.nodes[edge.tail]? = some nA ∧ cg.nodes[edge.head]? = some nB ∧
        nA.clusterPath.contains owner = true ∧ nB.clusterPath.contains owner = true := by
  have hp : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
    simp [List.getD_eq_getElem?_getD, hi]
  obtain ⟨cn, hcn, hcnDum, _, hcnPath⟩ := proper_to_coordinate_dummy hrun hp hdummy
  have hownerC : owner ∈ cn.node.clusterPath := by rw [hcnPath]; exact howner
  obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordRun, hpositions⟩ :=
    componentRun_labeled_chain_rank_positions hrun
  obtain ⟨rrC, normC, labC, index, edge, chain, position,
      hrrC, hnormC, hlabC, hcoordC, hedge, hchainC, hpos, hhead, hlast, hrankC,
      _hfind, hleftC, hrightC⟩ :=
    componentRun_dummy_path_chain_source hrun hcn hcnDum hownerC
  have e1 : rr = rrC := Except.ok.inj (hrr.symm.trans hrrC)
  subst e1
  have e2 : normalized = normC := Except.ok.inj (hnormalize.symm.trans hnormC)
  subst e2
  have e3 : labeled = labC := Except.ok.inj (hlabels.symm.trans hlabC)
  subst e3
  have hindex : index < cg.edges.length := (List.getElem?_eq_some_iff.mp hedge).1
  have hwf : cg.wellformed = true := (normalize_node_rank_alignment hnormalize).2
  have hedgeMem : edge ∈ cg.edges := List.mem_of_getElem? hedge
  obtain ⟨htailLt, hheadLt, _⟩ := RankImpl.wellformed_spec hwf edge hedgeMem
  have hchainsEq : labeled.chains = normalized.chains :=
    (Labels.addLabelNodes_metadata hlabels).2.2.1
  have hfact := (normalize_ok hnormalize).2.2 index hindex edge hedge
  have hne : edge.tail ≠ edge.head := by
    intro heq
    have hif := hfact.2
    simp only [heq, ↓reduceIte] at hif
    rw [← hchainsEq] at hif
    have hempty : chain = [] := Option.some.inj (hchainC.symm.trans hif)
    rw [hempty] at hpos
    simp at hpos
  have hlastElem : chain[chain.length - 1]? = some edge.head := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hlastLt : chain.length - 1 < chain.length :=
    (List.getElem?_eq_some_iff.mp hlastElem).1
  have hposLen : position < chain.length := (List.getElem?_eq_some_iff.mp hpos).1
  have hlastEq : chain[chain.length - 1]'hlastLt = edge.head :=
    Option.some.inj ((List.getElem?_eq_getElem hlastLt).symm.trans hlastElem)
  have hlastRank := hpositions index edge chain hedge hchainC (chain.length - 1) hlastLt
  rw [hlastEq] at hlastRank
  have hlabLe1 : rk labeled.rank edge.tail ≤ rk labeled.rank i := by omega
  have hlabLe2 : rk labeled.rank i ≤ rk labeled.rank edge.head := by omega
  have hlenN := normalize_nodes_length_le hnormalize
  have hlenL : normalized.nodes.length = labeled.nodes.length :=
    addLabelNodes_node_length hlabels
  have htailL : edge.tail < labeled.nodes.length := by omega
  have hheadL : edge.head < labeled.nodes.length := by omega
  have haligned := labeled_rank_aligned hnormalize hlabels
  have hK : NodeKeys cg labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hnormalize) hlabels
  have hcnL : (coordinateGraph P labeled).nodes[i]? = some cn := by
    rw [hcoordRun]; exact hcn
  have hiL : i < labeled.nodes.length := by
    rcases coordinateGraph_lookup P labeled hcnL with
      ⟨m, hm, _, _, _, _⟩ | ⟨hdF, _⟩ | ⟨_, tq, htq, _, hdT, _, _⟩
    · exact (List.getElem?_eq_some_iff.mp hm).1
    · rw [hcnDum] at hdF; exact absurd hdF (by decide)
    · obtain ⟨hs, hbq⟩ := titleNodes_spec htq
      have hk := sizeProperPorts_key P labeled tq.2
      rw [hs] at hk
      cases hp2 : labeled.nodes[tq.2]? with
      | none => simp [hp2] at hk
      | some mp =>
        simp only [hp2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK tq.2 mp hp2 with ⟨_, _, hmd, _, _⟩ | ⟨_, hbB, _⟩
        · rw [hdT, hk1, hmd] at hcnDum; exact absurd hcnDum (by decide)
        · rw [hk2] at hbq; rw [hbB] at hbq; exact absurd hbq (by decide)
  have hcTail : rk run.coordinateProper.rank edge.tail = rk labeled.rank edge.tail :=
    coord_rank_eq hcoordRun haligned htailL
  have hcHead : rk run.coordinateProper.rank edge.head = rk labeled.rank edge.head :=
    coord_rank_eq hcoordRun haligned hheadL
  have hcI : rk run.coordinateProper.rank i = rk labeled.rank i :=
    coord_rank_eq hcoordRun haligned hiL
  have hleC1 : rk run.coordinateProper.rank edge.tail ≤ rk run.coordinateProper.rank i := by
    omega
  have hleC2 : rk run.coordinateProper.rank i ≤ rk run.coordinateProper.rank edge.head := by
    omega
  obtain ⟨nA, hnA⟩ : ∃ n, cg.nodes[edge.tail]? = some n :=
    ⟨_, List.getElem?_eq_getElem htailLt⟩
  obtain ⟨nB, hnB⟩ : ∃ n, cg.nodes[edge.head]? = some n :=
    ⟨_, List.getElem?_eq_getElem hheadLt⟩
  have hlabT : labeled.nodes[edge.tail]? = some ⟨nA, false, none, false⟩ := by
    have hn0 := normalize_node_record hnormalize hnA
    exact addLabelNodes_untouched_node hlabels hn0 rfl
  have hlabH : labeled.nodes[edge.head]? = some ⟨nB, false, none, false⟩ := by
    have hn0 := normalize_node_record hnormalize hnB
    exact addLabelNodes_untouched_node hlabels hn0 rfl
  obtain ⟨qT, hqT, hpT⟩ := prepared_path_eq hlabT
  obtain ⟨qH, hqH, hpH⟩ := prepared_path_eq hlabH
  have hheadD : chain.headD i = edge.tail := by
    cases hcchain : chain with
    | nil => simp [hcchain] at hhead
    | cons a as =>
      simp only [List.headD]
      simpa [hcchain] using hhead
  have hlastD : chain.getLastD i = edge.head := by
    rw [List.getLastD_eq_getLast?, hlast, Option.getD_some]
  have hgetDT : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes.getD
      edge.tail default = qT := by
    rw [List.getD_eq_getElem?_getD, hqT, Option.getD_some]
  have hgetDH : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes.getD
      edge.head default = qH := by
    rw [List.getD_eq_getElem?_getD, hqH, Option.getD_some]
  rw [hheadD, hgetDT] at hleftC
  rw [hlastD, hgetDH] at hrightC
  have hcontA : nA.clusterPath.contains owner = true := by
    rw [hpT] at hleftC
    exact List.contains_iff_mem.mpr hleftC
  have hcontB : nB.clusterPath.contains owner = true := by
    rw [hpH] at hrightC
    exact List.contains_iff_mem.mpr hrightC
  exact ⟨index, edge, hedge, hne, htailLt, hheadLt, hleC1, hleC2,
    nA, nB, hnA, hnB, hcontA, hcontB⟩

/-- Dummy-only restriction of the group-top closure: an executed edge dummy
whose path carries the group top declaration ranks at or below the top, via
the lower chain endpoint and `groupTopSubtreeRankCg`. -/
theorem groupTopDummyRankLe : GroupTopDummyRankLe := by
  intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run labels
    orderOptions hrun v nd hvGet hbordV hvcg i hi hpath hdum
  have howner : nd.decl ∈ (run.proper.nodes.getD i default).node.clusterPath :=
    List.contains_iff_mem.mp hpath
  obtain ⟨index, edge, _, _, htailLt, _, hle1, _, nA, _, hnA, _, hcontA, _⟩ :=
    dummy_chain_bracket hrun hi hdum howner
  obtain ⟨rr, hrr, hclose⟩ :=
    groupTopSubtreeRankCg hgraph hlines hwf hfp hcomp hrun hvGet hbordV
  have hgetDA : (componentCandidate graph comp candidate).nodes.getD edge.tail default = nA := by
    simp [List.getD_eq_getElem?_getD, hnA]
  have hgetDContains : ((componentCandidate graph comp candidate).nodes.getD edge.tail
      default).clusterPath.contains nd.decl = true := by
    rw [hgetDA]; exact hcontA
  have hleTail : rk rr.ranks v ≤ rk rr.ranks edge.tail :=
    hclose edge.tail htailLt hgetDContains
  obtain ⟨rrS, _, hrrS, hcS, _, hranksS, _, _⟩ :=
    rankSource_of_componentRun hgraph hcomp hrun
  have hrrEq : rr = rrS := Except.ok.inj (hrr.symm.trans hrrS)
  subst hrrEq
  have hVcoord : rk run.coordinateProper.rank v = rk rr.ranks v := by
    have h1 := prepared_coordinate_original_rk (P := P) hrr hranksS hvcg
    rw [← hcS]; exact h1
  have hTcoord : rk run.coordinateProper.rank edge.tail = rk rr.ranks edge.tail := by
    have h1 := prepared_coordinate_original_rk (P := P) hrr hranksS htailLt
    rw [← hcS]; exact h1
  have erv : rk run.proper.rank v = rk run.coordinateProper.rank v :=
    proper_rank_eq_local hrun v
  have eri : rk run.proper.rank i = rk run.coordinateProper.rank i :=
    proper_rank_eq_local hrun i
  omega

/-- Executed top closure with the dummy residual discharged. -/
theorem groupTopSubtreeRankProper' : GroupTopSubtreeRankProper :=
  groupTopSubtreeRankProper groupTopDummyRankLe

/-- Derived closure with the dummy residual discharged. -/
theorem properDerivedRank' : ProperDerivedRank :=
  properDerivedRank groupTopDummyRankLe

/-- Dummy-only restriction of the bottom synthetic bound: an executed edge
dummy whose path carries the outer declaration ranks at or below the outer
bottom proxy, via the upper chain endpoint and `bottomOrigRankLe`. -/
theorem bottomDummyRankLe : ∀ (P : Params) (graph : Graph), BottomDummyRankLe P graph := by
  intro P graph inp o lines hgraph hlines hwf hframed comp hcomp candidate run
    labels orderOptions hrun v t ndV ndT hvGet htGet hbordV hbordT hdecl q hq
    hcontains hdum
  have hqget : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  have hlen : q.2 < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hqget).1
  have hgetD : run.proper.nodes.getD q.2 default = q.1 := by
    simp [List.getD_eq_getElem?_getD, hqget]
  have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
      ndT.decl := by
    rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
  have howner : ((componentCandidate graph comp candidate).nodes.getD t default).decl ∈
      (run.proper.nodes.getD q.2 default).node.clusterPath := by
    rw [hgetD]; exact List.contains_iff_mem.mp hcontains
  have hdumQ : (run.proper.nodes.getD q.2 default).dummy = true := by
    rw [hgetD]; exact hdum
  obtain ⟨_, _, _, _, _, hheadLt, _, hle2, _, nB, _, hnB, _, hcontB⟩ :=
    dummy_chain_bracket hrun hlen hdumQ howner
  have hcontB' : nB.clusterPath.contains ndT.decl = true := by
    rw [← hdeclT]; exact hcontB
  have hle := bottomOrigRankLe hgraph hlines hwf hframed hcomp hrun hvGet htGet
    hbordV hbordT hdecl bottomNestedBottomRankLe hnB hcontB'
  exact Int.le_trans hle2 hle

end Elegant.Layered.PipelineImpl

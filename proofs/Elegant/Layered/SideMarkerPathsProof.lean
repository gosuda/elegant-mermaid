import Elegant.Layered.SideMarkerFactsProof
import Elegant.Layered.SizingFacts
import Elegant.Layered.Labels
import Elegant.Layered.Normalize
import Elegant.Layered.Rank

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Canonical cluster path of an executed side marker: the title path of its
declaration. Side markers are emitted by `OrderImpl.addClusterBorders`;
`addClusterBorders_side_source` carries each marker's path from its `-2`
title anchor, and title paths are determined by the declaration
(`measuredGraph_group_origin`). -/
private theorem sideMarkerCanon {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {a : Nat} {na : ProperNode} {decl : Nat}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hside : na.node.border = -1 ∨ na.node.border = 1)
    (hlast : na.node.clusterPath.getLast? = some decl) :
    ∃ box : ModelBox,
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[decl]? = some box ∧
      na.node.clusterPath = Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) box ++ [decl] := by
  obtain ⟨_, _, labeled, _, hn, hl, hcoord, _⟩ := componentRun_ranked_source hrun
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hmarkers : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []) :=
    fun index node hnode => componentCandidate_marker_shape hgraph hnode
  have hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPorts P labeled)) :=
    titled_border_ready hkeys hshape hmarkers haligned
  have hcoordinate : (coordinateGraph P labeled).nodes[a]? = some na := by
    rw [hcoord]; exact hna
  have horiginal := coordinateGraph_side_original hready hcoordinate hside
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal)
      hside
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp htop
  have hget : (titleReservations (sizeProperPorts P labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hbord : top.1.node.border = -2 := by simpa using hcond
  rcases titled_node_origin hkeys hget with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hbord
    rcases hkeys top.2 orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨_, _, hsrcG⟩ := componentCandidate_nonplain_source hbn (by omega)
      obtain ⟨_, boxG, hboxG, _, hpathG⟩ :=
        measuredGraph_group_origin hgraph hsrcG hbnB
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

/-- Two side markers of one declaration share the anchor's full cluster path:
each marker's path is the canonical title path of the shared declaration. -/
theorem sideMarkerSamePath : SideMarkerSamePath := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions
    hrun decl m m' marker marker' hmem hborder hgetLast hmem' hborder'
    hgetLast'
  obtain ⟨boxL, hboxL, hpathL⟩ :=
    sideMarkerCanon hgraph hcomp hrun hmem (Or.inl hborder) hgetLast
  obtain ⟨boxR, hboxR, hpathR⟩ :=
    sideMarkerCanon hgraph hcomp hrun hmem' (Or.inr hborder') hgetLast'
  have hbox : boxL = boxR := Option.some.inj (hboxL.symm.trans hboxR)
  rw [hpathL, hpathR, hbox]

/-- A labeled original index keeps a non-dummy record through title
reservation, border insertion, and proxy clearing. -/
private theorem preparedNondummyOfLabeled {P : Params} {labeled : Proper}
    {e : Nat} {ndL : ProperNode}
    (hlabeled : labeled.nodes[e]? = some ndL) (hdL : ndL.dummy = false) :
    ∃ pm : ProperNode,
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW)).nodes[e]? = some pm ∧ pm.dummy = false := by
  have hsize : ∃ sized, (sizeProperPorts P labeled).nodes[e]? = some sized ∧
      sized.dummy = false := by
    unfold sizeProperPorts
    simp only [List.getElem?_map, List.getElem?_zipIdx, hlabeled,
      Option.map_some]
    split
    · exact ⟨_, rfl, hdL⟩
    · exact ⟨_, rfl, hdL⟩
  obtain ⟨sized, hsized, hdS⟩ := hsize
  have hlenS : e < (sizeProperPorts P labeled).nodes.length :=
    (List.getElem?_eq_some_iff.mp hsized).1
  have htitle : (titleReservations (sizeProperPorts P labeled)).nodes[e]? =
      some (titleF sized) := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hlenS)]
    simp [List.getElem?_map, hsized]
  have hdT : (titleF sized).dummy = false := by
    rw [(titleF_keys sized).1]; exact hdS
  obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW
  have hlenT : e < (titleReservations (sizeProperPorts P labeled)).nodes.length := by
    rw [titleReservations_nodes]
    simp only [List.length_append, List.length_map]
    omega
  have hborders : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW).nodes[e]? = some (titleF sized) := by
    rw [hnodes, List.getElem?_append_left hlenT]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW)).nodes[e]? = some (clearF (titleF sized)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hborders, Option.map_some]
  exact ⟨_, hclear, by rw [(clearF_keys _).1]; exact hdT⟩

/-- Materialization preserves the cluster path at a non-dummy index. -/
private theorem matEndpointClusterPath {PREP : Proper} {e : Nat}
    {pm : ProperNode}
    (hprep : PREP.nodes[e]? = some pm) (hd : pm.dummy = false) :
    ((materializeDummyPaths PREP).nodes.getD e default).node.clusterPath =
      (PREP.nodes.getD e default).node.clusterPath := by
  have hmat : (materializeDummyPaths PREP).nodes[e]? = some pm := by
    simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
      hprep, Option.map_some, hd, Bool.false_eq_true, ↓reduceIte]
  have h1 : (materializeDummyPaths PREP).nodes.getD e default = pm := by
    simp [List.getD_eq_getElem?_getD, hmat]
  have h2 : PREP.nodes.getD e default = pm := by
    simp [List.getD_eq_getElem?_getD, hprep]
  rw [h1, h2]

/-- On a border-`0` coordinate node, `nodePath` unfolds to the cluster path.
For non-dummy nodes this is `nodePath_of_nondummy`; for dummy nodes it is
the `materializeDummyPaths` equation plus chain-endpoint stability: endpoints
are normalize-chain ends, hence non-dummy originals whose records survive
every stage to the prepared graph. -/
theorem plainNodePathEq : PlainNodePathEq := by
  intro P cg run labels orderOptions hrun v nd hlook hborder
  by_cases hd : nd.dummy = false
  · exact OrderImpl.nodePath_of_nondummy hlook hd
  · have hdT : nd.dummy = true := by
      cases h : nd.dummy with
      | false => exact absurd h hd
      | true => rfl
    obtain ⟨_, normalized, labeled, _, hnorm, hlabels, hcoord, _⟩ :=
      componentRun_ranked_source hrun
    have hcoordM : materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P
          labeled)) P.clusterBorderW)) = run.coordinateProper := by
      exact hcoord
    have hlookM : (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P
          labeled)) P.clusterBorderW))).nodes[v]? = some nd := by
      rw [hcoordM]; exact hlook
    obtain ⟨mp, hmp, hdm, _, _, _⟩ :=
      materialize_lookup (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW)) hlookM
    have hmpT : mp.dummy = true := hdm.symm.trans hdT
    have hpath : nd.node.clusterPath = OrderImpl.nodePath (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P
          labeled)) P.clusterBorderW)) v := by
      have h := hlookM
      simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
        hmp, Option.map_some, hmpT, ↓reduceIte, Option.some.injEq] at h
      rw [← h]
      simp only [Nat.zero_add]
    rw [← hcoordM, hpath]
    have hchains : (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P
          labeled)) P.clusterBorderW))).chains =
        (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPorts P labeled))
          P.clusterBorderW)).chains := rfl
    have hgetM : (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P
          labeled)) P.clusterBorderW))).nodes.getD v default = nd := by
      simp [List.getD_eq_getElem?_getD, hlookM]
    have hgetP : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW)).nodes.getD v default = mp := by
      simp [List.getD_eq_getElem?_getD, hmp]
    unfold OrderImpl.nodePath
    dsimp only
    rw [hgetM, hdT, hgetP, hmpT, hchains]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases hfind : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW)).chains.find? (fun chain => chain.contains v) with
    | none => rfl
    | some chain =>
      dsimp only
      have hmemC : v ∈ chain := by
        have hfv := List.find?_some hfind
        simpa only [List.contains_iff_mem] using hfv
      have hcmem : chain ∈ (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPorts P labeled))
          P.clusterBorderW)).chains := List.mem_of_find?_eq_some hfind
      have ePREP : (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPorts P labeled))
          P.clusterBorderW)).chains = labeled.chains :=
        (OrderImpl.addClusterBorders_metadata _ _).2.1
      have hcNorm : chain ∈ normalized.chains := by
        have h1 := hcmem
        rw [ePREP, (Labels.addLabelNodes_metadata hlabels).2.2.1] at h1
        exact h1
      obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hcNorm
      have hidxB : idx < cg.edges.length := by
        have hlt := (List.getElem?_eq_some_iff.mp hidx).1
        rwa [normalize_chains_length hnorm] at hlt
      obtain ⟨edge, hedge⟩ : ∃ e, cg.edges[idx]? = some e :=
        ⟨_, List.getElem?_eq_getElem hidxB⟩
      have hfact := (normalize_ok hnorm).2.2 idx hidxB edge hedge
      obtain ⟨hanchor, hrest⟩ := hfact
      have hwf : cg.wellformed = true := (normalize_node_rank_alignment hnorm).2
      have hedgeMem : edge ∈ cg.edges := List.mem_of_getElem? hedge
      have hbounds := RankImpl.wellformed_spec hwf edge hedgeMem
      obtain ⟨htailB, hheadB, _⟩ := hbounds
      by_cases hself : edge.tail = edge.head
      · simp only [hself, ↓reduceIte] at hrest
        have hempty : chain = [] := Option.some.inj (hidx.symm.trans hrest)
        rw [hempty] at hmemC
        simp at hmemC
      · simp only [hself, ↓reduceIte] at hrest
        obtain ⟨chl, hch, _, hhead, hlast, _⟩ := hrest
        have hcc : chl = chain := Option.some.inj (hch.symm.trans hidx)
        have hhead' : chain.head? = some edge.tail := by
          rw [← hcc]; exact hhead
        have hlast' : chain.getLast? = some edge.head := by
          rw [← hcc]; exact hlast
        have ehead : chain.headD v = edge.tail := by
          cases hc : chain with
          | nil => simp [hc] at hmemC
          | cons h t =>
            have h2 := hhead'; rw [hc] at h2
            simp only [List.head?_cons, Option.some.injEq] at h2
            exact h2
        have elast : chain.getLastD v = edge.head := by
          rw [List.getLastD_eq_getLast?, hlast', Option.getD_some]
        obtain ⟨nT, hnT⟩ : ∃ n, cg.nodes[edge.tail]? = some n :=
          ⟨_, List.getElem?_eq_getElem htailB⟩
        have hnormT : normalized.nodes[edge.tail]? =
            some ⟨nT, false, none, false⟩ :=
          normalize_node_record hnorm hnT
        have hlabT : labeled.nodes[edge.tail]? =
            some ⟨nT, false, none, false⟩ :=
          addLabelNodes_untouched_node hlabels hnormT rfl
        obtain ⟨pmT, hprepT, hdT2⟩ := preparedNondummyOfLabeled hlabT rfl
        obtain ⟨nH, hnH⟩ : ∃ n, cg.nodes[edge.head]? = some n :=
          ⟨_, List.getElem?_eq_getElem hheadB⟩
        have hnormH : normalized.nodes[edge.head]? =
            some ⟨nH, false, none, false⟩ :=
          normalize_node_record hnorm hnH
        have hlabH : labeled.nodes[edge.head]? =
            some ⟨nH, false, none, false⟩ :=
          addLabelNodes_untouched_node hlabels hnormH rfl
        obtain ⟨pmH, hprepH, hdH2⟩ := preparedNondummyOfLabeled hlabH rfl
        have hclH : ((materializeDummyPaths (clearProxyExtents
            (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P
              labeled)) P.clusterBorderW))).nodes.getD
            (chain.headD v) default).node.clusterPath =
            ((clearProxyExtents (OrderImpl.addClusterBorders
              (titleReservations (sizeProperPorts P labeled))
              P.clusterBorderW)).nodes.getD
              (chain.headD v) default).node.clusterPath := by
          rw [ehead]
          exact matEndpointClusterPath hprepT hdT2
        have hclL : ((materializeDummyPaths (clearProxyExtents
            (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P
              labeled)) P.clusterBorderW))).nodes.getD
            (chain.getLastD v) default).node.clusterPath =
            ((clearProxyExtents (OrderImpl.addClusterBorders
              (titleReservations (sizeProperPorts P labeled))
              P.clusterBorderW)).nodes.getD
              (chain.getLastD v) default).node.clusterPath := by
          rw [elast]
          exact matEndpointClusterPath hprepH hdH2
        rw [hclH, hclL]

/-- Closed form: same-side markers share one `x`-span with nonnegative right
edge, and a left marker lies left of the same-rank right marker. -/
theorem sideMarkerSpanAligned' (halign : ForeignBorderChainXAligned) :
    SideMarkerSpanAligned :=
  sideMarkerSpanAligned halign sideMarkerSamePath

/-- Closed form: a plain node off the group lies beyond the marker pair. -/
theorem plainClearOfSideMarker' : PlainClearOfSideMarker :=
  plainClearOfSideMarker sideMarkerSamePath plainNodePathEq

end Elegant.Layered.PipelineImpl

import Elegant.Layered.ForeignClusterFactsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Border construction residuals: anchor paths and rank-pair anchors.

This module discharges two of the three residuals of
`ForeignClusterFactsProof.lean`:

* `foreignBorderAnchorPaths`: every side marker of an executed run carries the
  cluster path of its own title, and each title path ends in its own
  declaration.  The side-marker half replays the `coordinateGraph` origin
  chase (`materialize_lookup`, `clearProxyExtents`, `addClusterBorders`) over
  the titled source; the title half is the measured-graph group origin.
* `foreignBorderLayerOrder'`: the seam field `ForeignBorderLayerOrder`,
  closed by applying `foreignBorderLayerOrder` to the anchor paths.
* `foreignRankPairAnchors`: the title-level anchor lookups backing the
  per-rank marker pairs, modulo one colocation hypothesis.

The remaining residual is `ForeignBorderSideUps` (the executed alignment
`up` behaviour on each declaration side-chain), which needs the deep
median-pick facts and is left open.
-/

/-- A side border emitted by `addClusterBorders` is non-dummy. -/
private theorem anchor_side_dummy {p : Proper} {bw : Int}
    (hready : OrderImpl.BorderConstructionReady p) {nd : ProperNode}
    (hmem : nd ∈ (OrderImpl.addClusterBorders p bw).nodes)
    (hs : nd.node.border = -1 ∨ nd.node.border = 1) : nd.dummy = false := by
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra p bw
  rw [hx] at hmem
  rcases List.mem_append.mp hmem with hp | he
  · rcases hs with hs1 | hs2
    · exact absurd hs1 (hready.1 nd hp).1
    · exact absurd hs2 (hready.1 nd hp).2
  · exact (hall nd he).1

/-- A side border of the coordinate graph carries a `-2` anchor path. -/
private theorem anchor_side_path {P : Params} {p t : Proper}
    (ht : t = titleReservations (sizeProperPorts P p))
    (hready : OrderImpl.BorderConstructionReady t)
    {v : Nat} {nd : ProperNode}
    (h : (coordinateGraph P p).nodes[v]? = some nd)
    (hs : nd.node.border = -1 ∨ nd.node.border = 1) :
    nd.dummy = false ∧
    ∃ m : ProperNode, m ∈ t.nodes ∧ m.node.border = -2 ∧
      nd.node.clusterPath = m.node.clusterPath := by
  unfold coordinateGraph at h
  rw [← ht] at h
  obtain ⟨m1, hm1, _, hb1, heq1⟩ := materialize_lookup _ h
  have hm1d : m1.dummy = false := by
    by_cases hc : m1.dummy = true
    · exfalso
      rw [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hm1
      obtain ⟨m2, hm2get, heq2⟩ := hm1
      have cm2 := clearF_keys m2
      have hm2b : m2.node.border = -1 ∨ m2.node.border = 1 := by
        rw [← cm2.2.1, heq2, ← hb1]; exact hs
      have hm2mem : m2 ∈ (OrderImpl.addClusterBorders t P.clusterBorderW).nodes :=
        List.mem_of_getElem? hm2get
      have hdummy : m2.dummy = false :=
        anchor_side_dummy hready hm2mem hm2b
      have hnd2 : m1.dummy = false := by
        rw [← heq2, cm2.1]; exact hdummy
      rw [hnd2] at hc
      exact absurd hc (by decide)
    · exact by simpa using hc
  rw [← heq1.2 hm1d] at hm1
  rw [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hm1
  obtain ⟨m2, hm2, heq2⟩ := hm1
  have cm2 := clearF_keys m2
  rw [heq2] at cm2
  have hm2b : m2.node.border = -1 ∨ m2.node.border = 1 := by
    rw [← cm2.2.1]; exact hs
  have hm2mem : m2 ∈ (OrderImpl.addClusterBorders t P.clusterBorderW).nodes :=
    List.mem_of_getElem? hm2
  have hndF : nd.dummy = false := by
    rw [cm2.1]; exact anchor_side_dummy hready hm2mem hm2b
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source t P.clusterBorderW hready hm2mem hm2b
  obtain ⟨tmem, hcond⟩ := List.mem_filter.mp htop
  have hget : t.nodes[top.2]? = some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp tmem
  refine ⟨hndF, top.1, List.mem_of_getElem? hget, ?_, cm2.2.2.1.trans hpath⟩
  simpa using hcond

/-- Bottom-marker colocation: the candidate component holding a group title
also holds the `border = 2` bottom marker with the same declaration and
cluster path.  The bottom record is emitted by `Compound.prepare` for every
group box, and the `Compound.constraints` edges link each title to its
declaration-matched bottom, so both land in one reported component; the
statement is pinned to the same three execution equations as the rank
residual that consumes it. -/
def ForeignBottomInCandidate : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u : Nat} {uNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    uNode.border = -2 →
    ∃ (iB : Nat) (bNode : Node),
      (componentCandidate graph comp candidate).nodes[iB]? = some bNode ∧
      bNode.border = 2 ∧ bNode.decl = uNode.decl ∧
      bNode.clusterPath = uNode.clusterPath

/-- Every side marker carries its title path; every title path ends in its
own declaration. -/
theorem foreignBorderAnchorPaths : ForeignBorderAnchorPaths := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions
    hrun u w uNode wNode hu hw hbU hbW _hne
  obtain ⟨_, _, hsrcU⟩ := componentCandidate_nonplain_source hu (by omega)
  obtain ⟨_, boxU, hboxU, _, hpathU⟩ :=
    measuredGraph_group_origin hgraph hsrcU hbU
  obtain ⟨_, _, hsrcW⟩ := componentCandidate_nonplain_source hw (by omega)
  obtain ⟨_, boxW, hboxW, _, hpathW⟩ :=
    measuredGraph_group_origin hgraph hsrcW hbW
  have hlastU : uNode.clusterPath.getLast? = some uNode.decl := by
    rw [hpathU, List.getLast?_append]; simp
  have hlastW : wNode.clusterPath.getLast? = some wNode.decl := by
    rw [hpathW, List.getLast?_append]; simp
  refine ⟨hlastU, hlastW, fun {a na} hna hside => ?_⟩
  obtain ⟨_, _, labeled, _, hn, hl, hcoord, _⟩ :=
    componentRun_ranked_source hrun
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
  rw [← hcoord] at hna
  obtain ⟨_, m, hmem, hmB, hpath⟩ :=
    anchor_side_path rfl hready hna hside
  obtain ⟨mindex, hmindex⟩ := List.mem_iff_getElem?.mp hmem
  rcases titled_node_origin hkeys hmindex with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hmB
    rcases hkeys mindex orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨_, _, hsrcG⟩ :=
        componentCandidate_nonplain_source hbn (by omega)
      obtain ⟨_, boxG, hboxG, _, hpathG⟩ :=
        measuredGraph_group_origin hgraph hsrcG hbnB
      have hlastG : bn.clusterPath.getLast? = some bn.decl := by
        rw [hpathG, List.getLast?_append]; simp
      have hnaLast : na.node.clusterPath.getLast? = some bn.decl := by
        rw [hpath, hpp, hnp]; exact hlastG
      constructor
      · intro ho
        have hdeclEq : bn.decl = uNode.decl :=
          Option.some.inj (hnaLast.symm.trans ho)
        rw [hdeclEq] at hboxG
        have hboxEq : boxG = boxU := Option.some.inj (hboxG.symm.trans hboxU)
        rw [hpath, hpp, hnp, hpathG, hdeclEq, hboxEq, hpathU]
      · intro ho
        have hdeclEq : bn.decl = wNode.decl :=
          Option.some.inj (hnaLast.symm.trans ho)
        rw [hdeclEq] at hboxG
        have hboxEq : boxG = boxW := Option.some.inj (hboxG.symm.trans hboxW)
        rw [hpath, hpp, hnp, hpathG, hdeclEq, hboxEq, hpathW]
    · rw [hb0] at horigB; omega
  · rw [hb3] at hmB; omega

/-- The seam field: border markers of unrelated declarations form disjoint
layer blocks. -/
theorem foreignBorderLayerOrder' : ForeignBorderLayerOrder :=
  foreignBorderLayerOrder foreignBorderAnchorPaths

/-- The title-level anchor lookups backing the per-rank marker pairs. -/
theorem foreignRankPairAnchors (hbot : ForeignBottomInCandidate) :
    ForeignRankPairAnchors := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions
    hrun u w uNode wNode hu hw hbU hbW _hne
  obtain ⟨rr, _, labeled, hrr, hn, hl, hcoord, _⟩ :=
    componentRun_ranked_source hrun
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hlenEq := titleReservations_node_rank_alignment P haligned
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hranks : ∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
      labeled.rank[index]? = some rank := by
    intro index rank hrank
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hrank
  have hnodeRec : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
      labeled.nodes[index]? = some (⟨node, false, none, false⟩ : ProperNode) :=
    fun index node hnode =>
      addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨_, _, hsrcU⟩ := componentCandidate_nonplain_source hu (by omega)
  obtain ⟨_, _, _, _, hpathU⟩ :=
    measuredGraph_group_origin hgraph hsrcU hbU
  obtain ⟨_, _, hsrcW⟩ := componentCandidate_nonplain_source hw (by omega)
  obtain ⟨_, _, _, _, hpathW⟩ :=
    measuredGraph_group_origin hgraph hsrcW hbW
  obtain ⟨iBU, bU, hBUlook, hBUbord, _hBUdecl, hBUpath⟩ :=
    hbot hgraph hcomp hrun hu hbU
  obtain ⟨iBW, bW, hBWlook, hBWbord, _hBWdecl, hBWpath⟩ :=
    hbot hgraph hcomp hrun hw hbW
  have hlabU : labeled.nodes[u]? =
      some (⟨uNode, false, none, false⟩ : ProperNode) :=
    hnodeRec u uNode hu
  have hlabW : labeled.nodes[w]? =
      some (⟨wNode, false, none, false⟩ : ProperNode) :=
    hnodeRec w wNode hw
  have hlabBU : labeled.nodes[iBU]? =
      some (⟨bU, false, none, false⟩ : ProperNode) :=
    hnodeRec iBU bU hBUlook
  have hlabBW : labeled.nodes[iBW]? =
      some (⟨bW, false, none, false⟩ : ProperNode) :=
    hnodeRec iBW bW hBWlook
  have htopU : (titleReservations (sizeProperPorts P labeled)).nodes[u]? =
      some (titleF (⟨uNode, false, none, false⟩ : ProperNode)) :=
    titled_marker_record hlabU (Or.inl hbU)
  have htopW : (titleReservations (sizeProperPorts P labeled)).nodes[w]? =
      some (titleF (⟨wNode, false, none, false⟩ : ProperNode)) :=
    titled_marker_record hlabW (Or.inl hbW)
  have hbotTU : (titleReservations (sizeProperPorts P labeled)).nodes[iBU]? =
      some (titleF (⟨bU, false, none, false⟩ : ProperNode)) :=
    titled_marker_record hlabBU (Or.inr hBUbord)
  have hbotTW : (titleReservations (sizeProperPorts P labeled)).nodes[iBW]? =
      some (titleF (⟨bW, false, none, false⟩ : ProperNode)) :=
    titled_marker_record hlabBW (Or.inr hBWbord)
  have htopUmem : (titleF (⟨uNode, false, none, false⟩ : ProperNode), u) ∈
      (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopU
  have htopWmem : (titleF (⟨wNode, false, none, false⟩ : ProperNode), w) ∈
      (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopW
  have hbUtop : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.border
      = -2 := by
    rw [(titleF_keys _).2.1]; exact hbU
  have hbWtop : (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.border
      = -2 := by
    rw [(titleF_keys _).2.1]; exact hbW
  have hlastTopU : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath.getLast?
      = some uNode.decl := by
    rw [show (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath
      = uNode.clusterPath from (titleF_keys _).2.2.1,
      hpathU, List.getLast?_append]
    simp
  have hlastTopW : (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath.getLast?
      = some wNode.decl := by
    rw [show (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath
      = wNode.clusterPath from (titleF_keys _).2.2.1,
      hpathW, List.getLast?_append]
    simp
  have hmemBU : (titleF (⟨bU, false, none, false⟩ : ProperNode), iBU) ∈
      (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hbotTU
  have hmemBW : (titleF (⟨bW, false, none, false⟩ : ProperNode), iBW) ∈
      (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hbotTW
  have hpredBU : (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
      entry.1.node.clusterPath ==
        (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath)
      (titleF (⟨bU, false, none, false⟩ : ProperNode), iBU) = true := by
    have e1 : (titleF (⟨bU, false, none, false⟩ : ProperNode)).node.border
        = 2 := by
      rw [(titleF_keys _).2.1]; exact hBUbord
    have e2 : (titleF (⟨bU, false, none, false⟩ : ProperNode)).node.clusterPath
        = (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath := by
      rw [show (titleF (⟨bU, false, none, false⟩ : ProperNode)).node.clusterPath
        = bU.clusterPath from (titleF_keys _).2.2.1,
        show (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath
        = uNode.clusterPath from (titleF_keys _).2.2.1, hBUpath]
    show ((titleF (⟨bU, false, none, false⟩ : ProperNode)).node.border == 2 &&
      (titleF (⟨bU, false, none, false⟩ : ProperNode)).node.clusterPath ==
        (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath)
      = true
    simp [e1, e2]
  have hpredBW : (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
      entry.1.node.clusterPath ==
        (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath)
      (titleF (⟨bW, false, none, false⟩ : ProperNode), iBW) = true := by
    have e1 : (titleF (⟨bW, false, none, false⟩ : ProperNode)).node.border
        = 2 := by
      rw [(titleF_keys _).2.1]; exact hBWbord
    have e2 : (titleF (⟨bW, false, none, false⟩ : ProperNode)).node.clusterPath
        = (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath := by
      rw [show (titleF (⟨bW, false, none, false⟩ : ProperNode)).node.clusterPath
        = bW.clusterPath from (titleF_keys _).2.2.1,
        show (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath
        = wNode.clusterPath from (titleF_keys _).2.2.1, hBWpath]
    show ((titleF (⟨bW, false, none, false⟩ : ProperNode)).node.border == 2 &&
      (titleF (⟨bW, false, none, false⟩ : ProperNode)).node.clusterPath ==
        (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath)
      = true
    simp [e1, e2]
  obtain ⟨botU, hbotU⟩ : ∃ x,
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath))
        = some x := by
    cases h : ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath)) with
    | none =>
      have hnone := (List.find?_eq_none.mp h) _ hmemBU
      simp [hpredBU] at hnone
    | some x => exact ⟨x, rfl⟩
  obtain ⟨botW, hbotW⟩ : ∃ x,
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath))
        = some x := by
    cases h : ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath)) with
    | none =>
      have hnone := (List.find?_eq_none.mp h) _ hmemBW
      simp [hpredBW] at hnone
    | some x => exact ⟨x, rfl⟩
  refine ⟨labeled, rr, hcoord, haligned, hkeys, hrr, hranks, hnodeRec, hlenEq,
    (titleF (⟨uNode, false, none, false⟩ : ProperNode), u), botU,
    htopUmem, hbUtop, hlastTopU, hbotU,
    (titleF (⟨wNode, false, none, false⟩ : ProperNode), w), botW,
    htopWmem, hbWtop, hlastTopW, hbotW⟩


end Elegant.Layered.PipelineImpl

import Elegant.Layered.DivergeSweepSeedStepProof
import Elegant.Layered.SideMarkerTopInCandidateProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem executedSidePath {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {opts : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels opts = .ok run)
    {v : Nat} {node : ProperNode} (hnode : run.coordinateProper.nodes[v]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    ∃ (owner : Nat) (box : ModelBox), inp.boxes[owner]? = some box ∧
      node.node.clusterPath = Compound.path inp.boxes box ++ [owner] := by
  obtain ⟨_, labeled, _, hcoord, hkeys, hready, hrecords, _⟩ :=
    componentRun_prepared_titled_source hgraph hcomp hrun
  rw [← hcoord] at hnode
  have hraw := coordinateGraph_side_original hready hnode hside
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hraw) hside
  obtain ⟨htopMem, htopBorder⟩ := List.mem_filter.mp htop
  have htopLeft : top.1.node.border = -2 := by simpa using htopBorder
  obtain ⟨original, hcandidate, hborder, hrecord⟩ := titled_marker_source_record hkeys hrecords
    (List.mem_zipIdx_iff_getElem?.mp htopMem) (Or.inl htopLeft)
  have horiginalBorder := hborder.symm.trans htopLeft
  obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hcandidate (by omega)
  obtain ⟨_, mapped, hmapped, _, hcanonical⟩ :=
    measuredGraph_group_origin hgraph hsource horiginalBorder
  rw [List.getElem?_map] at hmapped
  obtain ⟨box, hbox, hmap⟩ := Option.map_eq_some_iff.mp hmapped
  obtain ⟨_, _, hfixedPath⟩ := fixedSizes_path_index inp hbox
  refine ⟨original.decl, box, hbox, ?_⟩
  rw [hpath, hrecord, (titleF_keys _).2.2.1, hcanonical, ← hmap, hfixedPath]

private theorem ownerOfPathPrefix {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {pref : List Nat} {decl : Nat} (revSuffix : List Nat) {owner : Nat} {box : ModelBox}
    (hbox : inp.boxes[owner]? = some box)
    (hpath : Compound.path inp.boxes box ++ [owner] = pref ++ decl :: revSuffix.reverse) :
    ∃ group : ModelBox, inp.boxes[decl]? = some group ∧ Compound.path inp.boxes group = pref := by
  induction revSuffix generalizing owner box with
  | nil =>
    have hdecl : owner = decl := by simpa using congrArg List.getLast? hpath
    subst owner
    exact ⟨box, hbox, by simpa using congrArg List.dropLast hpath⟩
  | cons last revSuffix ih =>
    have hshape : pref ++ decl :: (last :: revSuffix).reverse =
        (pref ++ decl :: revSuffix.reverse) ++ [last] := by
      rw [List.reverse_cons, List.append_assoc, List.cons_append]
    have hshort : Compound.path inp.boxes box = pref ++ decl :: revSuffix.reverse := by
      simpa only [List.dropLast_concat] using congrArg List.dropLast (hpath.trans hshape)
    have hparent : box.parent ≠ "" := by
      intro hroot
      have hempty : Compound.path inp.boxes box = [] := by
        unfold Compound.path
        rw [hroot]
        cases inp.boxes.length <;> rfl
      have hmem : decl ∈ Compound.path inp.boxes box := by
        rw [hshort]
        exact List.mem_append_right _ List.mem_cons_self
      simp [hempty] at hmem
    obtain ⟨parent, hmem, hid, _, _⟩ :=
      framedParents_parent hframed (List.mem_of_getElem? hbox) hparent
    obtain ⟨_, hparentBox⟩ := List.mem_iff_getElem?.mp hmem
    have hstep := Compound.path_of_parent (inputModel inp o) hwf hparentBox hbox hid.symm hparent
    exact ih hparentBox (hstep.symm.trans hshort)

private theorem executedLeftMarkerOfPrefix {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph) (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {opts : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels opts = .ok run)
    {v : Nat} {node : ProperNode} (hnode : run.coordinateProper.nodes[v]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1)
    {pref : List Nat} {decl : Nat} {tail : List Nat}
    (hpath : node.node.clusterPath = pref ++ decl :: tail) :
    ∃ (left : Nat) (marker : ProperNode), run.coordinateProper.nodes[left]? = some marker ∧
      marker.node.border = -1 ∧ marker.node.clusterPath = pref ++ [decl] := by
  obtain ⟨_, box, hbox, hownerPath⟩ := executedSidePath hgraph hcomp hrun hnode hside
  obtain ⟨group, hgroup, hgroupPath⟩ := ownerOfPathPrefix hwf hframed (pref := pref)
    (decl := decl) tail.reverse hbox
    (by simpa only [List.reverse_reverse] using hownerPath.symm.trans hpath)
  have hproper := (componentRun_nonproxy_record hrun hnode (by rcases hside <;> omega)).1
  have hcontains : node.node.clusterPath.contains decl = true := by
    rw [hpath]
    exact List.contains_iff_mem.mpr (List.mem_append_right _ List.mem_cons_self)
  obtain ⟨left, _, marker, _, hleft, hborder, hlast, _⟩ :=
    bracketMarkersAtRank' hgraph hlines hwf hframed hcomp hrun
      (rk run.proper.rank v).toNat hproper hcontains (Nat.le_refl _)
      hproper hcontains (Nat.le_refl _)
  obtain ⟨owner, leftBox, hleftBox, hleftPath⟩ :=
    executedSidePath hgraph hcomp hrun hleft (Or.inl hborder)
  have hdecl : owner = decl := by simpa [hleftPath] using hlast
  subst owner
  have hboxEq : leftBox = group := Option.some.inj (hleftBox.symm.trans hgroup)
  exact ⟨left, marker, hleft, hborder, by rw [hleftPath, hboxEq, hgroupPath]⟩

theorem componentRun_framed_marker_heads {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph) (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {opts : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels opts = .ok run)
    {idxA idxB : Nat} {nodeA nodeB : ProperNode}
    (hnodeA : run.coordinateProper.nodes[idxA]? = some nodeA)
    (hnodeB : run.coordinateProper.nodes[idxB]? = some nodeB)
    (hsideA : nodeA.node.border = -1 ∨ nodeA.node.border = 1)
    (hsideB : nodeB.node.border = -1 ∨ nodeB.node.border = 1)
    {pref : List Nat} {A B : Nat} {tailA tailB : List Nat}
    (hA : nodeA.node.clusterPath = pref ++ A :: tailA)
    (hB : nodeB.node.clusterPath = pref ++ B :: tailB) :
    A ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
    B ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
    OrderImpl.Sibling.parentOf run.coordinateProper A =
      OrderImpl.Sibling.parentOf run.coordinateProper B := by
  have hfunctional : OrderImpl.ClusterPathsFunctional run.coordinateProper := by
    intro a b na nb hna hnb ha hb hlast
    obtain ⟨ownerA, boxA, hboxA, hpathA⟩ := executedSidePath hgraph hcomp hrun hna (Or.inl ha)
    obtain ⟨ownerB, boxB, hboxB, hpathB⟩ := executedSidePath hgraph hcomp hrun hnb (Or.inl hb)
    have howner : ownerA = ownerB := by simpa [hpathA, hpathB] using hlast
    subst ownerB
    have hboxEq : boxA = boxB := Option.some.inj (hboxA.symm.trans hboxB)
    rw [hpathA, hpathB, hboxEq]
  obtain ⟨_, _, hleftA, hbA, hprefixA⟩ :=
    executedLeftMarkerOfPrefix hgraph hlines hwf hframed hcomp hrun hnodeA hsideA hA
  obtain ⟨_, _, hleftB, hbB, hprefixB⟩ :=
    executedLeftMarkerOfPrefix hgraph hlines hwf hframed hcomp hrun hnodeB hsideB hB
  have hparentA := OrderImpl.parentOf_eq hfunctional hleftA hbA hprefixA
  have hparentB := OrderImpl.parentOf_eq hfunctional hleftB hbB hprefixB
  exact ⟨OrderImpl.clusterIds_mem hleftA hbA hprefixA,
    OrderImpl.clusterIds_mem hleftB hbB hprefixB, hparentA.trans hparentB.symm⟩

theorem divergeSeedExecuted_holds {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph) (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {opts : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels opts = .ok run) :
    DivergeChainAgree run.coordinateProper (OrderImpl.seedBest run.coordinateProper opts.start) := by
  intro k1 k2 l1 l2 hk1 hk2 a b a' b' na nb na' nb' hna hnb ha hb hna' hnb'
    ha' hb' _ _ _ _ hpathA hpathB pref A B tailA tailB hA hB hAB i j i' j' hi hj hi' hj'
  obtain ⟨hmA, hmB, hparent⟩ :=
    componentRun_framed_marker_heads hgraph hlines hwf hframed hcomp hrun hna hnb ha hb hA hB
  exact divergeSeedAgree_holds hgraph hcomp hrun hk1 hk2 hna hnb ha hb hna' hnb' ha' hb'
    hpathA hpathB hA hB hAB hmA hmB hparent hi hj hi' hj'

end Elegant.Layered.PipelineImpl

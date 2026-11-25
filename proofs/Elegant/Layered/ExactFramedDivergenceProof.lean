import Elegant.Layered.ExactBorderDivergeProof
import Elegant.Layered.ExactSideMarkerFactsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem inputBoxAtPathHead {inp : Input} {o : Options}
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

theorem X_foreignBorderDivergeStableFramed_holds {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraph : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length) (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true) {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {opts : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate)
      labels opts = .ok run) : X_ForeignBorderDivergeStableRun run := by
  have sidePath : ∀ {v : Nat} {node : ProperNode},
      run.coordinateProper.nodes[v]? = some node →
      (node.node.border = -1 ∨ node.node.border = 1) →
      ∃ (owner : Nat) (box : ModelBox), inp.boxes[owner]? = some box ∧
        node.node.clusterPath = Compound.path inp.boxes box ++ [owner] := by
    obtain ⟨_, _, _, hcoord, hkeys, hready, hrecords, _, _⟩ :=
      X_cg_run_bundle hgraph0 hgraph hcomp hrun
    intro v node hnode hside
    rw [← hcoord] at hnode
    have hraw := X_side_original hready hnode hside
    obtain ⟨top, htop, _, _, hpath⟩ :=
      addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hraw) hside
    obtain ⟨htopMem, htopBorder⟩ := List.mem_filter.mp htop
    have htopLeft : top.1.node.border = -2 := by simpa using htopBorder
    obtain ⟨original, hcandidate, hborder, hrecord⟩ :=
      X_titled_marker_source_record hkeys hrecords
        (List.mem_zipIdx_iff_getElem?.mp htopMem) (Or.inl htopLeft)
    obtain ⟨box, hbox, hownerPath⟩ :=
      X_cg_group_box hgraph0 hgraph hcandidate (hborder.symm.trans htopLeft)
    refine ⟨original.decl, box, hbox, ?_⟩
    rw [hpath, hrecord, (titleF_keys _).2.2.1, hownerPath]
  have hfunctional : OrderImpl.ClusterPathsFunctional run.coordinateProper := by
    intro a b na nb hna hnb ha hb hlast
    obtain ⟨ownerA, boxA, hboxA, hpathA⟩ := sidePath hna (Or.inl ha)
    obtain ⟨ownerB, boxB, hboxB, hpathB⟩ := sidePath hnb (Or.inl hb)
    have howner : ownerA = ownerB := by simpa [hpathA, hpathB] using hlast
    subst ownerB
    have hboxEq : boxA = boxB := Option.some.inj (hboxA.symm.trans hboxB)
    rw [hpathA, hpathB, hboxEq]
  have leftMarkerOfPrefix : ∀ {v : Nat} {node : ProperNode},
      run.coordinateProper.nodes[v]? = some node →
      (node.node.border = -1 ∨ node.node.border = 1) →
      ∀ {pref : List Nat} {decl : Nat} {tail : List Nat},
        node.node.clusterPath = pref ++ decl :: tail →
        ∃ (left : Nat) (marker : ProperNode), run.coordinateProper.nodes[left]? = some marker ∧
          marker.node.border = -1 ∧ marker.node.clusterPath = pref ++ [decl] := by
    intro v node hnode hside pref decl tail hpath
    obtain ⟨_, box, hbox, hownerPath⟩ := sidePath hnode hside
    obtain ⟨group, hgroup, hgroupPath⟩ := inputBoxAtPathHead hwf hframed (pref := pref)
      (decl := decl) tail.reverse hbox
      (by simpa only [List.reverse_reverse] using hownerPath.symm.trans hpath)
    obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
    have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
      rcases hside with hb | hb <;> omega
    have hproper : run.proper.nodes[v]? = some node := by
      rw [← hdrop]
      exact ((proxyWidths_rel hproxy).2.2.2.2.2 v node hnode hnotProxy).1
    have hcontains : node.node.clusterPath.contains decl = true := by
      rw [hpath]
      exact List.contains_iff_mem.mpr (List.mem_append_right _ List.mem_cons_self)
    obtain ⟨left, _, marker, _, hleft, hleftBorder, hlast, _⟩ :=
      XN_bracketMarkersAtRank_holds exactIds hgraph0 hgraph hlines hwf hframed hcomp hrun
        (rk run.proper.rank v).toNat hproper hcontains (Nat.le_refl _)
        hproper hcontains (Nat.le_refl _)
    obtain ⟨owner, leftBox, hleftBox, hleftPath⟩ := sidePath hleft (Or.inl hleftBorder)
    have hdecl : owner = decl := by simpa [hleftPath] using hlast
    subst owner
    have hboxEq : leftBox = group := Option.some.inj (hleftBox.symm.trans hgroup)
    exact ⟨left, marker, hleft, hleftBorder, by rw [hleftPath, hboxEq, hgroupPath]⟩
  intro l1 l2 hl1 hl2 a b a' b' na nb na' nb' hna hnb ha hb hna' hnb' ha' hb'
    hpathA hpathB hdiv i j i' j' hi hj hi' hj'
  refine X_foreignBorderDivergeStableSeparated_holds exactIds hgraph0 hgraph hcomp hrun hl1 hl2
    hna hnb ha hb hna' hnb' ha' hb' hpathA hpathB hdiv ?_ hi hj hi' hj'
  intro pref A B tailA tailB hA hB _
  obtain ⟨_, _, hleftA, hbA, hprefixA⟩ := leftMarkerOfPrefix hna ha hA
  obtain ⟨_, _, hleftB, hbB, hprefixB⟩ := leftMarkerOfPrefix hnb hb hB
  have hparentA := OrderImpl.parentOf_eq hfunctional hleftA hbA hprefixA
  have hparentB := OrderImpl.parentOf_eq hfunctional hleftB hbB hprefixB
  exact ⟨OrderImpl.clusterIds_mem hleftA hbA hprefixA,
    OrderImpl.clusterIds_mem hleftB hbB hprefixB, hparentA.trans hparentB.symm⟩

end Elegant.Layered.PipelineImpl

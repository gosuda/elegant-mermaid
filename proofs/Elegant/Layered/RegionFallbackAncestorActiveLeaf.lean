import Elegant.Layered.RegionFallbackAncestorAllocation
import Elegant.Layered.RegionFallbackAncestorFrameSides
import Elegant.Layered.RegionFallbackAncestorRanks

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem selectedParentTop
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} {s : RegionSpec} {cand u parentKey : Nat}
    {child parent : ModelBox} (hchild : child ∈ inp.boxes)
    (hparent : inp.boxes[parentKey]? = some parent) (href : child.parent = parent.id)
    (hne : child.parent ≠ "") (hu : comp[u]? = some parentKey) :
    ∃ top, (componentCandidateR (some s) e.graph comp cand).nodes[u]? = some top ∧
      top.border = -2 ∧ top.decl = parentKey := by
  obtain ⟨p, hp, hid, hrole, hfixed⟩ := framedParents_parent hfp hchild hne
  have he : p = parent := eq_of_mem_id (Model.boxIds_nodup hwf) hp
    (List.mem_of_getElem? hparent) (hid.trans href)
  subst p
  have heffective : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box)[parentKey]? = some parent := by
    simp only [List.getElem?_map, hparent, Option.map_some, hfixed, Bool.false_eq_true, ↓reduceIte]
  have hlen : parentKey < e.lines.length := by
    rw [boxLines_length e.lines_eq]
    exact (List.getElem?_eq_some_iff.mp hparent).1
  obtain ⟨raw, _, hraw, _, hb, _, hd, _, _, _, _, _⟩ :=
    measuredGraph_paired_markers e.graph0_eq hlen heffective hrole
  obtain ⟨top, ht, htBorder, _, htDecl⟩ := exactGraph_node_key e.graph_eq hraw
  exact ⟨top, component_node_lookupR hu ht, htBorder.trans hb, htDecl.trans hd⟩

/-- An active component's selected border-zero member lies strictly inside its
actual direct parent frame, including a fixed-size demoted group or zero-size member. -/
theorem regionActiveSelectedDirectLeaf_strict
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {s : RegionSpec} {index : Nat} {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) e.graph comp index) e.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) e.params inp
      (componentCandidateR (some s) e.graph comp index) = .ok (some rm))
    {u v parentKey key : Nat} {member : Node} {ps cs : ModelBox}
    (hu : comp[u]? = some parentKey) (hv : comp[v]? = some key)
    (hmember : (componentCandidateR (some s) e.graph comp index).nodes[v]? = some member)
    (hplain : member.border = 0)
    (hps : inp.boxes[parentKey]? = some ps) (hcs : inp.boxes[key]? = some cs)
    (href : cs.parent = ps.id) (hnonroot : cs.parent ≠ "") :
    (frameRect e.params cg run u).StrictInside (frameRect e.params cg run v) := by
  obtain ⟨top, htop, hgroup, htDecl⟩ := selectedParentTop (s := s) (cand := index)
    e hwf hfp (List.mem_of_getElem? hcs) hps href hnonroot hu
  obtain ⟨_, _, _, _, _, _, _, _, hrank, hnorm, hlabels, hcoord, hmin, _, ⟨st⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes := rankEquivalentR_nodes_eq hrank
  have ht : cg.nodes[u]? = some top := by rwa [hnodes]
  have hm : cg.nodes[v]? = some member := by rwa [hnodes]
  have hpath := active_candidate_plain_source_path e hcomp hmember hplain hv hcs
  have hstep := Compound.path_of_parent (inputModel inp o) hwf hps hcs href hnonroot
  change Compound.path inp.boxes cs = Compound.path inp.boxes ps ++ [parentKey] at hstep
  have hmemberPath : member.clusterPath = Compound.path inp.boxes ps ++ [top.decl] := by
    rw [hpath, hstep, htDecl]
  have hlast : member.clusterPath.getLast? = some top.decl := by
    rw [hmemberPath, List.getLast?_append]
    simp
  obtain ⟨owner, cluster, howner, hcluster, hdecl⟩ := active_candidate_top_cluster hactive htop hgroup
  have hownerBound := (List.getElem?_eq_some_iff.mp hcluster).1
  obtain ⟨bucket, _, hbucket, _, hleft, hright⟩ :=
    st.activePlain_frame_in_ownerBucket hrun hactive hrank hnorm hlabels hcoord hmin hm hplain
  rw [hlast] at hbucket
  change clusterOfDecl rm top.decl = some bucket at hbucket
  have he : bucket = owner := Option.some.inj (hbucket.symm.trans howner)
  subst bucket
  have hownerPlacement : owner < st.placement.rm.clusters.length := by rwa [st.hPlacement]
  have hnotRoot := Nat.ne_of_lt hownerPlacement
  simp only [groupPlain_bucketRight, groupPlain_bucketLeft, groupPlain_allocLeft,
    ite_eq_right hnotRoot] at hleft hright
  obtain ⟨hleftInset, hrightInset, _⟩ :=
    st.active_directAllocationInsets e.checked hrun hactive hmin owner hownerBound
  have hcover := st.activeGroup_frame_covers_reservation e.graph0_eq e.graph_eq hcomp
    hrun hactive hrank hnorm hlabels hcoord e.checked hcluster ht hgroup hdecl.symm
  dsimp only at hcover
  rw [← groupPlain_allocation_width_eq st.hAllocation] at hcover
  have hx : (frameRect e.params cg run u).x < (frameRect e.params cg run v).x ∧
      (frameRect e.params cg run v).x + (frameRect e.params cg run v).w <
        (frameRect e.params cg run u).x + (frameRect e.params cg run u).w :=
    ⟨by omega, by omega⟩
  have hexactNodes : (componentCandidate e.graph comp index).nodes =
      (componentCandidateR (some s) e.graph comp index).nodes := by
    rw [componentCandidate_nodes] <;> rfl
  have htopExact : (componentCandidate e.graph comp index).nodes[u]? = some top := by
    rwa [hexactNodes]
  obtain ⟨bottom, hbottom⟩ := X_componentRun_cg_bottom_find e.graph0_eq e.graph_eq
    (boxLines_length e.lines_eq) hcomp htopExact hgroup
  have hbotKey : bottom.1.border = 2 ∧ bottom.1.decl = top.decl := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hbottom
  obtain ⟨_, _, hbottomPath⟩ := X_cg_bottom_box e.graph0_eq e.graph_eq
    (List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hbottom)) hbotKey.1
  obtain ⟨_, _, htopPath⟩ := X_cg_group_box e.graph0_eq e.graph_eq htopExact hgroup
  have htopContains : top.clusterPath.contains top.decl = true := by rw [htopPath]; simp
  have hbottomContains : bottom.1.clusterPath.contains top.decl = true := by
    rw [hbottomPath, hbotKey.2]
    simp
  have hmemberContains : member.clusterPath.contains top.decl = true := by rw [hmemberPath]; simp
  have hbottomRun : (cg.nodes.zipIdx.find? (fun q =>
      q.1.border == 2 && q.1.decl == top.decl)) = some bottom := by
    rw [hnodes, ← hexactNodes]
    exact hbottom
  obtain ⟨hyLo, hyHi⟩ := componentRunR_active_leaf_strictVertical (exactIds := exactIds)
    hrun hactive (top := (top, u)) (member := (member, v)) ht hgroup hbottomRun hm hplain
    htopContains hbottomContains hmemberContains
  exact ⟨hx.1, hx.2, hyLo, hyHi⟩

end Elegant.Layered.PipelineImpl


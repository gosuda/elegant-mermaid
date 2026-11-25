import Elegant.Layered.RegionForwardAnchorOrigin
import Elegant.Layered.RegionForwardChildGeometry
import Elegant.Layered.NormalizeDummyOwnership

set_option autoImplicit false
set_option maxHeartbeats 6000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem r8b_resolvedLast_eq {rm : ComponentRegions} {path : List Nat} {owner : Nat}
    (h : match path.getLast? with
      | none => owner = rm.clusters.length
      | some d => clusterOfDecl rm d = some owner) :
    ((path.map fun d => (clusterOfDecl rm d).getD rm.clusters.length).getLast?).getD
      rm.clusters.length = owner := by
  rw [List.getLast?_map]
  cases hl : path.getLast? with
  | none =>
    have he : owner = rm.clusters.length := by simpa only [hl] using h
    exact he.symm
  | some d =>
    have he : clusterOfDecl rm d = some owner := by simpa only [hl] using h
    simp only [Option.map_some, he, Option.getD_some]

theorem r8b_forward_anchor_chain_path {P : Params} {exact : List Nat} {s : RegionSpec}
    {cg : Graph} {ranks : List Int} {p0 labeled p : Proper} {labels : List MeasuredLabel}
    (hnorm : normalize cg ranks = .ok p0)
    (hlab : Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled)
    (hcoord : coordinateGraphR P exact (some s) labeled = p)
    {edge v : Nat} {e : Edge} {nd old prepared : ProperNode} {tail head : Node}
    (he : cg.edges[edge]? = some e) (hTail : cg.nodes[e.tail]? = some tail)
    (hHead : cg.nodes[e.head]? = some head) (hn : p.nodes[v]? = some nd)
    (ho : p0.nodes[v]? = some old) (hok : old.edge = some edge) (hod : old.dummy = true)
    (hp : (r8bForwardPrepared P exact s labeled).nodes[v]? = some prepared)
    (hpd : prepared.dummy = true)
    (hchains : (r8bForwardPrepared P exact s labeled).chains = p0.chains) :
    v ∈ (p0.chains[edge]?).getD [] ∧
      nd.node.clusterPath = OrderImpl.commonPath tail.clusterPath head.clusterPath := by
  obtain ⟨nt, ht, _, htp⟩ := r8b_forwardPrepared_endpoint P exact s hnorm hlab hTail
  obtain ⟨nh, hh, _, hhp⟩ := r8b_forwardPrepared_endpoint P exact s hnorm hlab hHead
  have hmat := DummyOwnership.materialize_normalized_dummy_path
    hnorm hchains ho hod hok hp hpd he
  change (coordinateGraphR P exact (some s) labeled).nodes[v]? = _ at hmat
  rw [hcoord] at hmat
  refine ⟨(DummyOwnership.normalize_dummy_chain_iff hnorm ho hod).mpr hok, ?_⟩
  have hBt : ((r8bForwardPrepared P exact s labeled).nodes.getD e.tail default).node.clusterPath =
      tail.clusterPath := by simpa only [List.getD_eq_getElem?_getD, ht, Option.getD_some] using htp
  have hBh : ((r8bForwardPrepared P exact s labeled).nodes.getD e.head default).node.clusterPath =
      head.clusterPath := by simpa only [List.getD_eq_getElem?_getD, hh, Option.getD_some] using hhp
  rw [hBt, hBh, hn] at hmat
  exact congrArg (fun n : ProperNode => n.node.clusterPath) (Option.some.inj hmat)

theorem regionC8b_forwardAnchorBucketTrace_actual (exactIds : List String)
    (idSets : List (String × List String)) : R8b_ForwardAnchorBucketTrace exactIds idSets := by
  intro inp o res execution part selected hwf hframed hcomp s rm ranks budget
    p0 labeled p minimum ord reserved hspec hactive hrank hnorm hlab hcoord hmin _hord
    stages edge v e nd he _hne _hforward hanchor hnode
  have hrun := selected.run_eq
  rw [hspec] at hrun
  obtain ⟨hpre, hb, hx, _, _, _, old, prepared, ho, hok, hod, hp, hpd, hchains⟩ :=
    componentRunR_selectedAnchor_origin hrun hactive hrank hnorm hlab hcoord stages hanchor hnode
  have hbounds := RankImpl.wellformed_spec (normalize_node_rank_alignment hnorm).2 e
    (List.mem_of_getElem? he)
  let tail := selected.cg.nodes[e.tail]'hbounds.1
  let head := selected.cg.nodes[e.head]'hbounds.2.1
  have hTail : selected.cg.nodes[e.tail]? = some tail := List.getElem?_eq_getElem hbounds.1
  have hHead : selected.cg.nodes[e.head]? = some head := List.getElem?_eq_getElem hbounds.2.1
  have hpath := (r8b_forward_anchor_chain_path hnorm hlab hcoord he hTail hHead hpre
    ho hok hod hp hpd hchains).2
  have hparents := activeRegion_parent_count hactive
  have hchildren := (stages.group_paths hparents hmin).1
  have hnodeOwner {i : Nat} {raw : Node} (hi : selected.cg.nodes[i]? = some raw) :
      ∃ owner, stages.groups[i]? = some owner ∧
        ((raw.clusterPath.map fun d => (clusterOfDecl rm d).getD rm.clusters.length).getLast?).getD
          rm.clusters.length = owner ∧
        GroupPlainRootedPath stages.placement
          (fun d => (clusterOfDecl rm d).getD rm.clusters.length) rm.clusters.length raw.clusterPath := by
    obtain ⟨pn, _, hpn, hPnPath⟩ := r8b_forwardPrepared_endpoint execution.params
      (exactDecls exactIds inp) s hnorm hlab hi
    rw [hcoord] at hpn
    obtain ⟨owner, hlookup, _, hOwner⟩ := groupPlain_nodeGroups_lookup stages.hGroups hpn
    rw [hPnPath] at hOwner
    have hi' := hi
    rw [rankEquivalentR_nodes_eq hrank] at hi'
    exact ⟨owner, hlookup, r8b_resolvedLast_eq hOwner,
      r8b_executed_endpoint_rooted execution hwf hframed hcomp hactive stages hmin hi' hOwner⟩
  obtain ⟨t, ht, htt, htroot⟩ := hnodeOwner hTail
  obtain ⟨h, hh, hhh, hhroot⟩ := hnodeOwner hHead
  obtain ⟨hlt, htBound⟩ := r8b_executed_rooted_path_bounds stages hparents hmin htroot
  obtain ⟨hlh, _⟩ := r8b_executed_rooted_path_bounds stages hparents hmin hhroot
  have hinj {d a : Nat} (hd : d ∈ tail.clusterPath)
      (heq : (clusterOfDecl rm d).getD rm.clusters.length =
        (clusterOfDecl rm a).getD rm.clusters.length) : d = a :=
    r8b_executed_resolver_injective (htBound d hd) heq
  have hta : stages.groups.getD e.tail rm.clusters.length =
      ((tail.clusterPath.map fun d => (clusterOfDecl rm d).getD rm.clusters.length).getLast?).getD
        rm.clusters.length := by simpa only [List.getD_eq_getElem?_getD, ht, Option.getD_some] using htt.symm
  have hha : stages.groups.getD e.head rm.clusters.length =
      ((head.clusterPath.map fun d => (clusterOfDecl rm d).getD rm.clusters.length).getLast?).getD
        rm.clusters.length := by simpa only [List.getD_eq_getElem?_getD, hh, Option.getD_some] using hhh.symm
  have hEdgeOwner := forward_edgeOwner_of_decl_paths hchildren htroot hhroot hlt hlh
    (fun _ hd _ _ heq => hinj hd heq) hta hha
  obtain ⟨owner, howner, _, hpathOwner⟩ := groupPlain_nodeGroups_lookup stages.hGroups hpre
  refine ⟨hpre, hb, hx, ?_⟩
  rw [hEdgeOwner, ← hpath, r8b_resolvedLast_eq hpathOwner]
  exact howner

theorem regionC8b_selectedForwardChild_stored_actual {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hpart : part ∈ execution.componentsAcc.parts) {index pos : Nat} {stored frame : Rect}
    (hstored : (index, stored) ∈ part.2.labels) (hframe : part.2.rects[pos]? = some frame)
    (hbranch : R8b_EmittedForwardChildAt selected index pos) :
    ∃ raw, pos < selected.cg.nodes.length ∧
      (index, raw) ∈ placedLabels execution.params selected.cg selected.run execution.measured ∧
      (let b := placeBoundsX execution.params selected.cg selected.run execution.measured selected.loops
       stored = shiftRect (0 - b.minX) (-b.minY) raw) ∧
      Disjoint (frameRect execution.params selected.cg selected.run pos) raw ∧ Disjoint frame stored :=
  regionC8b_selectedForwardChild_stored_of_bucketTrace
    (regionC8b_forwardAnchorBucketTrace_actual exactIds idSets) selected hwf hfp hpart
    hstored hframe hbranch

theorem regionC8b_selectedForwardChild_emitted_actual {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hpart : part ∈ execution.componentsAcc.parts) {index pos key : Nat}
    {stored frame shelf : Rect} {srcBox : ModelBox}
    (hstored : (index, stored) ∈ part.2.labels) (hframe : part.2.rects[pos]? = some frame)
    (hkey : part.1[pos]? = some key) (hsrc : inp.boxes[key]? = some srcBox)
    (hgroup : srcBox.role = .group)
    (hpackBox : execution.packedAcc.rects.getD key default = shiftRect shelf.x shelf.y frame)
    (hpackLabel : execution.packedAcc.labels.getD index default = shiftRect shelf.x shelf.y stored)
    (hbranch : R8b_EmittedForwardChildAt selected index pos) :
    ∃ (srcLabel : ModelLabel) (g : Box) (l : SceneLabel),
      inp.labels[index]? = some srcLabel ∧ g ∈ res.scene.boxes ∧ l ∈ res.scene.labels ∧
      g.id = srcBox.id ∧ g.role = "group" ∧ l.id = srcLabel.id ∧ Disjoint g.rect l.rect :=
  regionC8b_selectedForwardChild_emitted_of_bucketTrace
    (regionC8b_forwardAnchorBucketTrace_actual exactIds idSets) selected hwf hfp hpart
    hstored hframe hkey hsrc hgroup hpackBox hpackLabel hbranch

#print axioms r8b_forward_anchor_chain_path
#print axioms regionC8b_forwardAnchorBucketTrace_actual
#print axioms regionC8b_selectedForwardChild_stored_actual
#print axioms regionC8b_selectedForwardChild_emitted_actual

end Elegant.Layered.PipelineImpl

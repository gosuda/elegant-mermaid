import Elegant.Layered.ExactMarkerBracketProof
import Elegant.Layered.ExactPlainNodePathProof
import Elegant.Layered.ForeignFrameClearance

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem exactCandidate_plain_path {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hplain : node.border = 0) (hnonempty : node.clusterPath ≠ []) :
    ∃ (source : Nat) (box : ModelBox), inp.boxes[source]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box := by
  obtain ⟨source, _, hsource⟩ := componentCandidate_nonempty_path_source hnode hnonempty
  have hbound : source < execution.graph0.nodes.length := by
    rw [← exactGraph_length execution.graph_eq]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨original, horiginal⟩ : ∃ n, execution.graph0.nodes[source]? = some n :=
    ⟨_, List.getElem?_eq_getElem hbound⟩
  obtain ⟨sized, hsized, hborder, hpath, _⟩ := exactGraph_node_key execution.graph_eq horiginal
  have heq : sized = node := Option.some.inj (hsized.symm.trans hsource)
  subst sized
  have hplainOriginal : original.border = 0 := hborder.symm.trans hplain
  obtain ⟨nodes, _, _, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  rw [hprepared] at horiginal
  have hsourceBound : source < nodes.length := by
    by_cases hlt : source < nodes.length
    · exact hlt
    · have hbottom := Compound.prepare_bottom_of_index _ _ _ _ source
        (by dsimp only; omega) horiginal
      have hb := hbottom.1
      omega
  have hlines := boxLines_length execution.lines_eq
  have hboxBound : source < inp.boxes.length := by omega
  have hbox : inp.boxes[source]? = some inp.boxes[source] :=
    List.getElem?_eq_getElem hboxBound
  obtain ⟨_, heffective, hpathMap⟩ := fixedSizes_path_index inp hbox
  obtain ⟨_, hplainPath⟩ :=
    prepare_plain_path_origin _ _ _ _ hmetadata horiginal hplainOriginal heffective
  exact ⟨source, _, hbox, hpath.trans (hplainPath.trans hpathMap)⟩

private theorem exactCandidate_path_scoped {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate gpos index : Nat} {group node : Node}
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some group)
    (htop : group.border = -2)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node) :
    PathScoped group.decl group.clusterPath node.clusterPath := by
  intro hmem
  obtain ⟨groupBox, hgroupBox, hgroupPath⟩ :=
    X_cg_group_box execution.graph0_eq execution.graph_eq hgroup htop
  rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq hnode).1
    with hplain | hnodeTop | hnodeBottom
  · have hnonempty : node.clusterPath ≠ [] := by
      intro hempty
      rw [hempty] at hmem
      exact List.not_mem_nil hmem
    obtain ⟨_, box, hbox, hpath⟩ := exactCandidate_plain_path execution hnode hplain hnonempty
    rw [hpath] at hmem
    rw [hgroupPath, hpath]
    exact Compound.path_ancestor_prefix (inputModel inp o) hwf hgroupBox hbox hmem
  · obtain ⟨box, hbox, hpath⟩ :=
      X_cg_group_box execution.graph0_eq execution.graph_eq hnode hnodeTop
    exact X_cg_scope_prefix hwf hgroupBox hgroupPath hbox hpath (List.contains_iff_mem.mpr hmem)
  · obtain ⟨box, hbox, hpath⟩ :=
      X_cg_bottom_box execution.graph0_eq execution.graph_eq hnode hnodeBottom
    exact X_cg_scope_prefix hwf hgroupBox hgroupPath hbox hpath (List.contains_iff_mem.mpr hmem)

private theorem exactCoordinate_paths_scoped {owner : Nat} {path : List Nat} {P : Params}
    {exact : List Nat} {labeled : Proper}
    (hlabeled : ∀ n ∈ labeled.nodes, PathScoped owner path n.node.clusterPath) :
    ∀ n ∈ (coordinateGraphX P exact labeled).nodes, PathScoped owner path n.node.clusterPath := by
  let sized := sizeProperPortsX P exact labeled
  have hsized : ∀ n ∈ sized.nodes, PathScoped owner path n.node.clusterPath := by
    intro n hn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hn
    have hkey := (sizeProperPortsX_key P exact labeled i).symm
    change (sized.nodes[i]?) = some n at hi
    change (labeled.nodes[i]?).map (fun nd => (nd.dummy, nd.node.border, nd.node.clusterPath)) =
      (sized.nodes[i]?).map (fun nd => (nd.dummy, nd.node.border, nd.node.clusterPath)) at hkey
    rw [hi, Option.map_some] at hkey
    obtain ⟨original, horiginal, hkeyEq⟩ := Option.map_eq_some_iff.mp hkey
    have hpath : original.node.clusterPath = n.node.clusterPath := by
      simpa only using congrArg (fun key : Bool × Int × List Nat => key.2.2) hkeyEq
    rw [← hpath]
    exact hlabeled original (List.mem_of_getElem? horiginal)
  have htitled : ∀ n ∈ (titleReservations sized).nodes, PathScoped owner path n.node.clusterPath := by
    intro n hn
    rw [titleReservations_nodes] at hn
    rcases List.mem_append.mp hn with hold | hnew
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hold
      rw [(titleF_keys s).2.2.1]
      exact hsized s hs
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨hzip, _⟩ := List.mem_filter.mp hs
      exact hsized s.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hzip))
  unfold coordinateGraphX
  apply materializeDummyPaths_scoped
  intro n hn
  rw [clearProxyExtents_nodes] at hn
  obtain ⟨bordered, hbordered, rfl⟩ := List.mem_map.mp hn
  rw [(clearF_keys bordered).2.2.1]
  rcases addClusterBorders_node_origin _ _ _ hbordered with horiginal | ⟨top, htop, _, _, hp⟩
  · exact htitled bordered horiginal
  · rw [hp]
    obtain ⟨hzip, _⟩ := List.mem_filter.mp htop
    exact htitled top.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hzip))

/-- Group paths prefix the ordering path of each linked dummy at its executed index. -/
theorem embMarkerPrefixX_holds (exactIds : List String) : embMarkerPrefixX exactIds := by
  intro inp o res execution hwf _hfp comp hcomp candidate run orderOptions hrun
    gpos group hgroup htop d nd hnd hdummy hmem
  obtain ⟨_, labeled, _, hcoord, hkeys, hready, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hlabeled : ∀ n ∈ labeled.nodes, PathScoped group.decl group.clusterPath n.node.clusterPath := by
    intro n hn
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hn
    rcases hkeys index n hindex with ⟨source, hsource, _, _, hpath⟩ | ⟨_, _, hpath⟩
    · rw [hpath]
      exact exactCandidate_path_scoped execution hwf hgroup htop hsource
    · rw [hpath]
      exact pathScoped_nil _ _
  have hscoped := exactCoordinate_paths_scoped (P := execution.params)
    (exact := exactDecls exactIds inp) hlabeled
  rw [hcoord] at hscoped
  have hborders : OrderImpl.BordersWellFormed run.coordinateProper := by
    rw [← hcoord]
    exact materializeDummyPaths_bordersWellFormed
      (clearProxyExtents_bordersWellFormed (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  obtain ⟨_, _, _, widened, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  rw [← hdrop, OrderImpl.dropSynthetic_nodes] at hnd
  have hrel := proxyWidths_rel hproxy
  have hcoordBound : d < run.coordinateProper.nodes.length := by
    rw [← hrel.2.2.1]
    exact (List.getElem?_eq_some_iff.mp hnd).1
  obtain ⟨cn, hcn⟩ : ∃ n, run.coordinateProper.nodes[d]? = some n :=
    ⟨_, List.getElem?_eq_getElem hcoordBound⟩
  obtain ⟨actual, hactual, hdummyEq, _, _⟩ := hrel.2.2.2.2.1 d cn hcn
  have hactualEq : actual = nd := Option.some.inj (hactual.symm.trans hnd)
  have hcnDummy : cn.dummy = true := by
    rw [← hdummyEq, hactualEq]
    exact hdummy
  have hcnBorder : cn.node.border = 0 := hborders.2.2 d cn hcn hcnDummy
  have hsame : widened.nodes[d]? = some cn :=
    (hrel.2.2.2.2.2 d cn hcn (by omega)).1
  have hcnEq : cn = nd := Option.some.inj (hsame.symm.trans hnd)
  rw [XN_plainNodePathResidual_holds exactIds execution.graph0_eq execution.graph_eq
    hcomp hrun hcn hcnBorder]
  exact hscoped cn (List.mem_of_getElem? hcn) (by rwa [hcnEq])

end Elegant.Layered.PipelineImpl

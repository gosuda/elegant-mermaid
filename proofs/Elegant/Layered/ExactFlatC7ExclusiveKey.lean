import Elegant.Layered.ExactFlatC7
import Elegant.Layered.RunStagePathFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact C7 exclusive-key facts.

Target theorems (proved at the end of this file):
  `theorem x_exclusiveRunNodeDecl_holds (exactIds : List String) :
    X_ExclusiveRunNodeDecl exactIds`
  `theorem x_exclusiveKeyOutsideCgPaths_holds (exactIds : List String) :
    X_ExclusiveKeyOutsideCgPaths exactIds`

Route: replay the plain `exclusiveRunNodeDecl_of_preserved` chain
(`RunStagePathFacts.runDeclOfCandidate`) over `componentRunX`, and the plain
`exclusiveKeyOutsideCgPaths` chain over the exact graph by reversing
`exactGraph` (`X_cg_key_rev`, from `exactGraph_node_key`) into the measured
graph `graph0` and reusing the measured-graph origin lemmas there.
-/

/-- `sizeProperPortsX` keeps declarations, dummy flags, borders and paths
(copy of `sizeProperPorts_decl` with the exact-keep condition). -/
private theorem X_sizeProperPortsX_decl {P : Params} {exact : List Nat} {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (sizeProperPortsX P exact p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  unfold sizeProperPortsX
  simp only [List.getElem?_map, List.getElem?_zipIdx, hv, Option.map_some]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> split <;> rfl
/-- The exact coordinate graph keeps every prefix declaration and path
(copy of `coordinateGraph_decl_prefix` over `sizeProperPortsX`). -/
private theorem X_coordinateGraphX_decl_prefix {P : Params} {exact : List Nat} {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (coordinateGraphX P exact p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧
      (nd.dummy = false → qn.node.clusterPath = nd.node.clusterPath) := by
  unfold coordinateGraphX at ⊢
  obtain ⟨s1, hs1, hdecl1, hdum1, hbord1, hpath1⟩ := X_sizeProperPortsX_decl hv
  obtain ⟨t1, ht1, hdecl2, hdum2, hbord2, hpath2⟩ := titleReservations_decl hs1
  obtain ⟨c1, hc1, hdecl3, hdum3, hbord3, hpath3⟩ :=
    addClusterBorders_decl (w := P.clusterBorderW) ht1
  obtain ⟨e1, he1, hdecl4, hdum4, hbord4, hpath4⟩ := clearProxyExtents_decl hc1
  obtain ⟨m1, hm1, hdecl5, hdum5, hbord5⟩ := materialize_decl he1
  refine ⟨m1, hm1, ?_, ?_, ?_, ?_⟩
  · exact hdecl5.trans (hdecl4.trans (hdecl3.trans (hdecl2.trans hdecl1)))
  · exact hdum5.trans (hdum4.trans (hdum3.trans (hdum2.trans hdum1)))
  · exact hbord5.trans (hbord4.trans (hbord3.trans (hbord2.trans hbord1)))
  · intro hnd
    have he1dum : e1.dummy = false := by
      have h1 : s1.dummy = nd.dummy := hdum1
      have h2 : t1.dummy = s1.dummy := hdum2
      have h3 : c1.dummy = t1.dummy := hdum3
      have h4 : e1.dummy = c1.dummy := hdum4
      rw [h4, h3, h2, h1, hnd]
    have hme : m1.node.clusterPath = e1.node.clusterPath := by
      have hlookup : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some e1 := he1
      unfold materializeDummyPaths at hm1
      simp only [List.getElem?_map, List.getElem?_zipIdx, hlookup,
        Option.map_some] at hm1
      have hF : e1.dummy = false := he1dum
      simp only [hF, Bool.false_eq_true, ↓reduceIte] at hm1
      have heq := Option.some.inj hm1
      rw [heq]
    rw [hme, hpath4, hpath3, hpath2, hpath1]

/-- Every original candidate node survives the exact run with its declaration
(copy of `runDeclOfCandidate` over `componentRunX`). -/
private theorem X_runDeclOfCandidate {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {n : Node} (hn : cg.nodes[v]? = some n) :
    ∃ out : ProperNode, run.proper.nodes[v]? = some out ∧ out.node.decl = n.decl := by
  obtain ⟨_, p0, labeled, q0, hn0, hl0, hcoord, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨pn0, hpn0, hdecl0, _, _, _⟩ := normalize_decl_prefix hn0 hn
  obtain ⟨pn1, hpn1, hdecl1, _, _, _⟩ := addLabelNodes_decl _ _ _ hl0 hpn0
  obtain ⟨pn2, hpn2, hdecl2, _, _, _⟩ := X_coordinateGraphX_decl_prefix hpn1
  have hpn2c : run.coordinateProper.nodes[v]? = some pn2 := by
    rw [← hcoord]
    exact hpn2
  obtain ⟨pn3, hpn3, hdecl3, _, _, _⟩ := proxyWidths_decl_path hproxy hpn2c
  have hpn3q : q0.nodes[v]? = some pn3 := hpn3
  obtain ⟨pn4, hpn4, hdecl4, _, _, _⟩ := dropSynthetic_decl (p := q0) hpn3q
  have hpn4r : run.proper.nodes[v]? = some pn4 := by
    rw [← hdrop]
    exact hpn4
  exact ⟨pn4, hpn4r, hdecl4.trans (hdecl3.trans (hdecl2.trans (hdecl1.trans hdecl0)))⟩

/-- Exact execution lines cover every input box. -/
private theorem X_lines_len {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length := (mapM_getElem? _ _ _ h).1
    _ = inp.boxes.length := List.length_zipIdx

/-- The exact measured graph covers a nonfixed group box with a declaration
node (copy of `SceneExecution.nonfixed_group_graph_node` over `graph0`). -/
private theorem X_nonfixed_group_graph_node {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hgroup : source.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) :
    ∃ node : Node, execution.graph0.nodes[key]? = some node ∧ node.border = -2 ∧
      node.decl = key := by
  obtain ⟨nodes, edges, titles, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hi : key < nodes.length := by
    rw [hlength, X_lines_len execution]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hpreparedSource :
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[key]? = some source := by
    simp [List.getElem?_map, hsource, hfixed]
  have hrecord := Compound.prepare_group_title_record
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)
    execution.params.clusterPad titles
    { nodes := nodes, edges := edges, slot := execution.params.slot }
    hi hpreparedSource hgroup
  rw [← hprepared] at hrecord
  exact ⟨_, hrecord, rfl, (hmetadata key _ (List.getElem?_eq_getElem hi)).1⟩

/-- The exact measured graph covers a plain box with a declaration node
(copy of `SceneExecution.plain_graph_node` over `graph0`). -/
private theorem X_plain_graph_node {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hplain : ¬(source.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false)) :
    ∃ node : Node, execution.graph0.nodes[key]? = some node ∧ node.border = 0 ∧
      node.clusterPath = Compound.path inp.boxes source ∧ node.decl = key := by
  obtain ⟨nodes, edges, titles, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hi : key < nodes.length := by
    rw [hlength, X_lines_len execution]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hsource
  have hnotGroup : (if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true then
      { id := source.id, parent := source.parent, exclusive := source.exclusive,
        direction := source.direction, shape := source.shape, icon := source.icon,
        text := source.text } else source : ModelBox).role ≠ .group := by
    by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true
    · simp only [hf, ↓reduceIte]
      decide
    · have hf' : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false :=
        Bool.eq_false_iff.mpr hf
      simp only [hf]
      intro hrole
      exact hplain ⟨hrole, hf'⟩
  have hrecord := Compound.prepare_plain_node_record
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { id := box.id, parent := box.parent, exclusive := box.exclusive,
          direction := box.direction, shape := box.shape, icon := box.icon,
          text := box.text } else box)
    execution.params.clusterPad titles
    { nodes := nodes, edges := edges, slot := execution.params.slot }
    hi hchangedBox hnotGroup
  rw [← hprepared] at hrecord
  obtain ⟨hdecl, hborder⟩ := hmetadata key _ (List.getElem?_eq_getElem hi)
  exact ⟨_, hrecord, hborder, hpathMap, hdecl⟩

/-- The exact graph node behind a model box carries that box index as its
declaration (copy of `graphNodeDeclOfBox` through `exactGraph_node_key`). -/
private theorem X_graphNodeDeclOfBox {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source) :
    ∃ node : Node, execution.graph.nodes[key]? = some node ∧ node.decl = key := by
  by_cases h : source.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false
  · obtain ⟨hrole, hfixed⟩ := h
    obtain ⟨node, hn, _, hdecl⟩ :=
      X_nonfixed_group_graph_node execution hsource hrole hfixed
    obtain ⟨node', hn', _, _, hnd⟩ := exactGraph_node_key execution.graph_eq hn
    exact ⟨node', hn', hnd.trans hdecl⟩
  · have hplain : ¬ (source.role = .group ∧
        inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) := h
    obtain ⟨node, hn, _, _, hdecl⟩ :=
      X_plain_graph_node execution hsource hplain
    obtain ⟨node', hn', _, _, hnd⟩ := exactGraph_node_key execution.graph_eq hn
    exact ⟨node', hn', hnd.trans hdecl⟩

/-- The run node of an exclusive box keeps its declaration through
`componentRunX` (mirror of `exclusiveRunNodeDecl_of_preserved`). -/
theorem x_exclusiveRunNodeDecl_holds (exactIds : List String) :
    X_ExclusiveRunNodeDecl exactIds := by
  intro inp o res execution comp candidate run hcomp hrun v key source hcompv hsource
  obtain ⟨node, hnode, hdecl⟩ := X_graphNodeDeclOfBox execution hsource
  have hcand : (componentCandidate execution.graph comp candidate).nodes[v]? = some node :=
    candidate_node_of_part_key hcompv hnode
  obtain ⟨out, hout, hdecl2⟩ := X_runDeclOfCandidate hrun hcand
  have hnd : RouteImpl.nodeDecl run.proper v = out.node.decl := by
    unfold RouteImpl.nodeDecl
    simp only [hout]
  rw [hnd, hdecl2, hdecl]

/-- A node of an exact component candidate graph is the exact-graph node at
its component key, or the empty-path default (copy of `candidate_graph_node`). -/
private theorem X_candidate_graph_node {g : Graph} {comp : List Nat} {candidate u : Nat}
    {nd : Node} (h : (componentCandidate g comp candidate).nodes[u]? = some nd) :
    (∃ keyU, comp[u]? = some keyU ∧ g.nodes[keyU]? = some nd) ∨
      nd.clusterPath = [] := by
  rw [componentCandidate_nodes] at h
  have hmap : (componentGraph g comp).nodes =
      comp.map (fun v => g.nodes.getD v default) := rfl
  rw [hmap, List.getElem?_map] at h
  cases hu : comp[u]? with
  | none => simp [hu] at h
  | some keyU =>
    simp only [hu, Option.map_some, Option.some.injEq] at h
    cases hgU : g.nodes[keyU]? with
    | none =>
      right
      have hnd : (default : Node) = nd := by
        simpa [List.getD_eq_getElem?_getD, hgU, Option.getD_none] using h
      rw [← hnd]
      rfl
    | some n =>
      left
      have hnn : n = nd := by
        simpa [List.getD_eq_getElem?_getD, hgU, Option.getD_some] using h
      subst hnn
      exact ⟨keyU, rfl, hgU⟩

/-- Reverse key lookup through `exactGraph`: every exact-graph node comes from
the measured-graph node at the same index with the same key fields. -/
private theorem X_cg_key_rev {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g)
    {v : Nat} {nd : Node} (hv : g.nodes[v]? = some nd) :
    ∃ nd0, g0.nodes[v]? = some nd0 ∧ nd0.border = nd.border ∧
      nd0.clusterPath = nd.clusterPath ∧ nd0.decl = nd.decl := by
  have hlen : g.nodes.length = g0.nodes.length := exactGraph_length h
  have hlt : v < g0.nodes.length := by
    have h1 := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have h0 : g0.nodes[v]? = some (g0.nodes[v]'hlt) := List.getElem?_eq_getElem hlt
  obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key h h0
  have heq : nd' = nd := Option.some.inj (hnd'.symm.trans hv)
  subst heq
  exact ⟨_, h0, hnb.symm, hnap.symm, hnd.symm⟩

/-- A demoted box with group role comes from a group-role source box
(copy of `demoted_group_role`). -/
private theorem X_demoted_group_role {inp : Input} {box boxD : ModelBox}
    (hmap : (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box) = boxD)
    (hrole : boxD.role = .group) : box.role = .group := by
  by_cases hfix : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
  · simp only [hfix, ↓reduceIte] at hmap
    rw [← hmap] at hrole
    simp at hrole
  · have hfix' : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
      Bool.eq_false_iff.mpr hfix
    simp only [hfix'] at hmap
    subst hmap
    exact hrole

/-- Plain path source for the exact measured graph
(copy of `SceneExecution.plain_node_path_source` over `graph0`). -/
private theorem X_plain_node_path_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box := by
  obtain ⟨nodes, edges, titles, hprepared, hnodeLength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  have hlineLength : execution.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
  have hpreparedNode := hnode
  rw [hprepared] at hpreparedNode
  have hi : index < nodes.length := by
    by_cases hi : index < nodes.length
    · exact hi
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega)
        hpreparedNode
      omega
  have hibox : index < inp.boxes.length := by omega
  let box := inp.boxes[index]'hibox
  have hbox : inp.boxes[index]? = some box := List.getElem?_eq_getElem hibox
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hbox
  obtain ⟨hdecl, hpath⟩ :=
    prepare_plain_path_origin _ _ _ _ hmetadata hpreparedNode hplain hchangedBox
  exact ⟨box, hbox, hdecl, hpath.trans hpathMap⟩

/-- Group path source for the exact measured graph
(copy of `SceneExecution.group_node_path_source` over `graph0`). -/
private theorem X_group_node_path_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box ++ [index] := by
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin execution.graph0_eq hnode hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, hdecl, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap, hdecl] at hpath
  exact hpath

/-- Bottom path source for the exact measured graph
(copy of `SceneExecution.bottom_node_path_source` over `graph0`). -/
private theorem X_bottom_node_path_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hborder : node.border = 2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨effective, heffective, _, hpath, _, _⟩ :=
    measuredGraph_bottom_origin execution.graph0_eq (List.mem_of_getElem? hnode) hborder
  rw [List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap] at hpath
  exact hpath

/-- The declaration of a group-frame or bottom node of the exact measured
graph is a group-role box (copy of `graph_decl_box_is_group` over `graph0`). -/
private theorem X_graph_decl_box_is_group {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {idx : Nat} {nd : Node} (hgU : execution.graph0.nodes[idx]? = some nd)
    (hb : nd.border = -2 ∨ nd.border = 2)
    {source : ModelBox} (hsource : inp.boxes[nd.decl]? = some source) :
    source.role = .group := by
  rcases hb with hm2 | h2
  · obtain ⟨_, boxD, hboxD, hroleD, _⟩ :=
      measuredGraph_group_origin execution.graph0_eq hgU hm2
    rw [List.getElem?_map, hsource] at hboxD
    obtain ⟨a, ha, hchange⟩ := Option.map_eq_some_iff.mp hboxD
    have har : source = a := Option.some.inj ha
    subst har
    exact X_demoted_group_role hchange hroleD
  · obtain ⟨boxD, hboxD, hroleD, _, _, _⟩ :=
      measuredGraph_bottom_origin execution.graph0_eq (List.mem_of_getElem? hgU) h2
    rw [List.getElem?_map, hsource] at hboxD
    obtain ⟨a, ha, hchange⟩ := Option.map_eq_some_iff.mp hboxD
    have har : source = a := Option.some.inj ha
    subst har
    exact X_demoted_group_role hchange hroleD

/-- The cluster path of an exact measured-graph node never contains the index
of an exclusive source box (copy of `graph_node_clusterPath_excludes` over
`graph0`, using the public `path_mem_group`). -/
private theorem X_clusterPath_excludes {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hexcl : source.exclusive = true)
    {keyU : Nat} {nd : Node} (hgU : execution.graph0.nodes[keyU]? = some nd) :
    key ∉ nd.clusterPath := by
  intro hmem
  have hng : source.role ≠ .group := by
    intro hg
    obtain ⟨_, _, _, _, _, _, hgroups⟩ := (wellFormed_iff (inputModel inp o)).mp hwf
    have hexf := hgroups source (List.mem_of_getElem? hsource) hg
    rw [hexf] at hexcl
    exact Bool.noConfusion hexcl
  have htri := (measuredGraph_marker_shape execution.graph0_eq hgU).1
  rcases htri with h0 | hm2 | h2
  · obtain ⟨boxU, hboxU, _, hpath⟩ := X_plain_node_path_source execution hgU h0
    rw [hpath] at hmem
    exact hng (path_mem_group hwf hframed (List.mem_of_getElem? hboxU) hmem hsource)
  · obtain ⟨boxU, hboxU, hdeclU, hpath⟩ := X_group_node_path_source execution hgU hm2
    rw [hpath] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · exact hng (path_mem_group hwf hframed (List.mem_of_getElem? hboxU) hleft hsource)
    · have hkeyU : key = keyU := List.mem_singleton.mp hright
      subst hkeyU
      rw [← hdeclU] at hsource
      have hrole := X_graph_decl_box_is_group execution hgU (Or.inl hm2) hsource
      exact hng hrole
  · obtain ⟨boxU, hboxU, hpath⟩ := X_bottom_node_path_source execution hgU h2
    rw [hpath] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · exact hng (path_mem_group hwf hframed (List.mem_of_getElem? hboxU) hleft hsource)
    · have hkeyD : key = nd.decl := List.mem_singleton.mp hright
      rw [hkeyD] at hsource
      have hrole := X_graph_decl_box_is_group execution hgU (Or.inr h2) hsource
      exact hng hrole

/-- The key of an exclusive box is not on any candidate cluster path of the
exact graph (mirror of `exclusiveKeyOutsideCgPaths`). -/
theorem x_exclusiveKeyOutsideCgPaths_holds (exactIds : List String) :
    X_ExclusiveKeyOutsideCgPaths exactIds := by
  intro inp o res hwf hframed comp candidate v key source execution
    hcomp hcompv hsource hexcl u nd hnd
  rcases X_candidate_graph_node hnd with ⟨keyU, _, hgU⟩ | hempty
  · obtain ⟨nd0, hg0, _, hpath, _⟩ := X_cg_key_rev execution.graph_eq hgU
    have hmem : key ∉ nd0.clusterPath :=
      X_clusterPath_excludes execution hwf hframed hsource hexcl hg0
    rw [← hpath]
    exact hmem
  · simp [hempty]

end PipelineImpl
end Layered
end Elegant

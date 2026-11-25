import Elegant.Layered.ExactFlatC6KeysPathsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Run-path groups for executed exact component runs.

Proves `X6_runPathGroupsW_holds : X6_RunPathGroupsW exactIds`: every index in
the cluster path of a proper node of an executed exact component run is a
group-role box of the input. This closes the single residual of
`X6_declOutsidePathsW_holds` in `ExactFlatC6KeysPathsProof`, so no narrower
residual remains.

Route: replay of `RunStagePathFacts.runClusterPathGroupMembersCore`
(`SceneExecution` / `componentRun`) over `SceneExecutionX` / `componentRunX`.
`exactGraph` preserves key fields (`exactGraph_node_key`), the shared
normalize / label / title / border / clear / materialize / proxy / drop
stages reuse their group-indexed-path transports, and the one exact-specific
stage `sizeProperPortsX` keeps paths (it only widens `w`). Dummy-node paths
come from chain-head paths via the shared `materialize_all_groups`, so no
dummy sub-case stays open. Truth on executed runs is witnessed by the six
`#eval` lines in `proofs/wip/Probe/X6KeysPathsTProbe.lean`.
-/

/-- Reverse key lookup through `exactGraph`: an exact-graph node comes from
the measured-graph node at the same index with the same key fields. -/
private theorem x6rpg_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g)
    {v : Nat} {nd : Node} (hv : g.nodes[v]? = some nd) :
    ∃ nd0, g0.nodes[v]? = some nd0 ∧ nd0.border = nd.border ∧
      nd0.clusterPath = nd.clusterPath ∧ nd0.decl = nd.decl := by
  have hlen : g.nodes.length = g0.nodes.length := exactGraph_length h
  have hvlt : v < g0.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have h0 : g0.nodes[v]? = some (g0.nodes[v]'hvlt) := List.getElem?_eq_getElem hvlt
  obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key h h0
  have heq : nd' = nd := Option.some.inj (hnd'.symm.trans hv)
  subst heq
  exact ⟨_, h0, hnb.symm, hnap.symm, hnd.symm⟩

/-- Exact measured-graph nodes carry group-indexed paths (copy of
`measured_nodes_path_group` over `SceneExecutionX.graph0`). -/
private theorem x6rpg_measured_all_groups {inp : Input} {o : Options}
    {exactIds : List String} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecutionX exactIds inp o res)
    {v : Nat} {nd : Node} (hn : execution.graph0.nodes[v]? = some nd)
    {k : Nat} (hk : k ∈ nd.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  obtain ⟨nodes, edges, titles, hprepared, hlenNodes, _⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have h2 := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa using h2
  have hnodesLen : nodes.length = inp.boxes.length := by
    rw [hlenNodes, hlinesLen]
  have hmapped : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box).length = inp.boxes.length := by
    simp
  by_cases hv : v < nodes.length
  · have hsrc : ∃ box : ModelBox, inp.boxes[v]? = some box := by
      have : v < inp.boxes.length := by omega
      exact ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨box, hbox⟩ := hsrc
    have hmappedBox : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[v]? =
        some (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) := by
      simp [List.getElem?_map, hbox]
    by_cases hgroup : (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        ({ box with role := .node } : ModelBox) else box).role = .group
    · have hrec := Compound.prepare_group_title_record _ execution.params.clusterPad titles
        { nodes := nodes, edges := edges, slot := execution.params.slot }
        hv hmappedBox hgroup
      rw [← hprepared] at hrec
      have heq := Option.some.inj (hn.symm.trans hrec)
      have hpath : nd.clusterPath =
          Compound.path _ _ ++ [v] := congrArg Node.clusterPath heq
      rw [hpath] at hk
      rcases List.mem_append.mp hk with hmem | hmem
      · have hpathEq := (fixedSizes_path_index inp hbox).2.2
        rw [hpathEq] at hmem
        exact path_mem_group hwf hframed (List.mem_of_getElem? hbox) hmem hb
      · have hkv : k = v := by simpa using hmem
        subst hkv
        have hb_box : b = box := Option.some.inj (hb.symm.trans hbox)
        rw [hb_box]
        have horig : box.role = .group := by
          by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
          · simp [hf] at hgroup
          · simp [hf] at hgroup
            exact hgroup
        exact horig
    · have hrec := Compound.prepare_plain_node_record _ execution.params.clusterPad titles
        { nodes := nodes, edges := edges, slot := execution.params.slot }
        hv hmappedBox (by simpa using hgroup)
      rw [← hprepared] at hrec
      have heq := Option.some.inj (hn.symm.trans hrec)
      have hpath : nd.clusterPath = Compound.path _ _ := congrArg Node.clusterPath heq
      rw [hpath] at hk
      have hpathEq := (fixedSizes_path_index inp hbox).2.2
      rw [hpathEq] at hk
      exact path_mem_group hwf hframed (List.mem_of_getElem? hbox) hk hb
  · have hbot := Compound.prepare_bottom_of_index _ execution.params.clusterPad titles
      { nodes := nodes, edges := edges, slot := execution.params.slot } v
      (by show nodes.length ≤ v; omega) (by rw [← hprepared]; exact hn)
    obtain ⟨_, _, _, hlt, box, hbsrc, hrole, hpath⟩ := hbot
    rw [hpath] at hk
    rcases List.mem_append.mp hk with hmem | hmem
    · have hboxmem : box ∈ (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b) := List.mem_of_getElem? hbsrc
      obtain ⟨orig, horigmem, horigEq⟩ : ∃ orig ∈ inp.boxes,
          (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
            ({ orig with role := .node } : ModelBox) else orig) = box := by
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hboxmem
        simp only [List.getElem?_map] at hi
        obtain ⟨orig, horig, heq⟩ := Option.map_eq_some_iff.mp hi
        exact ⟨orig, List.mem_of_getElem? horig, heq⟩
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp horigmem
      have h := (fixedSizes_path_index inp hm).2.2
      simp only [horigEq] at h
      rw [h] at hmem
      exact path_mem_group hwf hframed horigmem hmem hb
    · have hkv : k = nd.decl := by simpa using hmem
      subst hkv
      obtain ⟨orig, horig, horigEq⟩ : ∃ orig, inp.boxes[nd.decl]? = some orig ∧
          (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
            ({ orig with role := .node } : ModelBox) else orig) = box := by
        simp only [List.getElem?_map] at hbsrc
        obtain ⟨orig, horig, heq⟩ := Option.map_eq_some_iff.mp hbsrc
        exact ⟨orig, horig, heq⟩
      have horigGroup : orig.role = .group := by
        by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) = true
        · simp only [hf] at horigEq
          rw [← horigEq] at hrole
          simp at hrole
        · simp only [hf] at horigEq
          rw [← horigEq] at hrole
          exact hrole
      have hbOrig : b = orig := Option.some.inj (hb.symm.trans horig)
      rw [hbOrig]
      exact horigGroup



/-- Exact-graph nodes carry group-indexed paths via the measured-graph copy. -/
private theorem x6rpg_exact_all_groups {inp : Input} {o : Options} {exactIds : List String}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecutionX exactIds inp o res)
    {v : Nat} {nd : Node} (hn : execution.graph.nodes[v]? = some nd)
    {k : Nat} (hk : k ∈ nd.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  obtain ⟨nd0, hnd0, _, hpath, _⟩ := x6rpg_node_key_rev execution.graph_eq hn
  rw [← hpath] at hk
  exact x6rpg_measured_all_groups hwf hframed execution hnd0 hk hb

/-- Candidate nodes inherit group-indexed paths from the exact graph (copy of
`candidate_nodes_path_group` over `SceneExecutionX`). -/
private theorem x6rpg_candidate_all_groups {inp : Input} {o : Options}
    {exactIds : List String} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {v : Nat} {nd : Node}
    (hn : (componentCandidate execution.graph comp candidate).nodes[v]? = some nd)
    {k : Nat} (hk : k ∈ nd.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  have hrec : (componentCandidate execution.graph comp candidate).nodes =
      comp.map fun w => execution.graph.nodes.getD w default := by
    simp [componentCandidate_nodes, componentGraph]
  have hlen : (componentCandidate execution.graph comp candidate).nodes.length =
      comp.length := by rw [hrec, List.length_map]
  have hvlt : v < comp.length := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    omega
  have hcompv : comp[v]? = some (comp[v]'hvlt) := List.getElem?_eq_getElem hvlt
  have hmap : ((comp.map fun w => execution.graph.nodes.getD w default)[v]?) =
      some ((execution.graph.nodes.getD (comp[v]'hvlt) default)) := by
    simp [List.getElem?_map, hcompv]
  rw [← hrec] at hmap
  have hndEq : nd = execution.graph.nodes.getD (comp[v]'hvlt) default :=
    Option.some.inj (hn.symm.trans hmap)
  by_cases hkey : comp[v]'hvlt < execution.graph.nodes.length
  · have hgn : execution.graph.nodes[comp[v]'hvlt]? =
        some (execution.graph.nodes[comp[v]'hvlt]'hkey) :=
      List.getElem?_eq_getElem hkey
    have hgetD : execution.graph.nodes.getD (comp[v]'hvlt) default =
        execution.graph.nodes[comp[v]'hvlt]'hkey := by
      simp [List.getD_eq_getElem?_getD, hgn]
    rw [hndEq, hgetD] at hk
    exact x6rpg_exact_all_groups hwf hframed execution hgn hk hb
  · have hle : execution.graph.nodes.length ≤ comp[v]'hvlt := by omega
    have hgetD : execution.graph.nodes.getD (comp[v]'hvlt) default = default := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
    rw [hndEq, hgetD] at hk
    have hdef : (default : Node).clusterPath = [] := rfl
    rw [hdef] at hk
    simp at hk

/-- Labeled nodes carry group-indexed paths (copy of `labeled_nodes_path_group`
over `SceneExecutionX`, using the exact candidate copy). -/
private theorem x6rpg_labeled_all_groups {inp : Input} {o : Options}
    {exactIds : List String} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {cg : Graph}
    (hcg : cg = componentCandidate execution.graph comp candidate)
    {ranks : List Int} {p0 labeled : Proper}
    (hn0 : NormalizeImpl.normalize cg ranks = .ok p0)
    (hl0 : Labels.addLabelNodes cg p0 (componentLabels cg execution.measured) = .ok labeled)
    {i : Nat} {pn : ProperNode} (hn : labeled.nodes[i]? = some pn)
    {k : Nat} (hk : k ∈ pn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  subst hcg
  have hbase : ∀ (v : Nat) (n : Node),
      (componentCandidate execution.graph comp candidate).nodes[v]? = some n →
      ∀ (k : Nat), k ∈ n.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group := by
    intro v n hn k hk b hb
    exact x6rpg_candidate_all_groups hwf hframed execution hcomp hn hk hb
  have hkeys0 := normalize_keys hn0
  have hkeys := addLabelNodes_keys _ _ _ hkeys0 hl0
  exact nodeKeys_path_group hbase hkeys hn hk hb

/-- `sizeProperPortsX` keeps declarations, dummy flags, borders and paths (it
only widens `w` for non-exact nodes). -/
private theorem x6rpg_sizeX_decl {P : Params} {exact : List Nat} {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (sizeProperPortsX P exact p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  unfold sizeProperPortsX
  simp only [List.getElem?_map, List.getElem?_zipIdx, hv, Option.map_some]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> split <;> rfl

/-- `sizeProperPortsX` preserves group-indexed paths for all nodes. -/
private theorem x6rpg_sizeX_all_groups {inp : Input} {P : Params} {exact : List Nat}
    {p : Proper}
    (hAll : ∀ (i : Nat) (pn : ProperNode), p.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    {i : Nat} {qn : ProperNode} (hn : (sizeProperPortsX P exact p).nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  have hlen : (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
    simp [sizeProperPortsX]
  have hvlt : i < p.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    omega
  have hlookup : p.nodes[i]? = some (p.nodes[i]'hvlt) :=
    List.getElem?_eq_getElem hvlt
  obtain ⟨qn', hqn', _, _, _, hpath⟩ := x6rpg_sizeX_decl hlookup
  have heq := Option.some.inj (hn.symm.trans hqn')
  subst heq
  rw [hpath] at hk
  exact hAll i _ hlookup k hk b hb
/-- Exact coordinate graph preserves group-indexed paths (copy of
`coordinate_all_groups` over `sizeProperPortsX`). -/
private theorem x6rpg_coordinateX_all_groups {inp : Input} {P : Params} {exact : List Nat}
    {labeled : Proper}
    (hAll : ∀ (i : Nat) (pn : ProperNode), labeled.nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group)
    (hextra : AddClusterBordersExtraGroups
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)
    {i : Nat} {qn : ProperNode}
    (hn : (coordinateGraphX P exact labeled).nodes[i]? = some qn)
    {k : Nat} (hk : k ∈ qn.node.clusterPath)
    {b : ModelBox} (hb : inp.boxes[k]? = some b) : b.role = .group := by
  unfold coordinateGraphX at hn
  have hsize : ∀ (i : Nat) (pn : ProperNode),
      (sizeProperPortsX P exact labeled).nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => x6rpg_sizeX_all_groups hAll hn hk hb
  have htitle : ∀ (i : Nat) (pn : ProperNode),
      (titleReservations (sizeProperPortsX P exact labeled)).nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => titleReservations_all_groups hsize hn hk hb
  have hadd : ∀ (i : Nat) (pn : ProperNode),
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).nodes[i]? = some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => addClusterBorders_all_groups htitle hextra hn hk hb
  have hclear : ∀ (i : Nat) (pn : ProperNode),
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes[i]? =
        some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => clearProxyExtents_all_groups hadd hn hk hb
  have hmat : ∀ (i : Nat) (pn : ProperNode),
      (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).nodes[i]? =
        some pn →
      ∀ (k : Nat), k ∈ pn.node.clusterPath →
        ∀ (b : ModelBox), inp.boxes[k]? = some b → b.role = .group :=
    fun i pn hn k hk b hb => materialize_all_groups hclear hn hk hb
  exact hmat i qn hn k hk b hb

/-- Run-level cluster-path provenance for executed exact component runs:
every proper-node path entry is an input group box. Replay of
`runClusterPathGroupMembersCore` over `componentRunX`. -/
theorem X6_runPathGroupsW_holds (exactIds : List String) :
    X6_RunPathGroupsW exactIds := by
  intro inp o res execution hwf hframed comp candidate run hcomp hrun i nd hn k hk b hb
  obtain ⟨ranks, p0, labeled, q0, hn0, hl0, hproper, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hlabeledAll : ∀ (j : Nat) (pn : ProperNode), labeled.nodes[j]? = some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    exact x6rpg_labeled_all_groups hwf hframed execution hcomp rfl hn0 hl0 hjn hm hbb
  have hextra : AddClusterBordersExtraGroups
      (titleReservations (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled))
      execution.params.clusterBorderW :=
    addClusterBordersExtraGroups_all
  have hcoordAll : ∀ (j : Nat) (pn : ProperNode),
      (coordinateGraphX execution.params (exactDecls exactIds inp) labeled).nodes[j]? =
        some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    exact x6rpg_coordinateX_all_groups hlabeledAll hextra hjn hm hbb
  have hcoordAllRun : ∀ (j : Nat) (pn : ProperNode),
      run.coordinateProper.nodes[j]? = some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    have hjn' : (coordinateGraphX execution.params (exactDecls exactIds inp)
        labeled).nodes[j]? = some pn := by
      rw [hproper]
      exact hjn
    exact hcoordAll j pn hjn' m hm bb hbb
  have hproxyAll : ∀ (j : Nat) (pn : ProperNode), q0.nodes[j]? = some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    exact proxyWidths_all_groups hcoordAllRun hproxy hjn hm hbb
  have hdropAll : ∀ (j : Nat) (pn : ProperNode), run.proper.nodes[j]? = some pn →
      ∀ (m : Nat), m ∈ pn.node.clusterPath →
        ∀ (bb : ModelBox), inp.boxes[m]? = some bb → bb.role = .group := by
    intro j pn hjn m hm bb hbb
    have hqn : (OrderImpl.dropSynthetic q0).nodes[j]? = some pn := by
      rw [hdrop]
      exact hjn
    exact dropSynthetic_all_groups hproxyAll hqn hm hbb
  exact hdropAll i nd hn k hk b hb
end PipelineImpl
end Layered
end Elegant
import Elegant.Layered.RegionFlatC7
import Elegant.Layered.RunStagePathFacts
import Elegant.Layered.ExactFlatFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

private theorem r7_candidateR_nodes_eq (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (candidate : Nat) :
    (componentCandidateR spec g comp candidate).nodes =
      (componentCandidate g comp candidate).nodes := by
  cases spec with
  | none => rfl
  | some region =>
    calc
      (componentCandidateR (.some region) g comp candidate).nodes =
          (componentGraph g comp).nodes := rfl
      _ = (componentCandidate g comp candidate).nodes :=
        (componentCandidate_nodes g comp candidate).symm

private theorem r7_marker_path_mem_group {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {decl key : Nat} {effective source : ModelBox}
    (hlookup : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[decl]? = some effective)
    (hgroup : effective.role = .group)
    (hmem : key ∈ Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) effective ++ [decl])
    (hsource : inp.boxes[key]? = some source) : source.role = .group := by
  rw [List.getElem?_map] at hlookup
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp hlookup
  have hpath := (fixedSizes_path_index inp hbox).2.2
  dsimp only at hpath
  rw [hchange] at hpath
  rw [hpath] at hmem
  rcases List.mem_append.mp hmem with hparent | hself
  · exact path_mem_group hwf hframed (List.mem_of_getElem? hbox) hparent hsource
  · have hindex : key = decl := List.mem_singleton.mp hself
    subst key
    have hsame : source = box := Option.some.inj (hsource.symm.trans hbox)
    rw [hsame]
    split at hchange
    · rw [← hchange] at hgroup
      cases hgroup
    · rw [hchange]
      exact hgroup

private theorem r7_measured_path_mem_group {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hgraph : measuredGraph P inp o lines = .ok g)
    (hlen : lines.length = inp.boxes.length)
    {index key : Nat} {nd : Node} {source : ModelBox}
    (hnode : g.nodes[index]? = some nd) (hmem : key ∈ nd.clusterPath)
    (hsource : inp.boxes[key]? = some source) : source.role = .group := by
  rcases (measuredGraph_marker_shape hgraph hnode).1 with hplain | htop | hbottom
  · obtain ⟨nodes, edges, titles, hprepared, hnodeLen, hmetadata⟩ :=
      measuredGraph_prepared_source hgraph
    rw [hprepared] at hnode
    have hi : index < nodes.length := by
      by_cases hi : index < nodes.length
      · exact hi
      · have hb := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega) hnode
        omega
    have hibox : index < inp.boxes.length := by
      rwa [← hlen, ← hnodeLen]
    have hbox : inp.boxes[index]? = some (inp.boxes[index]'hibox) :=
      List.getElem?_eq_getElem hibox
    obtain ⟨_, heffective, hpathMap⟩ := fixedSizes_path_index inp hbox
    have hpath := (prepare_plain_path_origin _ _ _ _ hmetadata hnode hplain heffective).2
    rw [hpath, hpathMap] at hmem
    exact path_mem_group hwf hframed (List.mem_of_getElem? hbox) hmem hsource
  · obtain ⟨_, effective, hlookup, hgroup, hpath⟩ :=
      measuredGraph_group_origin hgraph hnode htop
    rw [hpath] at hmem
    exact r7_marker_path_mem_group hwf hframed hlookup hgroup hmem hsource
  · obtain ⟨effective, hlookup, hgroup, hpath, _, _⟩ :=
      measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hnode) hbottom
    rw [hpath] at hmem
    exact r7_marker_path_mem_group hwf hframed hlookup hgroup hmem hsource

theorem r7_exclusiveKeyOutsideCgPaths_holds (exactIds : List String)
    (idSets : List (String × List String)) : R7_ExclusiveKeyOutsideCgPaths exactIds idSets := by
  intro inp o res hwf hframed comp candidate _ key source execution _ _ hsource hexclusive
    u nd hnode hmem
  rw [r7_candidateR_nodes_eq] at hnode
  have hnonempty : nd.clusterPath ≠ [] := by
    intro hempty
    simp [hempty] at hmem
  obtain ⟨index, _, hexact⟩ := componentCandidate_nonempty_path_source hnode hnonempty
  have hi : index < execution.graph0.nodes.length := by
    rw [← exactGraph_length execution.graph_eq]
    exact (List.getElem?_eq_some_iff.mp hexact).1
  have hmeasured : execution.graph0.nodes[index]? = some (execution.graph0.nodes[index]'hi) :=
    List.getElem?_eq_getElem hi
  obtain ⟨out, hout, _, hpath, _⟩ := exactGraph_node_key execution.graph_eq hmeasured
  have hsame : out = nd := Option.some.inj (hout.symm.trans hexact)
  rw [hsame] at hpath
  rw [hpath] at hmem
  have hlen : execution.lines.length = inp.boxes.length := by
    have hlines := execution.lines_eq
    unfold boxLines at hlines
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
  have hgroup :=
    r7_measured_path_mem_group hwf hframed execution.graph0_eq hlen hmeasured hmem hsource
  obtain ⟨_, _, _, _, _, _, hgroups⟩ := (wellFormed_iff (inputModel inp o)).mp hwf
  have hnotExclusive := hgroups source (List.mem_of_getElem? hsource) hgroup
  rw [hnotExclusive] at hexclusive
  exact Bool.noConfusion hexclusive

end PipelineImpl
end Layered
end Elegant

import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.ParentContainmentFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem sceneExec_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : execution.lines.length = inp.boxes.length :=
  (mapM_getElem? _ _ _ execution.lines_eq).1.trans (by simp)

/-- A member node of an executed component is either a plain node or a group
top: measured-graph entries below the box count carry border `0` or `-2`. -/
theorem component_node_border_plain_or_group
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {key : Nat} (hkeyLen : key < inp.boxes.length)
    {member : Node} (hmemberGraph : execution.graph.nodes[key]? = some member) :
    member.border = 0 ∨ member.border = -2 := by
  obtain ⟨nodes, edges, titles, hprepared, hnodeLen, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hkeyNodes : key < nodes.length := by
    rw [hnodeLen, sceneExec_lines_len]
    exact hkeyLen
  rw [hprepared] at hmemberGraph
  have hdemoted : (inp.boxes.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source))[key]? =
      some ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) inp.boxes[key]) := by
    simp only [List.getElem?_map, List.getElem?_eq_getElem hkeyLen, Option.map_some]
  by_cases hng : ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) inp.boxes[key]).role = .group
  · rw [Compound.prepare_group_title_record _ _ _ ⟨nodes, edges, execution.params.slot⟩ hkeyNodes
      hdemoted hng] at hmemberGraph
    refine Or.inr ?_
    have hb := congrArg Node.border (Option.some.inj hmemberGraph)
    simpa using hb.symm
  · rw [Compound.prepare_plain_node_record _ _ _ ⟨nodes, edges, execution.params.slot⟩ hkeyNodes
      hdemoted hng] at hmemberGraph
    refine Or.inl ?_
    have hsrc := hmetadata key nodes[key] (List.getElem?_eq_getElem hkeyNodes)
    have hb : member.border = nodes[key].border :=
      (congrArg Node.border (Option.some.inj hmemberGraph)).symm
    rw [hb]
    exact hsrc.2


/-- A paired bottom marker present in the node list yields a `find?` result
for the by-declaration bottom search. -/
private theorem findBottom_some {graph : Graph} {bottom : Node} {decl : Nat}
    (hmem : bottom ∈ graph.nodes) (hborder : bottom.border = 2) (hdecl : bottom.decl = decl) :
    ∃ entry : Node × Nat,
      graph.nodes.zipIdx.find? (fun e => e.1.border == 2 && e.1.decl == decl) = some entry := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hmem
  have hb2 : (((bottom, idx) : Node × Nat).1.border == 2) = true := by
    show (bottom.border == 2) = true
    rw [hborder]; simp
  have hd2 : (((bottom, idx) : Node × Nat).1.decl == decl) = true := by
    show (bottom.decl == decl) = true
    rw [hdecl]; simp
  have hpred : ((fun e : Node × Nat => e.1.border == 2 && e.1.decl == decl)
        (bottom, idx)) = true :=
    Bool.and_eq_true_iff.mpr ⟨hb2, hd2⟩
  have his : (graph.nodes.zipIdx.find? (fun e : Node × Nat =>
      e.1.border == 2 && e.1.decl == decl)).isSome = true :=
    List.find?_isSome.mpr ⟨(bottom, idx), List.mem_zipIdx_iff_getElem?.mpr hidx, hpred⟩
  cases hfind : graph.nodes.zipIdx.find? (fun e => e.1.border == 2 && e.1.decl == decl) with
  | none => rw [hfind] at his; simp at his
  | some entry => exact ⟨entry, rfl⟩

/-- The identity and parent fields survive the fixed-size role demotion. -/
private theorem demotion_fields (inp : Input) :
    (∀ b ∈ inp.boxes,
        ((fun source : ModelBox =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
            { source with role := .node } else source) b).id = b.id) ∧
      ∀ b ∈ inp.boxes,
        ((fun source : ModelBox =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
            { source with role := .node } else source) b).parent = b.parent := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · show ((if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        ({ b with role := .node } : ModelBox) else b)).id = b.id
    by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == b.id) = true
    · simp [hf]
    · simp [hf]
  · show ((if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        ({ b with role := .node } : ModelBox) else b)).parent = b.parent
    by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == b.id) = true
    · simp [hf]
    · simp [hf]

/-- A member's parent group key lies in the member's connected component: the
compound constraint edge joins them, and components own connected endpoints. -/
theorem member_parent_key_in_component
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {key parentKey : Nat}
    (hkeyLen : key < inp.boxes.length)
    (hkeyIn : key ∈ comp)
    {member : Node} (hmemberGraph : execution.graph.nodes[key]? = some member)
    {childBox : ModelBox} (hchildBox : inp.boxes[key]? = some childBox)
    {parentBox : ModelBox} (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hparentRef : childBox.parent = parentBox.id)
    (hparentNe : childBox.parent ≠ "") :
    parentKey ∈ comp := by
  obtain ⟨pb, hpbMem, hpid, hpgroup, hpnotfixed⟩ := framedParents_parent hframed
    (List.mem_of_getElem? hchildBox) hparentNe
  -- the parent box with this id is unique, so it is the framed parent
  have hnod := Model.boxIds_nodup hwf
  obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp hpbMem
  have hmapLen : parentKey < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hparentBox).1
  have hmapLen2 : pi < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hpi).1
  have hid : (inp.boxes.map (·.id))[pi]? = (inp.boxes.map (·.id))[parentKey]? := by
    rw [List.getElem?_map, hpi, List.getElem?_map, hparentBox]
    simp only [Option.map_some, hpid, hparentRef]
  have hpe : pi = parentKey := (hnod.getElem?_inj hmapLen2).mp hid
  have hpe' : parentKey = pi := hpe.symm
  subst hpe'
  have hsame : pb = parentBox :=
    Option.some.inj (hpi.symm.trans hparentBox)
  subst hsame
  have hpbLookup : inp.boxes[parentKey]? = some pb := hparentBox
  -- demoted parent lookup and paired markers
  have hfPb : ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) pb) = pb := by
    simp [hpnotfixed]
  have hdemP : (inp.boxes.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source))[parentKey]? = some pb := by
    rw [List.getElem?_map, hpbLookup]
    simp only [Option.map_some, hfPb]
  have hpkLines : parentKey < execution.lines.length := by
    rw [sceneExec_lines_len]; exact (List.getElem?_eq_some_iff.mp hpbLookup).1
  obtain ⟨top, bottom, htopLookup, hbotMem, htopBorder, hbotBorder, htopDecl, hbotDecl,
    htopPathD, -, -, -⟩ :=
    measuredGraph_paired_markers execution.graph_eq hpkLines hdemP hpgroup
  obtain ⟨botEntry, hbotFind⟩ := findBottom_some hbotMem hbotBorder
    (hbotDecl.trans htopDecl.symm)
  -- transported parent path over the original boxes
  obtain ⟨hidF, hpF⟩ := demotion_fields inp
  have hpm := Compound.path_map inp.boxes (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) hidF hpF hpbMem
  have hstep2 : Compound.path (List.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) inp.boxes) pb =
      Compound.path inp.boxes pb :=
    (congrArg (fun x => Compound.path (List.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) inp.boxes) x) hfPb).symm.trans hpm
  have htopPathInp : top.clusterPath = Compound.path inp.boxes pb ++ [parentKey] := by
    rw [htopPathD, hstep2]
  -- the member path step
  have hstep : Compound.path inp.boxes childBox =
      Compound.path inp.boxes pb ++ [parentKey] :=
    Compound.path_of_parent (inputModel inp o) hwf hpbLookup hchildBox hparentRef hparentNe
  have hmemberZip : (member, key) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hmemberGraph
  have htopZip : (top, parentKey) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopLookup
  rcases component_node_border_plain_or_group execution hkeyLen hmemberGraph with
    hborder0 | hborderM2
  · -- plain member: constraint edge ⟨parentKey, key⟩ from the member list
    obtain ⟨b0, hb0lookup, -, hpath0⟩ := execution.plain_node_path_source hmemberGraph hborder0
    have hb0eq : b0 = childBox := Option.some.inj (hb0lookup.symm.trans hchildBox)
    have hin : parentKey ∈ member.clusterPath := by
      rw [hpath0, hb0eq, hstep]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    rw [← htopDecl] at hin
    obtain ⟨hedge, -⟩ :=
      compound_member_constraint_edges (top := (top, parentKey)) (bottom := botEntry)
        (member := (member, key)) htopZip htopBorder hbotFind hmemberZip hborder0
        (by exact List.contains_iff_mem.mpr hin)
    obtain ⟨comp', hcomp'mem, hparentIn, hkeyIn'⟩ :=
      components_edge_endpoints (sceneExecution_edges_bounded execution)
        (List.mem_append_right execution.graph.edges hedge)
    rw [components_shared_member_eq hcomp'mem hcomp hkeyIn' hkeyIn] at hparentIn
    exact hparentIn
  · -- group member: constraint edge ⟨parentKey, key⟩ from the nested-children list
    obtain ⟨hdeclM, demotedChild, hdemChildLookup, hdemChildRole, hchildPathD⟩ :=
      measuredGraph_group_origin execution.graph_eq hmemberGraph hborderM2
    rw [hdeclM] at hdemChildLookup
    have hdemChildEq : demotedChild = ((fun source : ModelBox =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
          { source with role := .node } else source) childBox) := by
      have hmapChild : (inp.boxes.map (fun source : ModelBox =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
            { source with role := .node } else source))[key]? = some
          ((fun source : ModelBox =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
            { source with role := .node } else source) childBox) := by
        rw [List.getElem?_map, hchildBox]
        simp
      exact Option.some.inj (hdemChildLookup.symm.trans hmapChild)
    have hchildPathInp : member.clusterPath =
        Compound.path inp.boxes childBox ++ [key] := by
      rw [hchildPathD, hdemChildEq, hdeclM]
      exact congrArg (fun p => p ++ [key])
        (Compound.path_map inp.boxes (fun source : ModelBox =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
            { source with role := .node } else source) hidF hpF
          (List.mem_of_getElem? hchildBox))
    have hpath : member.clusterPath.dropLast = top.clusterPath := by
      rw [hchildPathInp, List.dropLast_concat, hstep, ← htopPathInp]
    have hkeyLines : key < execution.lines.length := by
      rw [sceneExec_lines_len]; exact hkeyLen
    obtain ⟨-, childBottom, -, hchildBotMem, -, hchildBotBorder, -, hchildBotDecl, -, -, -, -⟩ :=
      measuredGraph_paired_markers execution.graph_eq hkeyLines hdemChildLookup hdemChildRole
    obtain ⟨childBotEntry, hchildBotFind⟩ :=
      findBottom_some hchildBotMem hchildBotBorder
        (show childBottom.decl = member.decl from by rw [hchildBotDecl]; exact hdeclM.symm)
    obtain ⟨hedge, -⟩ :=
      compound_child_constraint_edges (parent := (top, parentKey))
        (parentBottom := botEntry) (child := (member, key)) (childBottom := childBotEntry)
        htopZip htopBorder hbotFind hmemberZip hborderM2
        (by exact hpath) hchildBotFind
    obtain ⟨comp', hcomp'mem, hparentIn, hkeyIn'⟩ :=
      components_edge_endpoints (sceneExecution_edges_bounded execution)
        (List.mem_append_right execution.graph.edges hedge)
    rw [components_shared_member_eq hcomp'mem hcomp hkeyIn' hkeyIn] at hparentIn
    exact hparentIn

/-- U4: inside one executed component run, every member box lies inside the
frame rectangle of its parent group. -/
theorem frameRect_member_contained
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {memberIndex key parentKey parentIndex : Nat} {member : Node}
    (hkey : comp[memberIndex]? = some key)
    (hkeyLen : key < inp.boxes.length)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    {childBox : ModelBox} (hchildBox : inp.boxes[key]? = some childBox)
    {parentBox : ModelBox} (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hparentRef : childBox.parent = parentBox.id)
    (hparentNe : childBox.parent ≠ "")
    (hparentIndex : comp[parentIndex]? = some parentKey) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).Contained
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run memberIndex) := by
  have hkeyIn : key ∈ comp := List.mem_of_getElem? hkey
  have hmemberGraph : execution.graph.nodes[key]? = some member := by
    have h := hmember
    rw [componentCandidate_nodes] at h
    dsimp only [componentGraph] at h
    simp only [List.getElem?_map, Option.map_some, hkey, List.getD_eq_getElem?_getD] at h
    have hgl : key < execution.graph.nodes.length := sceneExecution_graph_len execution hkeyLen
    cases hkeyOpt : execution.graph.nodes[key]? with
    | none =>
      have hnone : execution.graph.nodes[key]? = none := hkeyOpt
      rw [List.getElem?_eq_none_iff] at hnone
      omega
    | some node =>
      rw [hkeyOpt] at h
      simpa using h
  -- the parent group node in the candidate graph
  obtain ⟨pb, hpbMem, hpid, hpgroup, hpnotfixed⟩ := framedParents_parent hframed
    (List.mem_of_getElem? hchildBox) hparentNe
  have hnod := Model.boxIds_nodup hwf
  obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp hpbMem
  have hmapLen : parentKey < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hparentBox).1
  have hmapLen2 : pi < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hpi).1
  have hid : (inp.boxes.map (·.id))[pi]? = (inp.boxes.map (·.id))[parentKey]? := by
    rw [List.getElem?_map, hpi, List.getElem?_map, hparentBox]
    simp only [Option.map_some, hpid, hparentRef]
  have hpe : pi = parentKey := (hnod.getElem?_inj hmapLen2).mp hid
  have hpe' : parentKey = pi := hpe.symm
  subst hpe'
  have hsame : pb = parentBox :=
    Option.some.inj (hpi.symm.trans hparentBox)
  subst hsame
  have hpbLookup : inp.boxes[parentKey]? = some pb := hparentBox
  have hfPb : ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) pb) = pb := by
    simp [hpnotfixed]
  have hdemP : (inp.boxes.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source))[parentKey]? = some pb := by
    rw [List.getElem?_map, hpbLookup]
    simp only [Option.map_some, hfPb]
  have hpkLines : parentKey < execution.lines.length := by
    rw [sceneExec_lines_len]; exact (List.getElem?_eq_some_iff.mp hpbLookup).1
  obtain ⟨top, -, htopLookup, -, htopBorder, -, htopDecl, -, -, -, -, -⟩ :=
    measuredGraph_paired_markers execution.graph_eq hpkLines hdemP hpgroup
  have hparentNode : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some top := by
    rw [componentCandidate_nodes] at *
    simp only [componentGraph, List.getElem?_map, Option.map_some, hparentIndex,
      List.getD_eq_getElem?_getD, htopLookup, Option.getD_some]
  rcases component_node_border_plain_or_group execution hkeyLen hmemberGraph with
    hborder0 | hborderM2
  · -- plain member
    obtain ⟨b0, hb0lookup, -, hpath0⟩ := execution.plain_node_path_source hmemberGraph hborder0
    have hb0eq : b0 = childBox := Option.some.inj (hb0lookup.symm.trans hchildBox)
    have hstep : Compound.path inp.boxes childBox =
        Compound.path inp.boxes pb ++ [parentKey] :=
      Compound.path_of_parent (inputModel inp o) hwf hpbLookup hchildBox hparentRef hparentNe
    have hin : parentKey ∈ member.clusterPath := by
      rw [hpath0, hb0eq, hstep]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    exact execution.component_member_contained hwf hcomp hrun hparentNode htopBorder
      hmember hborder0 (by rw [htopDecl]; exact List.contains_iff_mem.mpr hin)
  · -- group member
    have hparentBoxDecl : inp.boxes[top.decl]? = some pb := by rw [htopDecl]; exact hpbLookup
    have hchildDecl : member.decl = key := by
      obtain ⟨hdeclM, -, -, -, -⟩ :=
        measuredGraph_group_origin execution.graph_eq hmemberGraph hborderM2
      exact hdeclM
    have hchildBoxDecl : inp.boxes[member.decl]? = some childBox := by
      rw [hchildDecl]; exact hchildBox
    exact execution.component_child_frame_contained hwf hcomp hrun hparentNode htopBorder
      hmember hborderM2 hparentBoxDecl hchildBoxDecl hparentRef hparentNe

end Elegant.Layered.PipelineImpl

import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.CompoundPathFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Residual: exact-run frame nesting for `componentRunX`.

The exact flat pipeline shares ranking, ordering, borders, and coordinates
with the plain pipeline; it changes node sizes (`exactGraph`: exact ids and
fixed-size groups keep exactly their fixed size), port widening
(`sizeProperPortsX`: no widening for exact nodes, inside `componentRunX`),
and rank shifts (`reserveExactRanks`, inside `componentRunX`). The hull
argument behind the plain `SceneExecution.component_member_contained` and
`SceneExecution.component_child_frame_contained` does not depend on the size
values: vertical covering holds by `boundsOf` construction over the shifted
coordinates, and horizontal separation replays from the exact run's own
cross-coordinate and proxy-width equations. This hypothesis records the two
node-level containment facts for successful `componentRunX` runs; the main
theorem below proves everything else (graph transfer and input-level parent
identification) and applies this hypothesis twice. -/
def ExactRunFrameNesting {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) : Prop :=
  (∀ (comp : List Nat) (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
    comp ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run →
    ∀ (index memberIndex : Nat) (node member : Node),
      (componentCandidate execution.graph comp candidate).nodes[index]? = some node →
      node.border = -2 →
      (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member →
      member.border = 0 → member.clusterPath.contains node.decl = true →
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run index).Contained
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run memberIndex)) ∧
  (∀ (comp : List Nat) (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
    comp ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run →
    ∀ (parentIndex childIndex : Nat) (parent child : Node),
      (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent →
      parent.border = -2 →
      (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child →
      child.border = -2 →
      ∀ (parentBox childBox : ModelBox),
        inp.boxes[parent.decl]? = some parentBox →
        inp.boxes[child.decl]? = some childBox →
        childBox.parent = parentBox.id → childBox.parent ≠ "" →
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run parentIndex).Contained
          (frameRect execution.params (componentCandidate execution.graph comp candidate)
            run childIndex))

/-- Executed exact lines cover every input box. -/
private theorem exactLinesLenX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  exact ((mapM_getElem? _ _ _ h).1).trans List.length_zipIdx

/-- Key fields preserved by `exactGraph`: declaration, border, cluster path. -/
private def projNodeX (n : Node) : Nat × Int × List Nat := (n.decl, n.border, n.clusterPath)

private theorem projMapEqX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    List.map projNodeX execution.graph.nodes =
      List.map projNodeX execution.graph0.nodes := by
  have hlen : execution.graph.nodes.length = execution.graph0.nodes.length :=
    exactGraph_length execution.graph_eq
  apply List.ext_getElem?
  intro v
  rw [List.getElem?_map, List.getElem?_map]
  cases h0 : execution.graph0.nodes[v]? with
  | none =>
    have hnone : execution.graph.nodes[v]? = none := by
      rw [List.getElem?_eq_none_iff] at h0 ⊢
      omega
    rw [hnone]
  | some nd0 =>
    obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key execution.graph_eq h0
    rw [hnd']
    simp only [Option.map_some, projNodeX, hnb, hnap, hnd]

/-- Every exact-graph node comes from the measured-graph node at the same
index with the same key fields. -/
private theorem revKeyX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {v : Nat} {nd : Node} (h : execution.graph.nodes[v]? = some nd) :
    ∃ nd0, execution.graph0.nodes[v]? = some nd0 ∧ nd0.decl = nd.decl ∧
      nd0.border = nd.border ∧ nd0.clusterPath = nd.clusterPath := by
  have hmap := projMapEqX execution
  have h1 : (List.map projNodeX execution.graph.nodes)[v]? = some (projNodeX nd) := by
    simp only [List.getElem?_map, h, Option.map_some]
  rw [hmap] at h1
  rw [List.getElem?_map] at h1
  obtain ⟨nd0, hnd0, hproj⟩ := Option.map_eq_some_iff.mp h1
  simp only [projNodeX, Prod.mk.injEq] at hproj
  exact ⟨nd0, hnd0, hproj.1, hproj.2.1, hproj.2.2⟩

/-- A measured-graph node below the box count is a plain node or a group
top: entries below the box count carry border `0` or `-2`. -/
private theorem borderSplitX
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} (hkeyLen : key < inp.boxes.length)
    {member : Node} (hmemberGraph : execution.graph0.nodes[key]? = some member) :
    member.border = 0 ∨ member.border = -2 := by
  obtain ⟨nodes, edges, titles, hprepared, hnodeLen, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hkeyNodes : key < nodes.length := by
    rw [hnodeLen, exactLinesLenX]
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

/-- A plain measured-graph node resolves to its input box, declaration, and
compound path over the original boxes. -/
private theorem plainNodePathSourceX
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box := by
  have hlineLength : execution.lines.length = inp.boxes.length := exactLinesLenX execution
  obtain ⟨nodes, edges, titles, hprepared, hnodeLength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
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

/-- U4 for exact runs, under the plain theorem's hypotheses: inside one
successful exact component run, every member box lies inside the frame
rectangle of its parent group.

This is the nearest true statement to `ExactComponentPlacement` conjunct 2
(`ExactFlatFacts.lean` lines 767-783). The conjunct as stated there carries
no hypotheses, and that statement is false: with `exactIds := []`, boxes
`[a, b]` where `a` and `b` are plain nodes and `b.parent = "a"`, and one
route `a -> b`, `layoutX` succeeds with a single component `[[0, 1]]` whose
graph nodes both carry border `0`, while the two member frames are disjoint
in `y` (parent `{x := -1025, y := 0, w := 2051, h := 2304}`, member
`{x := -1048, y := 5376, w := 2096, h := 2304}`); see
`wip/Probe/ExactMemberWitness.lean`, which evaluates the exact phases and
`decide` of the `Contained` claim to `false` alongside the successful
`layoutX` run. The parent can only be located as a genuine group marker via
`framedParents` (which rules out fixed-size and non-group parents) and the
path identification needs unique box ids, so the plain `WellFormed` and
`framedParents` hypotheses are restored here. The remaining exact-run
geometry is the `ExactRunFrameNesting` residual about `componentRunX`. -/
theorem exactMemberInFrame {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hNest : ExactRunFrameNesting execution) :
    (∀ (comp : List Nat) (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
      comp ∈ components execution.graph →
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate) execution.measured
        orderOptions = .ok run →
      ∀ (memberIndex key parentKey parentIndex : Nat) (member : Node),
        comp[memberIndex]? = some key → key < inp.boxes.length →
        (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
          some member →
        ∀ (childBox : ModelBox), inp.boxes[key]? = some childBox →
        ∀ (parentBox : ModelBox), inp.boxes[parentKey]? = some parentBox →
        childBox.parent = parentBox.id → childBox.parent ≠ "" →
        comp[parentIndex]? = some parentKey →
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run parentIndex).Contained
          (frameRect execution.params (componentCandidate execution.graph comp candidate)
            run memberIndex)) := by
  intro comp candidate run orderOptions hcomp hrun
  intro memberIndex key parentKey parentIndex member hkey hkeyLen hmember
  intro childBox hchildBox parentBox hparentBox hparentRef hparentNe hparentIndex
  have hmemberGraph : execution.graph.nodes[key]? = some member := by
    have h := hmember
    rw [componentCandidate_nodes] at h
    dsimp only [componentGraph] at h
    simp only [List.getElem?_map, Option.map_some, hkey, List.getD_eq_getElem?_getD] at h
    have hgl : key < execution.graph.nodes.length := sceneExecutionX_graph_len execution hkeyLen
    cases hkeyOpt : execution.graph.nodes[key]? with
    | none =>
      have hnone : execution.graph.nodes[key]? = none := hkeyOpt
      rw [List.getElem?_eq_none_iff] at hnone
      omega
    | some node =>
      rw [hkeyOpt] at h
      simpa using h
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
    rw [exactLinesLenX]
    exact (List.getElem?_eq_some_iff.mp hpbLookup).1
  obtain ⟨top0, -, htopLookup0, -, htopBorder0, -, htopDecl0, -, -, -, -, -⟩ :=
    measuredGraph_paired_markers execution.graph0_eq hpkLines hdemP hpgroup
  obtain ⟨top, htopLookup, htopBorderD, _, htopDeclD⟩ :=
    exactGraph_node_key execution.graph_eq htopLookup0
  have htopBorder : top.border = -2 := htopBorderD.trans htopBorder0
  have htopDecl : top.decl = parentKey := htopDeclD.trans htopDecl0
  have hparentNode : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some top := by
    rw [componentCandidate_nodes] at *
    simp only [componentGraph, List.getElem?_map, Option.map_some, hparentIndex,
      List.getD_eq_getElem?_getD, htopLookup, Option.getD_some]
  obtain ⟨member0, hmember0Graph, hmember0Decl, hmember0Border, hmember0Path⟩ :=
    revKeyX execution hmemberGraph
  rcases borderSplitX execution hkeyLen hmember0Graph with hborder0 | hborderM2
  · obtain ⟨b0, hb0lookup, -, hpath0⟩ := plainNodePathSourceX execution hmember0Graph hborder0
    have hb0eq : b0 = childBox := Option.some.inj (hb0lookup.symm.trans hchildBox)
    have hstep : Compound.path inp.boxes childBox =
        Compound.path inp.boxes pb ++ [parentKey] :=
      Compound.path_of_parent (inputModel inp o) hwf hpbLookup hchildBox hparentRef hparentNe
    have hmemberBorder : member.border = 0 := hmember0Border.symm.trans hborder0
    have hmemberPath : member.clusterPath = Compound.path inp.boxes childBox := by
      rw [← hmember0Path, hpath0, hb0eq]
    have hin : parentKey ∈ member.clusterPath := by
      rw [hmemberPath, hstep]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    exact hNest.1 comp candidate run orderOptions hcomp hrun parentIndex memberIndex
      top member hparentNode htopBorder hmember hmemberBorder
      (by rw [htopDecl]; exact List.contains_iff_mem.mpr hin)
  · obtain ⟨hdeclM0, -, -, -, -⟩ :=
      measuredGraph_group_origin execution.graph0_eq hmember0Graph hborderM2
    have hmemberBorder : member.border = -2 := hmember0Border.symm.trans hborderM2
    have hdeclM : member.decl = key := hmember0Decl.symm.trans hdeclM0
    have hparentBoxDecl : inp.boxes[top.decl]? = some pb := by
      rw [htopDecl]; exact hpbLookup
    have hchildBoxDecl : inp.boxes[member.decl]? = some childBox := by
      rw [hdeclM]; exact hchildBox
    exact hNest.2 comp candidate run orderOptions hcomp hrun parentIndex memberIndex
      top member hparentNode htopBorder hmember hmemberBorder
      pb childBox hparentBoxDecl hchildBoxDecl hparentRef hparentNe

end PipelineImpl
end Layered
end Elegant

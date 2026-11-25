import Elegant.Layered.RegionFlatC3
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.ComponentCoverage

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Region parent-in-component (`R_ParentInComponentR`).

Replay of `exactParentInComponent` (`ExactParentInComponent.lean:157`) over
`SceneExecutionR`: the graph construction (`measuredGraph`, `exactGraph`,
`components`) is shared between the exact and region pipelines, and the exact
proof reads only the shared measured/exact graph facts (`graph0_eq`,
`graph_eq`, `lines_eq`) plus well-formedness/framing. The region record carries
the same phase equations (`RegionFoundation.lean:120-154`), so every step
replays verbatim with the `R` execution.

Truth note (probe `proofs/wip/Probe/RegionParentInComponentProbe.lean`,
all `.ok` with no error): on the well-formed framed group and nested inputs
the executed region run keeps every referenced parent in the member's
component (`parCheck=true`); degenerate empty/single inputs are vacuously
`true`. On the fixed-size-group input (`framed=false`) the check is `false`
with components `[[0], [1, 3], [2, 4]]`: the parent sits apart from its
children, so the `framedParents` premise is load-bearing. The dangling-parent
input is vacuous (no `parentBox`) with `framed=false`.
-/

/-- Projection preserved by `exactGraph`: declaration, border, cluster path
(copy of `projNode`/`proj_map_eq`). -/
private def rpic_projNode (n : Node) : Nat × Int × List Nat := (n.decl, n.border, n.clusterPath)

private theorem rpic_proj_map_eq {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    List.map rpic_projNode execution.graph.nodes =
      List.map rpic_projNode execution.graph0.nodes := by
  have hlen : execution.graph.nodes.length = execution.graph0.nodes.length :=
    exactGraph_length execution.graph_eq
  apply List.ext_getElem?
  intro v
  cases h0 : execution.graph0.nodes[v]? with
  | none =>
    have hle : execution.graph0.nodes.length ≤ v :=
      List.getElem?_eq_none_iff.mp h0
    have hle2 : execution.graph.nodes.length ≤ v := by omega
    have hnone : execution.graph.nodes[v]? = none :=
      List.getElem?_eq_none_iff.mpr hle2
    simp only [List.getElem?_map, hnone, h0]
  | some nd0 =>
    obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key execution.graph_eq h0
    simp only [List.getElem?_map, hnd', h0, Option.map_some, rpic_projNode, hnd, hnb, hnap]

/-- Backward key lookup through `exactGraph` (copy of `rev_key`). -/
private theorem rpic_rev_key {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {v : Nat} {nd : Node} (h : execution.graph.nodes[v]? = some nd) :
    ∃ nd0, execution.graph0.nodes[v]? = some nd0 ∧ nd0.decl = nd.decl ∧
      nd0.border = nd.border ∧ nd0.clusterPath = nd.clusterPath := by
  have hmap := rpic_proj_map_eq execution
  have h1 : (List.map rpic_projNode execution.graph.nodes)[v]? = some (rpic_projNode nd) := by
    simp only [List.getElem?_map, h, Option.map_some]
  rw [hmap] at h1
  rw [List.getElem?_map] at h1
  obtain ⟨nd0, hnd0, hproj⟩ := Option.map_eq_some_iff.mp h1
  simp only [rpic_projNode, Prod.mk.injEq] at hproj
  obtain ⟨hdecl, hborder, hpath⟩ := hproj
  exact ⟨nd0, hnd0, hdecl, hborder, hpath⟩

/-- Forward key lookup through `exactGraph` (copy of `fwd_key`). -/
private theorem rpic_fwd_key {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {v : Nat} {nd0 : Node} (h : execution.graph0.nodes[v]? = some nd0) :
    ∃ nd, execution.graph.nodes[v]? = some nd ∧ nd.decl = nd0.decl ∧
      nd.border = nd0.border ∧ nd.clusterPath = nd0.clusterPath := by
  have hmap := rpic_proj_map_eq execution
  have h1 : (List.map rpic_projNode execution.graph0.nodes)[v]? = some (rpic_projNode nd0) := by
    simp only [List.getElem?_map, h, Option.map_some]
  rw [← hmap] at h1
  rw [List.getElem?_map] at h1
  obtain ⟨nd, hnd, hproj⟩ := Option.map_eq_some_iff.mp h1
  simp only [rpic_projNode, Prod.mk.injEq] at hproj
  obtain ⟨hdecl, hborder, hpath⟩ := hproj
  exact ⟨nd, hnd, hdecl, hborder, hpath⟩

/-- Region lines cover the input boxes (copy of `lines_len_X`). -/
private theorem rpic_lines_len_R {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  have hlen := (mapM_getElem? _ _ _ h).1
  calc execution.lines.length = (inp.boxes.zipIdx).length := hlen
    _ = inp.boxes.length := List.length_zipIdx

/-- Region graph-plus-constraint edges stay in bounds (copy of
`sceneExecutionX_edges_bounded`). -/
private theorem rpic_edges_bounded {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    ∀ e ∈ execution.graph.edges ++ Compound.constraints execution.graph,
      e.tail < execution.graph.nodes.length ∧
        e.head < execution.graph.nodes.length := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · rw [exactGraph_edges execution.graph_eq] at he
    have hlines := rpic_lines_len_R execution
    have hbd := measuredGraph_edges_bounded execution.graph0_eq hlines e he
    have hlen := exactGraph_length execution.graph_eq
    omega
  · exact constraints_bounded _ e he

/-- Bottom-marker lookup for one declaration (copy of `findBottom_some`,
private to `ExactParentInComponent.lean`). -/
private theorem rpic_findBottom_some {graph : Graph} {bottom : Node} {decl : Nat}
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
/-- Region source nodes are plain or group-titled (copy of `graph0_border_class`). -/
private theorem rpic_graph0_border_class {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} (hkeyLen : key < inp.boxes.length)
    {nd0 : Node} (hnd0 : execution.graph0.nodes[key]? = some nd0) :
    nd0.border = 0 ∨ nd0.border = -2 := by
  obtain ⟨nodes, edges, titles, hprepared, hnodeLen, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hkeyNodes : key < nodes.length := by
    rw [hnodeLen, rpic_lines_len_R execution]
    exact hkeyLen
  rw [hprepared] at hnd0
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
      hdemoted hng] at hnd0
    refine Or.inr ?_
    have hb := congrArg Node.border (Option.some.inj hnd0)
    simpa using hb.symm
  · rw [Compound.prepare_plain_node_record _ _ _ ⟨nodes, edges, execution.params.slot⟩ hkeyNodes
      hdemoted hng] at hnd0
    refine Or.inl ?_
    have hsrc := hmetadata key nodes[key] (List.getElem?_eq_getElem hkeyNodes)
    have hb : nd0.border = nodes[key].border :=
      (congrArg Node.border (Option.some.inj hnd0)).symm
    rw [hb]
    exact hsrc.2

/-- Plain source nodes recover their box (copy of `graph0_plain_path`). -/
private theorem rpic_graph0_plain_path {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box := by
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  have hlineLength : execution.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
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

/-- Resolve the referenced parent to an unfixed group box (exact lines 169-197:
`framedParents_parent` plus input-id uniqueness). -/
private theorem rpic_parent_resolved {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {key parentKey : Nat} {childBox parentBox : ModelBox}
    (hchildBox : inp.boxes[key]? = some childBox)
    (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hparentRef : childBox.parent = parentBox.id) (hparentNe : childBox.parent ≠ "") :
    parentBox.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == parentBox.id) = false ∧
      ((fun source : ModelBox =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
          { source with role := .node } else source) parentBox) = parentBox ∧
      (inp.boxes.map (fun source : ModelBox =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
          { source with role := .node } else source))[parentKey]? = some parentBox := by
  obtain ⟨pb, hpbMem, hpid, hpgroup, hpnotfixed⟩ := framedParents_parent hframed
    (List.mem_of_getElem? hchildBox) hparentNe
  have hnod := Model.boxIds_nodup hwf
  obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp hpbMem
  have hmapLen : parentKey < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hparentBox).1
  have hmapLen2 : pi < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hpi).1
  have hid : (inp.boxes.map (·.id))[pi]? = (inp.boxes.map (·.id))[parentKey]? := by
    rw [List.getElem?_map, hpi, List.getElem?_map, hparentBox]
    simp only [Option.map_some, hpid, hparentRef]
  have hpe : pi = parentKey := (hnod.getElem?_inj hmapLen2).mp hid
  have hpe' : parentKey = pi := hpe.symm
  subst hpe'
  have hsame : pb = parentBox :=
    Option.some.inj (hpi.symm.trans hparentBox)
  have hfPb : ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) pb) = pb := by
    simp [hpnotfixed]
  have hdemP : (inp.boxes.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source))[parentKey]? = some pb := by
    rw [List.getElem?_map, hpi]
    simp only [Option.map_some, hfPb]
  rw [hsame] at hdemP hfPb hpgroup hpnotfixed
  exact ⟨hpgroup, hpnotfixed, hfPb, hdemP⟩

/-- Extract the parent top marker and its bottom witness (exact lines 201-249). -/
private theorem rpic_top_markers {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {parentKey : Nat} {parentBox : ModelBox}
    (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hpgroup : parentBox.role = .group)
    (hfPb : ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) parentBox) = parentBox)
    (hdemP : (inp.boxes.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source))[parentKey]? = some parentBox) :
    ∃ (top : Node) (botEntry : Node × Nat),
      execution.graph.nodes[parentKey]? = some top ∧ top.border = -2 ∧
      top.decl = parentKey ∧ (top, parentKey) ∈ execution.graph.nodes.zipIdx ∧
      (execution.graph.nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == top.decl) = some botEntry ∧
      top.clusterPath = Compound.path inp.boxes parentBox ++ [parentKey] := by
  have hpkLines : parentKey < execution.lines.length := by
    rw [rpic_lines_len_R execution]
    exact (List.getElem?_eq_some_iff.mp hparentBox).1
  obtain ⟨top0, bottom0, htop0Lookup, hbot0Mem, htop0Border, hbot0Border, htop0Decl,
      hbot0Decl, htop0PathD, _, _, _⟩ :=
    measuredGraph_paired_markers execution.graph0_eq hpkLines hdemP hpgroup
  obtain ⟨top, htopLookup, htopDeclEq, htopBorderEq, htopPathEq⟩ :=
    rpic_fwd_key execution htop0Lookup
  have htopBorder : top.border = -2 := by
    rw [htopBorderEq, htop0Border]
  have htopDecl : top.decl = parentKey := by
    rw [htopDeclEq, htop0Decl]
  have htopPathD : top.clusterPath = Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) parentBox ++ [parentKey] := by
    rw [htopPathEq, htop0PathD]
  obtain ⟨bidx, hbidx⟩ := List.mem_iff_getElem?.mp hbot0Mem
  obtain ⟨bottom, hbottomLookup, hbottomDeclEq, hbottomBorderEq, _⟩ :=
    rpic_fwd_key execution hbidx
  have hbottomMem : bottom ∈ execution.graph.nodes :=
    List.mem_of_getElem? hbottomLookup
  have hbottomBorder : bottom.border = 2 := by
    rw [hbottomBorderEq, hbot0Border]
  have hbottomDecl : bottom.decl = top.decl := by
    calc bottom.decl = bottom0.decl := hbottomDeclEq
      _ = parentKey := hbot0Decl
      _ = top.decl := htopDecl.symm
  obtain ⟨botEntry, hbotFind⟩ :=
    rpic_findBottom_some hbottomMem hbottomBorder hbottomDecl
  have hidF : ∀ b ∈ inp.boxes, ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) b).id = b.id := by
    intro b _
    by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == b.id) = true <;>
      simp [hf]
  have hpF : ∀ b ∈ inp.boxes, ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) b).parent = b.parent := by
    intro b _
    by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == b.id) = true <;>
      simp [hf]
  have hpm := Compound.path_map inp.boxes (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) hidF hpF
      (List.mem_of_getElem? hparentBox)
  have hstep2 : Compound.path (List.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) inp.boxes) parentBox =
      Compound.path inp.boxes parentBox :=
    (congrArg (fun x => Compound.path (List.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) inp.boxes) x) hfPb).symm.trans hpm
  have htopPathInp : top.clusterPath = Compound.path inp.boxes parentBox ++ [parentKey] := by
    rw [htopPathD, hstep2]
  have htopZip : (top, parentKey) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopLookup
  exact ⟨top, botEntry, htopLookup, htopBorder, htopDecl, htopZip, hbotFind, htopPathInp⟩

/-- Plain-member case (exact lines 253-276): the member path runs through the
parent, so a compound edge keeps both ends in one component. -/
private theorem rpic_plain_case {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {key parentKey : Nat} (_hkeyLen : key < inp.boxes.length) (hkeyIn : key ∈ comp)
    {member : Node} (hmemberGraph : execution.graph.nodes[key]? = some member)
    {childBox parentBox : ModelBox}
    (hchildBox : inp.boxes[key]? = some childBox)
    (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hparentRef : childBox.parent = parentBox.id) (hparentNe : childBox.parent ≠ "")
    {top : Node} (htopLookup : execution.graph.nodes[parentKey]? = some top)
    (htopBorder : top.border = -2) (htopDecl : top.decl = parentKey)
    {botEntry : Node × Nat}
    (hbotFind : (execution.graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.decl) = some botEntry)
    (_htopPathInp : top.clusterPath = Compound.path inp.boxes parentBox ++ [parentKey])
    {nd0 : Node} (hnd0 : execution.graph0.nodes[key]? = some nd0)
    (hborder0 : nd0.border = 0) :
    parentKey ∈ comp := by
  obtain ⟨nd0', hnd0', hdeclEq, hborderEq, hpathEq⟩ :=
    rpic_rev_key execution hmemberGraph
  have hndEq : nd0 = nd0' := Option.some.inj (hnd0.symm.trans hnd0')
  subst hndEq
  have hmemberZip : (member, key) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hmemberGraph
  have htopZip : (top, parentKey) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopLookup
  have hplainM : member.border = 0 := hborderEq.symm.trans hborder0
  obtain ⟨b0, hb0lookup, hdeclM0, hpath0⟩ :=
    rpic_graph0_plain_path execution hnd0 hborder0
  have hb0eq : b0 = childBox := Option.some.inj (hb0lookup.symm.trans hchildBox)
  have hmemberPath : member.clusterPath = Compound.path inp.boxes childBox := by
    have h1 : member.clusterPath = nd0.clusterPath := hpathEq.symm
    rw [h1, hpath0, hb0eq]
  have hstep : Compound.path inp.boxes childBox =
      Compound.path inp.boxes parentBox ++ [parentKey] :=
    Compound.path_of_parent (inputModel inp o) hwf hparentBox hchildBox hparentRef hparentNe
  have hin : parentKey ∈ member.clusterPath := by
    rw [hmemberPath, hstep]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  rw [← htopDecl] at hin
  obtain ⟨hedge, _⟩ :=
    compound_member_constraint_edges htopZip htopBorder hbotFind hmemberZip hplainM
      (by exact List.contains_iff_mem.mpr hin)
  obtain ⟨comp', hcomp'mem, hparentIn, hkeyIn'⟩ :=
    components_edge_endpoints (rpic_edges_bounded execution)
      (List.mem_append_right execution.graph.edges hedge)
  rw [components_shared_member_eq hcomp'mem hcomp hkeyIn' hkeyIn] at hparentIn
  exact hparentIn

/-- Group-member link (exact lines 277-303): demote the member, recover its
box, and express its path and declaration through the child box. -/
private theorem rpic_group_link {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} {member : Node}
    (hmemberGraph : execution.graph.nodes[key]? = some member)
    {childBox : ModelBox} (hchildBox : inp.boxes[key]? = some childBox)
    {nd0 : Node} (hnd0 : execution.graph0.nodes[key]? = some nd0)
    (hborderM2 : nd0.border = -2) :
    member.border = -2 ∧ member.decl = key ∧
      member.clusterPath = Compound.path inp.boxes childBox ++ [key] ∧
      ∃ demotedChild : ModelBox,
        (inp.boxes.map (fun source : ModelBox =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
            { source with role := .node } else source))[key]? = some demotedChild ∧
        demotedChild.role = .group := by
  obtain ⟨nd0', hnd0', hdeclEq, hborderEq, hpathEq⟩ :=
    rpic_rev_key execution hmemberGraph
  have hndEq : nd0 = nd0' := Option.some.inj (hnd0.symm.trans hnd0')
  subst hndEq
  have hgroupM : member.border = -2 := hborderEq.symm.trans hborderM2
  obtain ⟨hdeclM0, demotedChild, hdemChildLookup0, hdemChildRole, hchildPathD0⟩ :=
    measuredGraph_group_origin execution.graph0_eq hnd0 hborderM2
  rw [hdeclM0] at hdemChildLookup0
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
    exact Option.some.inj (hdemChildLookup0.symm.trans hmapChild)
  have hidF : ∀ b ∈ inp.boxes, ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) b).id = b.id := by
    intro b _
    by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == b.id) = true <;>
      simp [hf]
  have hpF : ∀ b ∈ inp.boxes, ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) b).parent = b.parent := by
    intro b _
    by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == b.id) = true <;>
      simp [hf]
  have hchildPathInp0 : nd0.clusterPath =
      Compound.path inp.boxes childBox ++ [key] := by
    rw [hchildPathD0, hdemChildEq, hdeclM0]
    exact congrArg (fun p => p ++ [key])
      (Compound.path_map inp.boxes (fun source : ModelBox =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
          { source with role := .node } else source) hidF hpF
        (List.mem_of_getElem? hchildBox))
  have hmemberDecl : member.decl = key := hdeclEq.symm.trans hdeclM0
  have hmemberPath : member.clusterPath =
      Compound.path inp.boxes childBox ++ [key] := hpathEq.symm.trans hchildPathInp0
  exact ⟨hgroupM, hmemberDecl, hmemberPath, demotedChild, hdemChildLookup0, hdemChildRole⟩

/-- Group-member close (exact lines 304-331): drop the member key to the
parent path, then close through the child edge in one component. -/
private theorem rpic_group_close {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {key parentKey : Nat} (hkeyLen : key < inp.boxes.length) (hkeyIn : key ∈ comp)
    {member : Node} (hmemberGraph : execution.graph.nodes[key]? = some member)
    (hmemberDecl : member.decl = key) (hgroupM : member.border = -2)
    {childBox parentBox : ModelBox}
    (hchildBox : inp.boxes[key]? = some childBox)
    (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hparentRef : childBox.parent = parentBox.id) (hparentNe : childBox.parent ≠ "")
    (hmemberPath : member.clusterPath =
      Compound.path inp.boxes childBox ++ [key])
    {top : Node} (htopLookup : execution.graph.nodes[parentKey]? = some top)
    (htopBorder : top.border = -2) (_htopDecl : top.decl = parentKey)
    {botEntry : Node × Nat}
    (hbotFind : (execution.graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.decl) = some botEntry)
    (htopPathInp : top.clusterPath = Compound.path inp.boxes parentBox ++ [parentKey])
    {demotedChild : ModelBox}
    (hdemChildLookup0 : (inp.boxes.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source))[key]? = some demotedChild)
    (hdemChildRole : demotedChild.role = .group) :
    parentKey ∈ comp := by
  have hmemberZip : (member, key) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hmemberGraph
  have htopZip : (top, parentKey) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopLookup
  have hstep : Compound.path inp.boxes childBox =
      Compound.path inp.boxes parentBox ++ [parentKey] :=
    Compound.path_of_parent (inputModel inp o) hwf hparentBox hchildBox hparentRef hparentNe
  have hpath : member.clusterPath.dropLast = top.clusterPath := by
    rw [hmemberPath, List.dropLast_concat, hstep, htopPathInp]
  have hkeyLines : key < execution.lines.length := by
    rw [rpic_lines_len_R execution]
    exact hkeyLen
  obtain ⟨_, childBottom0, _, hchildBotMem0, _, hchildBotBorder0, _, hchildBotDecl0, _, _, _, _⟩ :=
    measuredGraph_paired_markers execution.graph0_eq hkeyLines hdemChildLookup0 hdemChildRole
  obtain ⟨cidx, hcidx⟩ := List.mem_iff_getElem?.mp hchildBotMem0
  obtain ⟨childBottom, hchildLookup, hchildDeclEq, hchildBorderEq, _⟩ :=
    rpic_fwd_key execution hcidx
  have hchildBotMem : childBottom ∈ execution.graph.nodes :=
    List.mem_of_getElem? hchildLookup
  have hchildBotBorder : childBottom.border = 2 := by
    rw [hchildBorderEq, hchildBotBorder0]
  have hchildBotDecl : childBottom.decl = member.decl := by
    calc childBottom.decl = childBottom0.decl := hchildDeclEq
      _ = key := hchildBotDecl0
      _ = member.decl := hmemberDecl.symm
  obtain ⟨childBotEntry, hchildBotFind⟩ :=
    rpic_findBottom_some hchildBotMem hchildBotBorder hchildBotDecl
  obtain ⟨hedge, _⟩ :=
    compound_child_constraint_edges (parent := (top, parentKey))
      (parentBottom := botEntry) (child := (member, key)) (childBottom := childBotEntry)
      htopZip htopBorder hbotFind hmemberZip hgroupM hpath hchildBotFind
  obtain ⟨comp', hcomp'mem, hparentIn, hkeyIn'⟩ :=
    components_edge_endpoints (rpic_edges_bounded execution)
      (List.mem_append_right execution.graph.edges hedge)
  rw [components_shared_member_eq hcomp'mem hcomp hkeyIn' hkeyIn] at hparentIn
  exact hparentIn

/-- The region pipeline keeps referenced parents in the member's component:
replay of `exactParentInComponent` over `SceneExecutionR`. No residual: the
proof reads only the shared measured/exact graph construction. -/
theorem R_parentInComponentR_holds {exactIds : List String}
    {idSets : List (String × List String)} :
    R_ParentInComponentR exactIds idSets := by
  intro inp o res execution hwf hframed comp hcomp key parentKey hkeyLen hkeyIn
    member hmemberGraph childBox hchildBox parentBox hparentBox hparentRef hparentNe
  obtain ⟨hpgroup, _, hfPb, hdemP⟩ :=
    rpic_parent_resolved hwf hframed hchildBox hparentBox hparentRef hparentNe
  obtain ⟨top, botEntry, htopLookup, htopBorder, htopDecl, _, hbotFind, htopPathInp⟩ :=
    rpic_top_markers execution hparentBox hpgroup hfPb hdemP
  obtain ⟨nd0, hnd0, _, _, _⟩ := rpic_rev_key execution hmemberGraph
  rcases rpic_graph0_border_class execution hkeyLen hnd0 with hborder0 | hborderM2
  · exact rpic_plain_case execution hwf hcomp hkeyLen hkeyIn hmemberGraph
      hchildBox hparentBox hparentRef hparentNe htopLookup htopBorder htopDecl
      hbotFind htopPathInp hnd0 hborder0
  · obtain ⟨hgroupM, hmemberDecl, hmemberPath, demotedChild, hdemChildLookup0,
        hdemChildRole⟩ :=
      rpic_group_link execution hmemberGraph hchildBox hnd0 hborderM2
    exact rpic_group_close execution hwf hcomp hkeyLen hkeyIn hmemberGraph
      hmemberDecl hgroupM hchildBox hparentBox hparentRef hparentNe hmemberPath
      htopLookup htopBorder htopDecl hbotFind htopPathInp hdemChildLookup0 hdemChildRole
end PipelineImpl

end Layered
end Elegant

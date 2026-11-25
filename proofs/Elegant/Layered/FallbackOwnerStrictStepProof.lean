import Elegant.Layered.FallbackOwnerFrameProof
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.MemberInFrame
import Elegant.Layered.ChildFrameStrictRankProof
import Elegant.Layered.LabelsClearance
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem strict_key_part_position {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {key : Nat} (hkey : key < inp.boxes.length) :
    ∃ (part : List Nat × Part) (pos k : Nat),
      part ∈ execution.componentsAcc.parts ∧
      execution.componentsAcc.parts[k]? = some part ∧
      part.1[pos]? = some key := by
  have hsizeC : execution.componentsAcc.rects.size = inp.boxes.length :=
    execution.components_rects_size
  have hrect : execution.componentsAcc.rects[key]? = some execution.componentsAcc.rects[key] :=
    Array.getElem?_eq_some_iff.mpr ⟨by rw [hsizeC]; exact hkey, rfl⟩
  obtain ⟨part, hpart, entry, hentry, hentryKey⟩ := execution.parts_coverage _ _ hrect
  have hkeyIn : key ∈ part.1 := by
    rw [← hentryKey]
    exact (List.of_mem_zip hentry).1
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hkeyIn
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hpart
  exact ⟨part, pos, k, hpart, hk, hpos⟩

private theorem strict_part_packed_box_len {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {part : List Nat × Part}
    (hk : execution.componentsAcc.parts[k]? = some part) : k < packed.boxes.length := by
  have hkbl : k < execution.componentsAcc.parts.length := (List.getElem?_eq_some_iff.mp hk).1
  have hcount := Pack.pack_count hpack
  rw [hcount, List.length_map]
  exact hkbl

private theorem strict_component_node_lookup {graph : Graph} {comp : List Nat} {cand : Nat}
    {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

private theorem strict_sceneExec_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) : execution.lines.length = inp.boxes.length :=
  (mapM_getElem? _ _ _ execution.lines_eq).1.trans (by simp)

/-- Strict version of `frameRect_member_contained`: inside one executed
component run, every member box lies strictly inside the frame rectangle of
its parent group. The plain case uses `component_member_strictInside'`
(no residual); the group case uses `component_child_frame_strictInside''`
with the framed-parents admission. -/
theorem frameRect_member_strictInside
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
      run parentIndex).StrictInside
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
    rw [strict_sceneExec_lines_len]; exact (List.getElem?_eq_some_iff.mp hpbLookup).1
  obtain ⟨top, -, htopLookup, -, htopBorder, -, htopDecl, -, -, -, -, -⟩ :=
    measuredGraph_paired_markers execution.graph_eq hpkLines hdemP hpgroup
  have hparentNode : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some top := by
    rw [componentCandidate_nodes] at *
    simp only [componentGraph, List.getElem?_map, Option.map_some, hparentIndex,
      List.getD_eq_getElem?_getD, htopLookup, Option.getD_some]
  rcases component_node_border_plain_or_group execution hkeyLen hmemberGraph with
    hborder0 | hborderM2
  · obtain ⟨b0, hb0lookup, -, hpath0⟩ := execution.plain_node_path_source hmemberGraph hborder0
    have hb0eq : b0 = childBox := Option.some.inj (hb0lookup.symm.trans hchildBox)
    have hstep : Compound.path inp.boxes childBox =
        Compound.path inp.boxes pb ++ [parentKey] :=
      Compound.path_of_parent (inputModel inp o) hwf hpbLookup hchildBox hparentRef hparentNe
    have hin : parentKey ∈ member.clusterPath := by
      rw [hpath0, hb0eq, hstep]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    exact execution.component_member_strictInside' hwf hcomp hrun hparentNode htopBorder
      hmember hborder0 (by rw [htopDecl]; exact List.contains_iff_mem.mpr hin)
  · have hparentBoxDecl : inp.boxes[top.decl]? = some pb := by rw [htopDecl]; exact hpbLookup
    have hchildDecl : member.decl = key := by
      obtain ⟨hdeclM, -, -, -, -⟩ :=
        measuredGraph_group_origin execution.graph_eq hmemberGraph hborderM2
      exact hdeclM
    have hchildBoxDecl : inp.boxes[member.decl]? = some childBox := by
      rw [hchildDecl]; exact hchildBox
    exact execution.component_child_frame_strictInside'' hwf hframed hcomp hrun hparentNode htopBorder
      hmember hborderM2 hparentBoxDecl hchildBoxDecl hparentRef hparentNe

end Elegant.Layered.PipelineImpl

namespace Elegant.Layered

/-- Every non-root scene box lies strictly inside its looked-up group parent,
for an executed layout with framed parents. -/
theorem fallbackOwnerStrictStep_executed {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) :
    FallbackOwnerStrictStep res := by
  intro b hb hparNe p hlook _hrole
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨childBox, hchildBoxMem, _, hbpar, -, hbrect⟩ :=
    PipelineImpl.sceneBox_source_rect execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hchildBoxMem).1
  have hparentNe : childBox.parent ≠ "" := by rw [← hbpar]; exact hparNe
  obtain ⟨parent, hparentMem, hpid, -, -⟩ :=
    framedParents_parent hfp (List.mem_of_getElem? hchildBoxMem) hparentNe
  obtain ⟨piIdx, hpi⟩ := List.mem_iff_getElem?.mp hparentMem
  have hfind : res.scene.layoutDump.boxes.find? (fun x : Box => x.id == b.parent) =
      some p := hlook
  have hpMemDump : p ∈ res.scene.layoutDump.boxes := List.mem_of_find?_eq_some hfind
  have hpMem : p ∈ res.scene.boxes := by
    simpa only [Scene.layoutDump] using hpMemDump
  have hpId : p.id = b.parent := by
    have hsome := List.find?_some hfind
    simpa using hsome
  obtain ⟨pj, hpj⟩ := List.mem_iff_getElem?.mp hpMem
  obtain ⟨pbox, hsp, hspid, -, -, hprect⟩ := PipelineImpl.sceneBox_source_rect execution hpj
  have hjLen : pj < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsp).1
  have hmapLen2 : piIdx < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hpi).1
  have hid : (inp.boxes.map (·.id))[piIdx]? = (inp.boxes.map (·.id))[pj]? := by
    rw [List.getElem?_map, hpi, List.getElem?_map, hsp]
    simp only [Option.map_some]
    rw [hpid.trans (hbpar.symm.trans (hpId.symm.trans hspid))]
  have hpe : piIdx = pj := (Model.boxIds_nodup hwf).getElem?_inj hmapLen2 |>.mp hid
  have hpiP : inp.boxes[pj]? = some parent := by rw [← hpe]; exact hpi
  have hpackedEq := execution.packed_eq
  unfold PipelineImpl.packAcc at hpackedEq
  obtain ⟨packed, hpack, -⟩ := PipelineImpl.bind_ok hpackedEq
  have hcompMap := (PipelineImpl.actual_components_parts_geometry (by rfl)
    execution.components_eq).1
  obtain ⟨part, posB, k, -, hk, hposB⟩ :=
    PipelineImpl.strict_key_part_position execution hbiLen
  have hkLen := PipelineImpl.strict_part_packed_box_len execution packed hpack hk
  have hbox : packed.boxes[k]? = some packed.boxes[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
  obtain ⟨cand, run, loops, _, hrun, _, _, hlookup⟩ :=
    PipelineImpl.part_frame_lookup execution packed hpack hk hbox
  have hcomp : part.1 ∈ PipelineImpl.components execution.graph := by
    rw [← hcompMap]
    exact List.mem_map.mpr ⟨part, List.mem_of_getElem? hk, rfl⟩
  have hgl : bi < execution.graph.nodes.length :=
    PipelineImpl.sceneExecution_graph_len execution hbiLen
  have hmemberGraph : execution.graph.nodes[bi]? = some execution.graph.nodes[bi] :=
    List.getElem?_eq_some_iff.mpr ⟨hgl, rfl⟩
  have hmemberLookup :
      (PipelineImpl.componentCandidate execution.graph part.1 cand).nodes[posB]? =
        some execution.graph.nodes[bi] :=
    PipelineImpl.strict_component_node_lookup hposB hmemberGraph
  have hkeyIn : bi ∈ part.1 := List.mem_of_getElem? hposB
  have hparentIn : pj ∈ part.1 :=
    PipelineImpl.member_parent_key_in_component execution hwf hfp hcomp hbiLen hkeyIn
      hmemberGraph hchildBoxMem hpiP hpid.symm hparentNe
  obtain ⟨parentIndex, hpIdx⟩ := List.getElem?_of_mem hparentIn
  have hstrict :=
    PipelineImpl.frameRect_member_strictInside execution hwf hfp hcomp hrun hposB hbiLen
      hmemberLookup hchildBoxMem hpiP hpid.symm hparentNe hpIdx
  have hchildRect := hlookup posB bi hposB hbiLen
  have hparentRect := hlookup parentIndex pj hpIdx hjLen
  have hstep1 := PipelineImpl.strictInside_shiftRect (dx := 0 - (PipelineImpl.placeBounds
        execution.params
        (PipelineImpl.componentCandidate execution.graph part.1 cand) run execution.measured loops).minX)
    (dy := 0 - (PipelineImpl.placeBounds
        execution.params
        (PipelineImpl.componentCandidate execution.graph part.1 cand) run execution.measured loops).minY)
    hstrict
  have hstep2 := PipelineImpl.strictInside_shiftRect
    (dx := packed.boxes[k].x) (dy := packed.boxes[k].y) hstep1
  have hstep3 := PipelineImpl.strictInside_orientRect (d := o.direction)
    (h := execution.packedAcc.canvasH) hstep2
  have htransport := PipelineImpl.strictInside_shiftRect
    (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin) hstep3
  rw [hprect, hbrect, hchildRect, hparentRect]
  exact htransport

end Elegant.Layered

import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.SizingCoverageBridge
import Elegant.Layered.MemberInFrame

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Every model box key below the input length is a member of some executed part at a
concrete part index. -/
private theorem key_part_position {inp : Input} {o : Options} {res : FamilyResult}
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

/-- A part index below the executed parts is below the packed shelf boxes. -/
private theorem part_packed_box_len {inp : Input} {o : Options} {res : FamilyResult}
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

/-- A node of a component at declaration position `pos` is the measured-graph node of
the declaration's box key. -/
private theorem component_node_lookup {graph : Graph} {comp : List Nat} {cand : Nat}
    {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

end PipelineImpl

set_option maxHeartbeats 2000000 in
/-- Clause 3 of the layout validator for a successful flat `PipelineImpl.layout` whose
input model is well formed and whose parents are all framed groups: a scene box with a
parent lies inside that parent's scene box. Both boxes come from the same executed
component part, where `frameRect_member_contained` holds; the shared packed and margin
shifts transport the containment to the output scene. -/
theorem layout_c3 {inp : Input} {o : Options} {res : FamilyResult}
    (h : PipelineImpl.layout inp o = .ok res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true) :
    Validator.C3 res.scene.layoutDump := by
  obtain ⟨execution⟩ := PipelineImpl.layout_sceneExecution h
  have hpackedEq := execution.packed_eq
  unfold PipelineImpl.packAcc at hpackedEq
  obtain ⟨packed, hpack, -⟩ := PipelineImpl.bind_ok hpackedEq
  have hcompMap := (PipelineImpl.actual_components_parts_geometry (by rfl)
    execution.components_eq).1
  intro b hb hbparent p hpLookup
  simp only [Scene.layoutDump] at hb
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨childBox, hchildBoxMem, -, hbpar, -, hbrect⟩ :=
    PipelineImpl.sceneBox_source_rect execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hchildBoxMem).1
  have hparentNe : childBox.parent ≠ "" := by rw [← hbpar]; exact hbparent
  obtain ⟨parent, hparentMem, hpid, -, -⟩ :=
    framedParents_parent hframed (List.mem_of_getElem? hchildBoxMem) hparentNe
  obtain ⟨piIdx, hpi⟩ := List.mem_iff_getElem?.mp hparentMem
  have hpiLen : piIdx < inp.boxes.length := (List.getElem?_eq_some_iff.mp hpi).1
  -- the dump's parent box `p` is the scene box of the input parent at index `pi`
  have hfind : res.scene.layoutDump.boxes.find? (fun x : Box => x.id == b.parent) =
      some p := hpLookup
  have hpMemDump : p ∈ res.scene.layoutDump.boxes := List.mem_of_find?_eq_some hfind
  have hpMem : p ∈ res.scene.boxes := by
    simpa only [Scene.layoutDump] using hpMemDump
  have hpId : p.id = b.parent := by
    have hsome := List.find?_some hfind
    simpa using hsome
  obtain ⟨pj, hpj⟩ := List.mem_iff_getElem?.mp hpMem
  obtain ⟨pbox, hsp, hspid, -, -, hprect⟩ := PipelineImpl.sceneBox_source_rect execution hpj
  have hjLen : pj < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsp).1
  -- the dump's parent box `p` is the scene box of the input parent at index `piIdx`:
  -- both resolve through `box?` to the same find result, so their ids agree
  have hmapLen2 : piIdx < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hpi).1
  have hid : (inp.boxes.map (·.id))[piIdx]? = (inp.boxes.map (·.id))[pj]? := by
    rw [List.getElem?_map, hpi, List.getElem?_map, hsp]
    simp only [Option.map_some]
    rw [hpid.trans (hbpar.symm.trans (hpId.symm.trans hspid))]
  have hpe : piIdx = pj := (Model.boxIds_nodup hwf).getElem?_inj hmapLen2 |>.mp hid
  have hpiP : inp.boxes[pj]? = some parent := by rw [← hpe]; exact hpi
  -- both boxes belong to one executed component part
  obtain ⟨part, posB, k, -, hk, hposB⟩ := PipelineImpl.key_part_position execution hbiLen
  have hkLen := PipelineImpl.part_packed_box_len execution packed hpack hk
  have hbox : packed.boxes[k]? = some packed.boxes[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
  obtain ⟨cand, run, loops, _area, hrun, _hloops, _hpartdef, hlookup⟩ :=
    PipelineImpl.part_frame_lookup execution packed hpack hk hbox

  have hcomp : part.1 ∈ PipelineImpl.components execution.graph := by
    rw [← hcompMap]
    exact List.mem_map.mpr ⟨part, List.mem_of_getElem? hk, rfl⟩
  -- the child's measured-graph node and its candidate node
  have hgl : bi < execution.graph.nodes.length := PipelineImpl.sceneExecution_graph_len execution hbiLen
  have hmemberGraph : execution.graph.nodes[bi]? = some execution.graph.nodes[bi] :=
    List.getElem?_eq_some_iff.mpr ⟨hgl, rfl⟩
  have hmemberLookup :
      (PipelineImpl.componentCandidate execution.graph part.1 cand).nodes[posB]? =
        some execution.graph.nodes[bi] :=
    PipelineImpl.component_node_lookup hposB hmemberGraph
  -- the parent group key lies in the same component
  have hkeyIn : bi ∈ part.1 := List.mem_of_getElem? hposB
  have hparentIn : pj ∈ part.1 :=
    Elegant.Layered.PipelineImpl.member_parent_key_in_component execution hwf hframed hcomp hbiLen hkeyIn hmemberGraph
      hchildBoxMem hpiP hpid.symm hparentNe
  obtain ⟨parentIndex, hpIdx⟩ := List.getElem?_of_mem hparentIn
  -- per-run containment of the two frame rectangles
  have hcontained :=
    Elegant.Layered.PipelineImpl.frameRect_member_contained execution hwf hframed hcomp hrun hposB hbiLen
      hmemberLookup hchildBoxMem hpiP hpid.symm hparentNe hpIdx
  -- the packed accumulator stores the transported frames of both keys
  have hchildRect := hlookup posB bi hposB hbiLen
  have hparentRect := hlookup parentIndex pj hpIdx hjLen
  have hstep1 := PipelineImpl.contained_shiftRect_imp
    (dx := 0 - (PipelineImpl.placeBounds execution.params
        (PipelineImpl.componentCandidate execution.graph part.1 cand) run execution.measured loops).minX)
    (dy := 0 - (PipelineImpl.placeBounds execution.params
        (PipelineImpl.componentCandidate execution.graph part.1 cand) run execution.measured loops).minY)
    hcontained
  have hstep2 := PipelineImpl.contained_shiftRect_imp
    (dx := packed.boxes[k].x) (dy := packed.boxes[k].y) hstep1
  have hstep3 := PipelineImpl.contained_orientRect (d := o.direction)
    (h := execution.packedAcc.canvasH) hstep2
  have htransport := PipelineImpl.contained_shiftRect_imp
    (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin) hstep3
  rw [hprect, hbrect, hchildRect, hparentRect]
  exact htransport

end Layered
end Elegant

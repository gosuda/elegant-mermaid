import Elegant.Layered.RankSiblingDisjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- `mapM` preserves the length of the input list on a successful run. -/
private theorem mapM_ok_len {err α β : Type} (f : α → Except err β) :
    ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    change Except.ok [] = Except.ok out at h
    injection h with hout
    subst out
    rfl
  | cons a l ih =>
    intro out h
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error err =>
      rw [ha] at h
      change Except.error err = Except.ok out at h
      cases h
    | ok b =>
      cases hxs : l.mapM f with
      | error err =>
        rw [ha, hxs] at h
        change Except.error err = Except.ok out at h
        cases h
      | ok xs =>
        rw [ha, hxs] at h
        change Except.ok (b :: xs) = Except.ok out at h
        injection h with hout
        subst out
        exact congrArg Nat.succ (ih xs hxs)

/-- A packed shelf box keeps the declaring part's item dimensions at the same index. -/
private theorem pack_box_dims {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out)
    {k : Nat} (hk : k < out.boxes.length) (hik : k < items.length) :
    out.boxes[k].w = items[k].width ∧ out.boxes[k].h = items[k].height := by
  have hd := Pack.pack_dimensions h
  unfold Pack.dimensions at hd
  have h1 := congrArg (fun l => l[k]?) hd
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hik] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  exact h1

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

private theorem placeComponent_rects_get {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} {cursor : Int}
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponent P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBounds P cg run labels loops).minX)
        (0 - (placeBounds P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponent placeBounds
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- For one executed part at pack index `k`: a fixed component run places every model box
key of the part inside the part's packed shelf box, and the packed accumulator stores
exactly that placed frame. -/
private theorem part_packed_frame
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {part : List Nat × Part}
    (hk : execution.componentsAcc.parts[k]? = some part)
    (hkLen : k < packed.boxes.length) :
    ∃ candidate run loops,
      componentRun execution.params
        (componentCandidate execution.graph part.1 candidate) execution.measured
        (candidateOrder candidate) = .ok run ∧
      (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
        packed.boxes[k].Contained (shiftRect packed.boxes[k].x packed.boxes[k].y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph part.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph part.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph part.1 candidate) run i)))) ∧
      (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
        execution.packedAcc.rects.getD key default =
          shiftRect packed.boxes[k].x packed.boxes[k].y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph part.1 candidate) run execution.measured
                loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph part.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph part.1 candidate) run i))) := by
  have hbox : packed.boxes[k]? = some packed.boxes[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
  obtain ⟨candidate, run, loops, _area, hrun, -, hpartdef, hlookup⟩ :=
    part_frame_lookup execution packed hpack hk hbox
  have hpartget := (List.getElem?_eq_some_iff.mp hk).2
  have hmapLen : k < (execution.componentsAcc.parts.map
      (fun part => Pack.Item.mk part.2.width part.2.height part.2.area)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hk).1
  have hitem : (execution.componentsAcc.parts.map
      (fun part => Pack.Item.mk part.2.width part.2.height part.2.area))[k] =
      Pack.Item.mk part.2.width part.2.height part.2.area := by
    rw [List.getElem_map, hpartget]
  obtain ⟨hw0, hh0⟩ := pack_box_dims hpack hkLen hmapLen
  have hwb : packed.boxes[k].w = part.2.width := by
    rw [hw0, hitem]
  have hhb : packed.boxes[k].h = part.2.height := by
    rw [hh0, hitem]
  have hwlink : part.2.width =
      (placeComponent execution.params
        (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops).width := by
    rw [hpartdef]
  have hhlink : part.2.height =
      (placeComponent execution.params
        (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops).height := by
    rw [hpartdef]
  refine ⟨candidate, run, loops, hrun, ?_, hlookup⟩
  intro i key hkey _
  have hi : i < (componentCandidate execution.graph part.1 candidate).nodes.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
    simpa using (List.getElem?_eq_some_iff.mp hkey).1
  have hplaced : (placeComponent execution.params
      (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops).rects[i]? =
    some (shiftRect (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 candidate) run execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 candidate) run execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 candidate) run i)) :=
    placeComponent_rects_get hi
  have hmem := List.mem_of_getElem? hplaced
  have hb := placeComponent_rects_bounds execution.params
    (componentCandidate execution.graph part.1 candidate) run 0 execution.measured loops _
    hmem
  simp only [Rect.Contained, shiftRect] at hb ⊢
  rw [hwb, hhb, hwlink, hhlink]
  omega

/-- A node of a component at declaration position `pos` is the measured-graph node of
the declaration's box key. -/
private theorem component_node_lookup {graph : Graph} {comp : List Nat} {cand : Nat}
    {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

/-- An exclusive source box of a successful execution is a border-0 node of the measured
graph at the same index. -/
private theorem exclusive_source_border_zero {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hlinesLen : execution.lines.length = inp.boxes.length)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hex : source.exclusive = true) :
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.border = 0 := by
  have hrole : source.role ≠ .group :=
    wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource) hex
  have hkeyLen : key < execution.lines.length := by
    rw [hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hline : execution.lines[key]? = some execution.lines[key] :=
    List.getElem?_eq_some_iff.mpr ⟨hkeyLen, rfl⟩
  exact measuredGraph_exclusive_node_border_zero execution.checked
    execution.graph_eq hline hsource hrole

end PipelineImpl

set_option maxHeartbeats 2000000 in
/-- Clause 2 of the layout validator for a successful flat `PipelineImpl.layout` under
the well-formed input model: two distinct exclusive scene boxes sharing a parent are
disjoint. Same-component siblings are separated by the executed component run; boxes in
different components live in disjoint packed shelf boxes. -/
theorem layout_c2 {inp : Input} {o : Options} {res : FamilyResult}
    (h : PipelineImpl.layout inp o = .ok res)
    (hwf : WellFormed (inputModel inp o)) :
    Validator.C2 res.scene.layoutDump := by
  obtain ⟨execution⟩ := PipelineImpl.layout_sceneExecution h
  have hpackedEq := execution.packed_eq
  unfold PipelineImpl.packAcc at hpackedEq
  obtain ⟨packed, hpack, -⟩ := PipelineImpl.bind_ok hpackedEq
  have hcompMap := (PipelineImpl.actual_components_parts_geometry (by rfl)
    execution.components_eq).1
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    simp only [PipelineImpl.boxLines] at hl
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        PipelineImpl.mapM_ok_len _ _ _ hl
      _ = inp.boxes.length := List.length_zipIdx
  intro b hb c hc hne hbex hcex _hpar
  simp only [Scene.layoutDump, List.mem_iff_getElem?] at hb hc
  obtain ⟨bi, hbi⟩ := hb
  obtain ⟨ci, hci⟩ := hc
  obtain ⟨sb, hsb, hbid, -, hbexS, hbrect⟩ := PipelineImpl.sceneBox_source_rect execution hbi
  obtain ⟨sc, hsc, hcid, -, hcexS, hcrect⟩ := PipelineImpl.sceneBox_source_rect execution hci
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
  have hciLen : ci < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsc).1
  have hbiNe : bi ≠ ci := by
    intro heq
    subst heq
    have hss : sb = sc := Option.some.inj (hsb.symm.trans hsc)
    exact hne (by rw [hbid, hcid, hss])
  obtain ⟨partB, posB, kB, -, hkB, hposB⟩ :=
    PipelineImpl.key_part_position execution hbiLen
  obtain ⟨partA, posA, kA, -, hkA, hposA⟩ :=
    PipelineImpl.key_part_position execution hciLen
  have hkBlen := PipelineImpl.part_packed_box_len execution packed hpack hkB
  have hkAlen := PipelineImpl.part_packed_box_len execution packed hpack hkA
  by_cases hksame : kB = kA
  · -- same packed shelf box: one component run separates the two plain nodes
    subst hksame
    have hpartsSame : partA = partB := Option.some.inj (hkA.symm.trans hkB)
    rw [hpartsSame] at hposA
    have hposNe : posB ≠ posA := by
      intro heq
      rw [heq] at hposB
      exact hbiNe (Option.some.inj (hposB.symm.trans hposA))
    obtain ⟨candB, runB, _loopsB, hrunB, -, hlookupB⟩ :=
      PipelineImpl.part_packed_frame execution packed hpack hkB hkBlen
    obtain ⟨nodeB, hnodeBg, hborderB⟩ :=
      PipelineImpl.exclusive_source_border_zero execution hwf hlinesLen hsb
        (hbexS.symm.trans hbex)
    obtain ⟨nodeA, hnodeAg, hborderA⟩ :=
      PipelineImpl.exclusive_source_border_zero execution hwf hlinesLen hsc
        (hcexS.symm.trans hcex)
    have hnodeBlookup : (PipelineImpl.componentCandidate execution.graph partB.1 candB).nodes[posB]? =
        some nodeB := PipelineImpl.component_node_lookup hposB hnodeBg
    have hnodeAlookup : (PipelineImpl.componentCandidate execution.graph partB.1 candB).nodes[posA]? =
        some nodeA := PipelineImpl.component_node_lookup hposA hnodeAg
    have hcompSame : partB.1 ∈ PipelineImpl.components execution.graph := by
      rw [← hcompMap]
      exact List.mem_map.mpr ⟨partB, List.mem_of_getElem? hkB, rfl⟩
    have hdisjFrames := PipelineImpl.componentRun_positions_disjoint
      (P := execution.params) execution.graph_eq hcompSame hrunB
      hnodeBlookup hnodeAlookup hborderB hborderA hposNe
    rw [hbrect, hcrect, hlookupB posB bi hposB hbiLen, hlookupB posA ci hposA hciLen]
    intro hmeet
    exact hdisjFrames (PipelineImpl.meetsInterior_of_shiftRect
      (PipelineImpl.meetsInterior_of_shiftRect (PipelineImpl.meetsInterior_of_orientRect
        (PipelineImpl.meetsInterior_of_shiftRect hmeet))))
  · -- different packed shelf boxes: the shelf boxes are disjoint and contain the frames
    obtain ⟨_candA, _runA, _loopsA, -, hcontainA, hlookupA⟩ :=
      PipelineImpl.part_packed_frame execution packed hpack hkA hkAlen
    obtain ⟨_candB, _runB, _loopsB, -, hcontainB, hlookupB⟩ :=
      PipelineImpl.part_packed_frame execution packed hpack hkB hkBlen
    have hboxesDisj : ¬ (packed.boxes[kB]).meetsInterior (packed.boxes[kA]) :=
      Pack.pack_boxes_disjoint hpack kB kA hkBlen hkAlen hksame
    have hdisjShift := PipelineImpl.not_meetsInterior_shiftRect
      (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
      (PipelineImpl.not_meetsInterior_orientRect (d := o.direction)
        (h := execution.packedAcc.canvasH) hboxesDisj)
    have hx := PipelineImpl.contained_shiftRect_imp
      (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
      (PipelineImpl.contained_orientRect (d := o.direction)
        (h := execution.packedAcc.canvasH) (hcontainB posB bi hposB hbiLen))
    have hy := PipelineImpl.contained_shiftRect_imp
      (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
      (PipelineImpl.contained_orientRect (d := o.direction)
        (h := execution.packedAcc.canvasH) (hcontainA posA ci hposA hciLen))
    rw [hbrect, hcrect, hlookupB posB bi hposB hbiLen, hlookupA posA ci hposA hciLen]
    exact PipelineImpl.not_meetsInterior_of_contained hdisjShift hx hy

end Layered
end Elegant

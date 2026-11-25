import Elegant.Layered.ExactBottomBracketVacancyProof
import Elegant.Layered.ExactFlatForeignLoopProof
import Elegant.Layered.LoopFootprintGroupHullProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem endpoint_preimage {boxes : List ModelBox} {side : Bool}
    {index other key : Nat} (hkey : key < boxes.length)
    (h : Compound.endpoint boxes side index other = key) : index = key := by
  cases hi : boxes[index]? <;> cases ho : boxes[other]?
  all_goals simp only [Compound.endpoint, hi, ho] at h
  all_goals first
    | exact h
    | split at h
      · exact h
      · split at h
        · exact h
        · unfold Compound.bottomIndex at h
          omega

private theorem endpoint_pair_ne {boxes : List ModelBox} {a b : Nat}
    (ha : a < boxes.length) (hb : b < boxes.length) (hne : a ≠ b) :
    Compound.endpoint boxes true a b ≠ Compound.endpoint boxes false b a := by
  intro heq
  by_cases hk : Compound.endpoint boxes true a b < boxes.length
  · have hfrom := endpoint_preimage (side := true) (index := a) (other := b) hk rfl
    have hto := endpoint_preimage hk heq.symm
    exact hne (hfrom.trans hto.symm)
  · exact lh_selfBottomNe ha hb hne rfl heq.symm hk

private theorem candidate_alias_positions
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {edge raw : Edge}
    (hedge : edge ∈ (componentCandidate execution.graph comp candidate).edges)
    (hsemantic : edge.original = { aliasEdgeOf inp raw with
      tail := comp.idxOf (aliasEdgeOf inp raw).tail,
      head := comp.idxOf (aliasEdgeOf inp raw).head }) :
    comp[edge.original.tail]? = some (aliasEdgeOf inp raw).tail ∧
      comp[edge.original.head]? = some (aliasEdgeOf inp raw).head := by
  have hb : edge.tail < comp.length ∧ edge.head < comp.length := by
    simpa only [componentCandidate_nodes, componentGraph, List.length_map] using
      candidate_edge_endpoints_bounded_general execution.graph comp candidate hcomp
        (sceneExecutionX_edges_bounded execution) hedge
  have hb' : edge.original.tail < comp.length ∧ edge.original.head < comp.length := by
    cases hr : edge.reversed
    · simpa [Edge.original, hr] using hb
    · simpa [Edge.original, hr] using And.intro hb.2 hb.1
  have ht : edge.original.tail = comp.idxOf (aliasEdgeOf inp raw).tail :=
    congrArg Edge.tail hsemantic
  have hh : edge.original.head = comp.idxOf (aliasEdgeOf inp raw).head :=
    congrArg Edge.head hsemantic
  have lookup (key : Nat) (hk : comp.idxOf key < comp.length) :
      comp[comp.idxOf key]? = some key :=
    (List.getElem?_eq_getElem hk).trans (congrArg some (List.getElem_idxOf hk))
  rw [ht, hh] at hb' ⊢
  exact ⟨lookup _ hb'.1, lookup _ hb'.2⟩

set_option maxHeartbeats 1200000 in
/-- A non-self route of a successful flat exact layout misses an unrelated
    fixed leaf, even when the scene presents that leaf as a group frame. -/
theorem layoutX_nonSelf_fixedLeaf_frame_miss
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutX exactIds inp o = .ok res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {boxId : String} {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == boxId) = some entry)
    (_hleaf : ExactFixedLeaf inp boxId)
    {frame : Box} (hframe : res.scene.boxes.find? (fun box => box.id == boxId) = some frame)
    {route : Route} (hroute : route ∈ res.scene.routes)
    (hfrom : route.fromId ≠ boxId) (hto : route.toId ≠ boxId)
    (hnonself : route.fromId ≠ route.toId) :
    ¬ Polyline.hitsRect route.points frame.rect := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hroute
  have hkLen : k < inp.routes.length := by
    rw [← sceneOf_routes_length execution.params inp o execution.lines
      execution.packedAcc execution.measured, ← execution.scene_eq]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨packed, c, q, candidate, run, loops, area, hIndex, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_sourceX hkLen
  have hrouteAt : res.scene.routes[edge.decl]? = some route := by rwa [hdecl]
  let cg := componentCandidate execution.graph q.1.1 candidate
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  obtain ⟨hparts, _⟩ := actual_components_parts_geometryX (by rfl) execution.components_eq
  have hcomp : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
  obtain ⟨index, model, raw, fromBox, toBox, hmodel, _, hmodelDecl,
    hrawFrom, hrawFromId, hrawTo, hrawToId, hsemantic⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq
      (List.mem_of_getElem? hedge)
  have hmodelAt : inp.routes[edge.decl]? = some model := by rwa [hmodelDecl]
  have hmodelAt' := List.getElem?_eq_some_iff.mp hmodelAt
  have hout := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured edge.decl hmodelAt'.1
  rw [← execution.scene_eq, hmodelAt'.2] at hout
  have houtEq := Option.some.inj (hrouteAt.symm.trans hout)
  have hfromId : fromBox.id = route.fromId :=
    hrawFromId.trans (congrArg Route.fromId houtEq).symm
  have htoId : toBox.id = route.toId :=
    hrawToId.trans (congrArg Route.toId houtEq).symm
  have hrawNe : raw.tail ≠ raw.head := by
    intro heq
    rw [heq] at hrawFrom
    have hids := congrArg ModelBox.id (Option.some.inj (hrawFrom.symm.trans hrawTo))
    exact hnonself (hfromId.symm.trans (hids.trans htoId))
  have hfromBound : raw.tail < (preparedBoxes inp).length := by
    simpa only [preparedBoxes, List.length_map] using (List.getElem?_eq_some_iff.mp hrawFrom).1
  have htoBound : raw.head < (preparedBoxes inp).length := by
    simpa only [preparedBoxes, List.length_map] using (List.getElem?_eq_some_iff.mp hrawTo).1
  have haliasNe : (aliasEdgeOf inp raw).tail ≠ (aliasEdgeOf inp raw).head :=
    endpoint_pair_ne hfromBound htoBound hrawNe
  obtain ⟨htailPos, hheadPos⟩ :=
    candidate_alias_positions execution hcomp (List.mem_of_getElem? hedge) hsemantic
  have hnonloop : edge.tail ≠ edge.head := by
    intro hself
    have hself' : edge.original.tail = edge.original.head := by
      cases hr : edge.reversed <;> simp [Edge.original, hr, hself]
    rw [hself'] at htailPos
    exact haliasNe (Option.some.inj (htailPos.symm.trans hheadPos))
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup execution.graph q.1.1 candidate
      (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
  have hloop := componentLoops_excludes_ordinary_decl hloops hnd hedge hnonloop
  have hi : hIndex < cg.edges.length := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  obtain ⟨native, hnative, horiginal, _⟩ := componentRunX_route_of_index hrun hi
  have hrouteLocal : q.1.2.routes[hIndex]? = some (edge.decl,
      native.points.map (shiftPoint (0 - bounds.minX) (-bounds.minY))) := by
    have hget := X_placeComponentExact_route_entry_of_producer hrun 0 loops hIndex hi
      (by simpa only [he] using hloop)
    rw [hpart]
    simpa only [he, (List.getElem?_eq_some_iff.mp hnative).2] using hget
  have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
    rw [hpart]
    unfold placeComponentExact
    dsimp only
    rw [List.map_map]
    change (cg.edges.zipIdx.map (fun q => q.1.decl)).Nodup
    rw [zipIdx_map_comp (fun e : Edge => e.decl)]
    exact hnd
  obtain ⟨key, hframeAt⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hframe)
  obtain ⟨source, hsource, hsourceId, _, _, _⟩ := sceneBox_source_rectX execution hframeAt
  have hid : source.id = boxId := hsourceId.symm.trans (by simpa using List.find?_some hframe)
  have hkeyLen := (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨part, pos, c', _, hentry, hpos⟩ := key_part_positionX execution hkeyLen
  by_cases hsame : c' = c
  · subst c'
    have hpartEq : part = q.1 := Option.some.inj (hentry.symm.trans (zip_getElem?_left hselected))
    subst part
    have hkeyBound : key < (preparedBoxes inp).length := by
      simpa only [preparedBoxes, List.length_map] using hkeyLen
    have hforeign : ∀ {side : Bool} {index other position : Nat} {endpoint : ModelBox},
        q.1.1[position]? = some (Compound.endpoint (preparedBoxes inp) side index other) →
        inp.boxes[index]? = some endpoint → endpoint.id ≠ boxId → pos ≠ position := by
      intro side index other position endpoint hlookup hendpoint hne heq
      rw [← heq] at hlookup
      have halias := Option.some.inj (hlookup.symm.trans hpos)
      rw [endpoint_preimage hkeyBound halias] at hendpoint
      exact hne ((congrArg ModelBox.id (Option.some.inj (hendpoint.symm.trans hsource))).trans hid)
    have hfromPos : pos ≠ edge.original.tail :=
      hforeign (side := true) (index := raw.tail) (other := raw.head)
        htailPos hrawFrom (fun heq => hfrom (hfromId.symm.trans heq))
    have htoPos : pos ≠ edge.original.head :=
      hforeign (side := false) (index := raw.head) (other := raw.tail)
        hheadPos hrawTo (fun heq => hto (htoId.symm.trans heq))
    have hpositions : pos ≠ edge.tail ∧ pos ≠ edge.head := by
      cases hr : edge.reversed
      · simpa [Edge.original, hr] using And.intro hfromPos htoPos
      · simpa [Edge.original, hr] using And.intro htoPos hfromPos
    have hsourceFixed : inp.fixedSizes.find? (fun row => row.1 == source.id) = some entry := by
      simpa only [hid] using hfixed
    have hlinesEq := execution.lines_eq
    unfold boxLines at hlinesEq
    have hkLine : key < execution.lines.length := by
      rw [show execution.lines.length = inp.boxes.length by
        simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlinesEq).1]
      exact hkeyLen
    obtain ⟨base, hbase, _, hzero, _, _⟩ := measuredGraph_fixed_node_dims execution.graph0_eq
      (List.getElem?_eq_getElem hkLine) hsource hsourceFixed
    obtain ⟨node, hnode, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hbase
    have hnodeLocal : cg.nodes[pos]? = some node := component_node_lookupX hpos hnode
    have hposBound := componentRunX_original_nodes_covered hrun pos
      (List.getElem?_eq_some_iff.mp hnodeLocal).1
    have hplain : (cg.nodes.getD pos default).border ≠ -2 := by
      rw [List.getD_eq_getElem?_getD, hnodeLocal, Option.getD_some, hborder, hzero]
      decide
    have hshape := componentCandidate_shape (components_nodup execution.graph q.1.1 hcomp)
      (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate
    have hbottom : ExactBottomBracketVacant run :=
      sceneExecutionX_bottomBracketVacant execution hwf hfp hcomp hrun
    obtain ⟨first, last, hfirst, hlast, htail, hhead⟩ :=
      X_componentRun_chain_endpoints hrun hedge hnonloop
    have hmiss := componentRunX_route_avoids_real_of_bottom_bracket
      (checkedParams_valid execution.checked) hshape hrun hbottom
      (List.mem_of_getElem? hnative) (start := first) (finish := last)
      (by rwa [horiginal]) (by rwa [horiginal])
      hposBound (X_componentRun_source_isReal hrun hnodeLocal)
      (by rw [htail]; exact hpositions.1) (by rw [hhead]; exact hpositions.2)
    rw [← plain_frame_eq_boxRect execution.params cg run pos hposBound hplain] at hmiss
    have hbox := X_DumpLookup_holds exactIds execution hwf packed hpacked hselected hpart hpos hsource
    have hframeLookup : res.scene.layoutDump.box? source.id = some frame := by
      change res.scene.boxes.find? (fun box => box.id == source.id) = some frame
      rwa [hid]
    have hscene := X_chosen_part_route_from_points execution packed hpacked hselected
      hrouteLocal hpartNodup hmodelAt
    rw [Option.some.inj (hrouteAt.symm.trans hscene), Option.some.inj (hframeLookup.symm.trans hbox)]
    exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
      execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
  · exact execution.chosenRoute_misses_other_part hpacked hselected hrouteLocal hpartNodup
      hmodelAt hrouteAt (Ne.symm hsame) hentry hpos hframeAt

end Elegant.Layered.PipelineImpl

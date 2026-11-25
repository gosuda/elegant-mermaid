import Elegant.Layered.ExactBottomBracketVacancyProof
import Elegant.Layered.ExactFlatC6BridgeChainProof
import Elegant.Layered.ExactFlatForeignLoopProof
import Elegant.Layered.RankSiblingDisjoint

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Clearance of an unrelated real node uses the coordinates after exact-rank
reservation, including the actual bottom-marker brackets. -/
theorem SceneExecutionX.route_avoids_foreign_real
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {native : EdgeRoute} (hnative : native ∈ run.routes) {first last v : Nat}
    (hfirst : (RouteImpl.edgesOf run.proper native.original).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper native.original).getLast? = some last)
    (hv : v < run.proper.nodes.length) (hreal : RouteImpl.IsReal run.proper v)
    (hfrom : v ≠ (RouteImpl.edgeAt run.proper first).tail)
    (hto : v ≠ (RouteImpl.edgeAt run.proper last).head) :
    ¬ Polyline.hitsRect native.points (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate
  exact componentRunX_route_avoids_real_of_bottom_bracket (checkedParams_valid execution.checked)
    hshape hrun (sceneExecutionX_bottomBracketVacant execution hwf hfp hcomp hrun)
    hnative hfirst hlast hv hreal hfrom hto

set_option maxHeartbeats 1200000 in
/-- Exact chain routes miss foreign exclusive boxes. In the same part, the
source box determines the real run node; across parts, the emitted route and
box are confined by axis-separated shelves, even if a shelf is degenerate. -/
theorem x6_chainCaseW_holds (exactIds : List String) : X6_ChainCaseW exactIds := by
  intro inp o res execution _hfix hwf hfp _hclear _hbridge r b _hr hb hex hscope
    key hkget _hkeylen packed c q candidate run loops i edge area hpacked
    hselected hrun hloops hpart hedge hdecl hfind
  let cg := componentCandidate execution.graph q.1.1 candidate
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  have hrouteAt : res.scene.routes[edge.decl]? = some r := by rwa [hdecl]
  have hloopen : ∀ l ∈ loops, l.1 ≠ edge.decl := by
    intro l hl he
    exact (List.find?_eq_none.mp hfind l hl) (by simp [he])
  have hi : i < cg.edges.length := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  obtain ⟨native, hnative, horiginal, _⟩ := componentRunX_route_of_index hrun hi
  have hrouteLocal : q.1.2.routes[i]? = some (edge.decl,
      native.points.map (shiftPoint (0 - bounds.minX) (-bounds.minY))) := by
    have hget := X_placeComponentExact_route_entry_of_producer hrun 0 loops i hi
      (by simpa only [he] using hloopen)
    rw [hpart]
    simpa only [he, (List.getElem?_eq_some_iff.mp hnative).2] using hget
  have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
    rw [hpart]
    unfold placeComponentExact
    dsimp only
    rw [List.map_map]
    change (cg.edges.zipIdx.map (fun q => q.1.decl)).Nodup
    rw [zipIdx_map_comp (fun e : Edge => e.decl)]
    exact componentCandidate_decls_nodup execution.graph q.1.1 candidate
      (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
  obtain ⟨_, model, _, _, _, hmodel, _, hmodelDecl, _, _, _, _, _⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq
      (List.mem_of_getElem? hedge)
  have hmodelAt : inp.routes[edge.decl]? = some model := by rwa [hmodelDecl]
  obtain ⟨boxKey, hboxAt⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨source, hsource, hboxId, _, hboxExclusive, _⟩ :=
    sceneBox_source_rectX execution hboxAt
  have hboxKeyLen := (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨part, pos, c', _, hentry, hpos⟩ := key_part_positionX execution hboxKeyLen
  by_cases hsame : c' = c
  · subst c'
    have hpartEq : part = q.1 := Option.some.inj (hentry.symm.trans (zip_getElem?_left hselected))
    subst part
    obtain ⟨hparts, _⟩ := actual_components_parts_geometryX (by rfl) execution.components_eq
    have hcomp : q.1.1 ∈ components execution.graph := by
      rw [← hparts]
      exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
    have hedgemem := List.mem_of_getElem? hedge
    have hnonloop : edge.tail ≠ edge.head := by
      intro hself
      have hbound := (candidate_edge_endpoints_bounded_general execution.graph q.1.1 candidate
        hcomp (sceneExecutionX_edges_bounded execution) hedgemem).1
      obtain ⟨placement, hplacement⟩ := componentLoops_entry_of_self_edge hloops
        hedgemem hbound hself
      exact hloopen (edge.decl, placement) hplacement rfl
    obtain ⟨first, last, hfirst, hlast, _, _⟩ := X_componentRun_chain_endpoints hrun hedge hnonloop
    have hfirst' : (RouteImpl.edgesOf run.proper native.original).head? = some first := by
      simpa only [horiginal] using hfirst
    have hlast' : (RouteImpl.edgesOf run.proper native.original).getLast? = some last := by
      simpa only [horiginal] using hlast
    have hnd := x_exclusiveRunNodeDecl_holds exactIds inp o res execution q.1.1
      candidate run hcomp hrun pos boxKey source hpos hsource
    obtain ⟨hstartScoped, hendScoped⟩ := x6_scopedW_holds exactIds execution hwf hfp
      q.1.1 candidate run hcomp hrun i edge native r hedge hnative horiginal hrouteAt
      first last hfirst' hlast'
    have hsourceScope : source.id ∉ LayoutDump.routeScope res.scene.layoutDump r := by
      simpa only [hboxId] using hscope
    have hfrom : pos ≠ (RouteImpl.edgeAt run.proper first).tail := by
      intro heq
      exact hsourceScope (hstartScoped source (by rwa [← heq, hnd]))
    have hto : pos ≠ (RouteImpl.edgeAt run.proper last).head := by
      intro heq
      exact hsourceScope (hendScoped source (by rwa [← heq, hnd]))
    have hnotGroup := wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource)
      (hboxExclusive.symm.trans hex)
    have hlines := execution.lines_eq
    unfold boxLines at hlines
    have hlineLen : execution.lines.length = inp.boxes.length := by
      simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
    have hkeyLine : boxKey < execution.lines.length := by rwa [hlineLen]
    obtain ⟨node₀, hnode₀, hzero⟩ := measuredGraph_exclusive_node_border_zero
      execution.checked execution.graph0_eq (List.getElem?_eq_getElem hkeyLine) hsource hnotGroup
    obtain ⟨node, hnode, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hnode₀
    have hnodeLocal : cg.nodes[pos]? = some node := component_node_lookupX hpos hnode
    have hposBound := componentRunX_original_nodes_covered hrun pos
      (List.getElem?_eq_some_iff.mp hnodeLocal).1
    have hplain : (cg.nodes.getD pos default).border ≠ -2 := by
      rw [List.getD_eq_getElem?_getD, hnodeLocal, Option.getD_some, hborder, hzero]
      decide
    have hmiss := execution.route_avoids_foreign_real hwf hfp hcomp hrun
      (List.mem_of_getElem? hnative) hfirst' hlast' hposBound
      (X_componentRun_source_isReal hrun hnodeLocal) hfrom hto
    rw [← plain_frame_eq_boxRect execution.params cg run pos hposBound hplain] at hmiss
    have hids : (res.scene.boxes.map (·.id)).Nodup := by
      rw [execution.boxes_eq_mapX, List.map_map]
      change (inp.boxes.zipIdx.map (fun q => q.1.id)).Nodup
      rw [zipIdx_map_comp (fun box : ModelBox => box.id)]
      exact Model.boxIds_nodup hwf
    have hboxLookup : res.scene.layoutDump.box? source.id = some b := by
      change res.scene.boxes.find? (fun box => box.id == source.id) = some b
      rw [← hboxId]
      exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hids b hb
    have hbox := X_DumpLookup_holds exactIds execution hwf packed hpacked hselected
      hpart hpos hsource
    have hscene := X_chosen_part_route_from_points execution packed hpacked hselected
      hrouteLocal hpartNodup hmodelAt
    rw [Option.some.inj (hrouteAt.symm.trans hscene), Option.some.inj (hboxLookup.symm.trans hbox)]
    exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
      execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
  · exact execution.chosenRoute_misses_other_part hpacked hselected hrouteLocal hpartNodup
      hmodelAt hrouteAt (Ne.symm hsame) hentry hpos hboxAt

end Elegant.Layered.PipelineImpl

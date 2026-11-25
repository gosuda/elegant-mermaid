import Elegant.Layered.ExactBottomBracketVacancyProof
import Elegant.Layered.ExactFlatC6BridgeChainProof
import Elegant.Layered.ExactFlatForeignLoopProof
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.ExactStraightenFacts

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
  obtain ⟨source, hsource, hboxId, _, hboxExclusive, hboxRect⟩ :=
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
    have hsuff : res.scene.routes[edge.decl]? =
        some (Route.mk model.id model.fromId model.toId model.orthogonal
          (native.points.map (routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY))) →
        ¬ Polyline.hitsRect r.points b.rect := by
      intro hscene0
      have hrEq := Option.some.inj (hrouteAt.symm.trans hscene0)
      have hbEq := Option.some.inj (hboxLookup.symm.trans hbox)
      rw [hrEq, hbEq]
      exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
        execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
    rcases hscene with hscene | ⟨ptsCorr, hcor, hrouteC⟩
    · exact hsuff hscene
    · obtain ⟨_cx0, _y0, _y1, _hltCor, hptsCorrEq⟩ := hcor
      have hgetD : execution.straightAcc.routes.getD edge.decl [] = ptsCorr :=
      ExactStraighten.straight_points_of_scene execution hrouteC
      have hptsNe : ptsCorr ≠ [] := by
        rw [hptsCorrEq]
        intro hcon
        simp at hcon
      have hpts : execution.straightAcc.routes[edge.decl]? = some ptsCorr := by
        have hgd : (execution.straightAcc.routes[edge.decl]?.getD []) = ptsCorr := by
          have h := hgetD
          rw [Array.getD_eq_getD_getElem?] at h
          exact h
        cases ho : execution.straightAcc.routes[edge.decl]? with
        | none =>
          simp only [ho, Option.getD_none] at hgd
          exact absurd hgd.symm hptsNe
        | some v =>
          simp only [ho, Option.getD_some] at hgd
          exact congrArg Option.some hgd
      rcases ExactStraighten.route_cases_clear execution X_componentRun_normalized_source hpts with hpackedPts | ⟨qW, ctx0W, oxW, oyW, iW, eW,
        routingW, spanW, hmemW, hctxW, hoffW, heW, hdeclW, hspanW, hptsW, hclearW⟩
      · have hsize : edge.decl < execution.componentsAcc.routes.size := by
          rw [← packAcc_routes_size execution.packed_eq]
          exact (Array.getElem?_eq_some_iff.mp hpackedPts).1
        have heP := (List.getElem?_eq_some_iff.mp hedge).2
        have hgetP := X_placeComponentExact_route_entry_of_producer hrun 0 loops i hi
          (by simpa only [he] using hloopen)
        have hpartRoutes : q.1.2.routes =
            (placeComponentExact execution.params
              (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
              loops).routes := by
          rw [hpart]
        rw [← hpartRoutes] at hgetP
        have hpackedRoute := ExactStraighten.actual_components_packAcc_routes_getD (by rfl)
          execution.components_eq
          (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
          packed execution.packed_eq hpacked c q hselected i _ _ [] hgetP hpartNodup
          (by rw [heP]; exact hsize)
        have hnativeGet := (List.getElem?_eq_some_iff.mp hnative).2
        have hk' : edge.decl < inp.routes.length := (List.getElem?_eq_some_iff.mp hmodelAt).1
        have hmodelEq : inp.routes[edge.decl]'hk' = model :=
          Option.some.inj ((List.getElem?_eq_getElem hk').symm.trans hmodelAt)
        have hbridge : execution.packedAcc.routes.getD edge.decl [] =
            execution.straightAcc.routes.getD edge.decl [] := by
          rw [hgetD, Array.getD_eq_getD_getElem?, hpackedPts, Option.getD_some]
        have hneg : -bounds.minY = 0 - bounds.minY := by omega
        have hstraight0 := sceneOf_routes_getElem? execution.params inp o execution.lines
          execution.straightAcc execution.measured edge.decl hk'
        rw [← execution.scene_eq] at hstraight0
        rw [ExactStraighten.straight_canvasH execution] at hstraight0
        rw [heP, hbridge] at hpackedRoute
        rw [hneg] at hpackedRoute
        rw [hmodelEq] at hstraight0
        rw [hpackedRoute, routePointTransport_eq, hnativeGet] at hstraight0
        exact hsuff hstraight0
      · have hrole : source.role = .node := by
          cases h : source.role with
          | node => rfl
          | group => exact absurd h hnotGroup
        have hcompSize : execution.componentsAcc.rects.size = inp.boxes.length :=
          execution.components_rects_size
        have hpackSize : execution.packedAcc.rects.size = execution.componentsAcc.rects.size :=
          installed_packAcc_rects_size execution.packed_eq
        have hsizeW : boxKey < execution.packedAcc.rects.size := by
          rw [hpackSize, hcompSize]
          exact hboxKeyLen
        have hneF : execution.packedAcc.rects[boxKey]? ≠ none := by
          intro hcon
          have hle := Array.getElem?_eq_none_iff.mp hcon
          omega
        obtain ⟨rectW, hlookW⟩ := Option.ne_none_iff_exists'.mp hneF
        have hflag : decide (source.role == BoxRole.node) = true := by
          have hb : (source.role == BoxRole.node) = true := by
            rw [hrole]
            exact beq_self_eq_true _
          rw [decide_eq_true_eq]
          exact hb
        have hmemG := ExactStraighten.installed_global_mem hlookW hsource
        rw [hflag] at hmemG
        have hcond := List.all_eq_true.mp hclearW _ (List.mem_append.mpr (Or.inl hmemG))
        have hcondBeta : (rectW == spanW.tailRect || rectW == spanW.headRect || false ||
            !Polyline.hitsRectB [⟨spanW.column, spanW.top⟩, ⟨spanW.column, spanW.bottom⟩]
              rectW) = true := hcond
        obtain ⟨eInv, heInv, _heligInv, _hdeclInv, hltW⟩ := ExactStraighten.straightSpanOf_inv hspanW
        have hshapeW : spanW.top = spanW.tailRect.y + spanW.tailRect.h ∧
            spanW.bottom = spanW.headRect.y := by
          have hspan2 := hspanW
          unfold straightSpanOf at hspan2
          cases he2 : ({ ctx0W with dx := ctx0W.dx + oxW, dy := ctx0W.dy + oyW }).proper.edges[iW]? with
          | none =>
            simp only [he2] at hspan2
            cases hspan2
          | some e2 =>
            simp only [he2] at hspan2
            cases hel : !straightEdgeEligible { ctx0W with dx := ctx0W.dx + oxW, dy := ctx0W.dy + oyW }
              routingW iW e2 with
            | true =>
              simp only [hel] at hspan2
              cases hspan2
            | false =>
              simp only [hel] at hspan2
              cases hgeom : straightGeom { ctx0W with dx := ctx0W.dx + oxW, dy := ctx0W.dy + oyW }
                routingW iW e2 with
              | mk tw hw th hh tailLeft headLeft lo hi cx =>
                simp only [hgeom] at hspan2
                by_cases hlo : lo > hi
                · rw [ite_eq_left hlo] at hspan2
                  cases hspan2
                · rw [ite_eq_right hlo] at hspan2
                  obtain ⟨pin, _, hspan2⟩ := bind_ok hspan2
                  obtain ⟨top, _, hspan2⟩ := bind_ok hspan2
                  obtain ⟨bottom, _, hspan2⟩ := bind_ok hspan2
                  by_cases hge : top ≥ bottom
                  · rw [ite_eq_left hge] at hspan2
                    cases hspan2
                  · rw [ite_eq_right hge] at hspan2
                    obtain ⟨column, _, hspan2⟩ := bind_ok hspan2
                    have hs := Option.some.inj (Except.ok.inj hspan2)
                    subst hs
                    refine ⟨by dsimp only; omega, by dsimp only⟩
        have hptsEqW : ptsCorr = [⟨spanW.column, spanW.top⟩, ⟨spanW.column, spanW.bottom⟩] := by
          rw [hptsW]
          rfl
        have hmissW : ¬ Polyline.hitsRect ptsCorr rectW := by
          rw [hptsEqW]
          cases hEqT : rectW == spanW.tailRect with
          | true =>
            have hRectEqT : rectW = spanW.tailRect := beq_iff_eq.mp hEqT
            rw [hRectEqT]
            exact ExactStraighten.corridor_misses_tail hshapeW.1 hltW
          | false =>
            cases hEqH : rectW == spanW.headRect with
            | true =>
              have hRectEqH : rectW = spanW.headRect := beq_iff_eq.mp hEqH
              rw [hRectEqH]
              exact ExactStraighten.corridor_misses_head hshapeW.2 hltW
            | false =>
              cases hB : Polyline.hitsRectB [⟨spanW.column, spanW.top⟩,
                  ⟨spanW.column, spanW.bottom⟩] rectW with
              | true =>
                rw [hEqT, hEqH, hB] at hcondBeta
                cases hcondBeta
              | false =>
                exact (Polyline.hitsRectB_eq_false_iff _ _).mp hB
        have hbV : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH rectW) := by
          have hget : execution.packedAcc.rects.getD boxKey default = rectW := by
            rw [Array.getD_eq_getD_getElem?, hlookW, Option.getD_some]
          rw [hboxRect, hget]
        have hrouteEqC : r.points =
            ptsCorr.map fun p => shiftPoint execution.params.canvasMargin
              execution.params.canvasMargin
              (orientPoint o.direction execution.packedAcc.canvasH p) :=
          congrArg Route.points (Option.some.inj (hrouteAt.symm.trans hrouteC))
        rw [hrouteEqC, hbV]
        exact not_hitsRect_shift_orient _ _ _ _ _ _ hmissW
  · exact execution.chosenRoute_misses_other_part hpacked hselected hrouteLocal hpartNodup
      hmodelAt hrouteAt (Ne.symm hsame) hentry hpos hboxAt

end Elegant.Layered.PipelineImpl

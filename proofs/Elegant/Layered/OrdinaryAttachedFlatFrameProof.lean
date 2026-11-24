import Elegant.Layered.ComponentRunPlainEndpointMissProof
import Elegant.Layered.CgShape
import Elegant.Layered.ExecutedPortsFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem fixed_endpoint_unaliased {inp : Input} {index other : Nat}
    {source : ModelBox} (side : Bool)
    (hsource : inp.boxes[index]? = some source)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true) :
    Compound.endpoint (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) side index other = index := by
  unfold Compound.endpoint
  cases hother : inp.boxes[other]? <;>
    simp only [List.getElem?_map, hsource, hfixed, hother,
      Option.map_some, Option.map_none, ↓reduceIte] <;> rfl

private theorem component_idxOf_lookup {component : List Nat} {key : Nat}
    (hkey : key ∈ component) : component[component.idxOf key]? = some key :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hkey)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hkey)))

private theorem components_fold_route_size (P : Params) (inp : Input) (o : Options)
    (g : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp labels) start = .ok out →
      out.routes.size = start.routes.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, hnext, hrest⟩ := bind_ok h
    exact (components_fold_route_size P inp o g labels comps next out hrest).trans
      (layoutComponent_sizes hnext).2.1.symm

set_option maxHeartbeats 1000000 in
/-- An ordinary flat route misses the interior of either attached fixed frame.
The fixed box remains the endpoint after aliasing, and packing applies the same
translation and orientation to the native route and its endpoint frame. -/
theorem SceneExecution.attached_fixed_frame_miss
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {boxId : String} {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == boxId) = some entry)
    {frame : Box} (hframe : res.scene.layoutDump.box? boxId = some frame)
    {pr : Route} (hpr : pr ∈ res.scene.routes)
    (hattach : pr.fromId = boxId ∨ pr.toId = boxId) :
    ¬ Polyline.hitsRect pr.points frame.rect := by
  obtain ⟨routeKey, hprIndex⟩ := List.mem_iff_getElem?.mp hpr
  have hrouteKey : routeKey < inp.routes.length := by
    rw [← sceneOf_routes_length execution.params inp o execution.lines
      execution.packedAcc execution.measured, ← execution.scene_eq]
    exact (List.getElem?_eq_some_iff.mp hprIndex).1
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_source hrouteKey
  let cg := componentCandidate execution.graph q.1.1 candidate
  let bounds := placeBounds execution.params cg run execution.measured loops
  obtain ⟨global, hglobal, hglobalTail, hsemantic⟩ :=
    componentCandidate_semantic_source (List.mem_of_getElem? hedge)
  obtain ⟨index, route, raw, hroute, hraw, halias⟩ :=
    measuredGraph_edge_source execution.graph_eq hglobal
  obtain ⟨hrawDecl, hrawRev, source, target, hsource, hsourceId, htarget, htargetId⟩ :=
    edgeOf_semantic_endpoints hraw
  have hindex : routeKey = index := by
    calc
      routeKey = edge.decl := hdecl.symm
      _ = global.decl := by
        simpa only [Edge.original_decl] using congrArg Edge.decl hsemantic
      _ = raw.decl := by rw [halias, Compound.aliasEdge_decl]
      _ = index := hrawDecl
  rw [← hindex] at hroute
  have hrouteEq : inp.routes[routeKey]'hrouteKey = route :=
    (List.getElem?_eq_some_iff.mp hroute).2
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured routeKey hrouteKey
  rw [← execution.scene_eq] at hscene
  have hprEq := Option.some.inj (hprIndex.symm.trans hscene)
  have hfrom : pr.fromId = route.fromId :=
    (congrArg Route.fromId hprEq).trans (congrArg ModelRoute.fromId hrouteEq)
  have hto : pr.toId = route.toId :=
    (congrArg Route.toId hprEq).trans (congrArg ModelRoute.toId hrouteEq)
  have hparts := (actual_components_parts_geometry (by rfl) execution.components_eq).1
  have hcomponent : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
  obtain ⟨comp, hcomp, htail, hhead⟩ :=
    components_edge_endpoints (sceneExecution_edges_bounded execution)
      (List.mem_append_left _ hglobal)
  have hcompEq := components_shared_member_eq hcomp hcomponent htail hglobalTail
  have hglobalHead : global.head ∈ q.1.1 := by
    rw [← hcompEq]
    exact hhead
  have horiginal : global.original = global := by
    have hrev : global.reversed = false := by rw [halias]; exact hrawRev
    cases global with
    | mk tail head minLen decl reversed => cases hrev; rfl
  rw [horiginal] at hsemantic
  have hsides : (edge.original.tail = edge.tail ∨ edge.original.tail = edge.head) ∧
      (edge.original.head = edge.tail ∨ edge.original.head = edge.head) := by
    cases hrev : edge.reversed <;> simp [Edge.original, hrev]
  have hfixedAny : inp.fixedSizes.any (fun fixed => fixed.1 == boxId) = true :=
    List.any_eq_true.mpr
      ⟨entry, List.mem_of_find?_eq_some hfixed, by simpa using List.find?_some hfixed⟩
  obtain ⟨v, boxKey, src, hv, hsrc, hsrcId, hside⟩ :
      ∃ (v boxKey : Nat) (src : ModelBox),
        q.1.1[v]? = some boxKey ∧ inp.boxes[boxKey]? = some src ∧ src.id = boxId ∧
          (v = edge.tail ∨ v = edge.head) := by
    rcases hattach with ha | ha
    · have hid := hsourceId.trans (hfrom.symm.trans ha)
      have hglobalKey : global.tail = raw.tail := by
        rw [halias]
        exact fixed_endpoint_unaliased true hsource (by simpa only [hid] using hfixedAny)
      have hv : edge.original.tail = q.1.1.idxOf global.tail := congrArg Edge.tail hsemantic
      refine ⟨edge.original.tail, raw.tail, source, ?_, hsource, hid, hsides.1⟩
      rw [hv, ← hglobalKey]
      exact component_idxOf_lookup hglobalTail
    · have hid := htargetId.trans (hto.symm.trans ha)
      have hglobalKey : global.head = raw.head := by
        rw [halias]
        exact fixed_endpoint_unaliased false htarget (by simpa only [hid] using hfixedAny)
      have hv : edge.original.head = q.1.1.idxOf global.head := congrArg Edge.head hsemantic
      refine ⟨edge.original.head, raw.head, target, ?_, htarget, hid, hsides.2⟩
      rw [hv, ← hglobalKey]
      exact component_idxOf_lookup hglobalHead
  have hentry := chosen_part_frame_entry hpart hv
  dsimp only at hentry
  have hbox := execution.part_entry_box_lookup hwf packed hpacked hselected hentry hsrc
  have hsrcFrame : res.scene.layoutDump.box? src.id = some frame := by
    simpa only [hsrcId] using hframe
  have hrect := congrArg Box.rect (Option.some.inj (hsrcFrame.symm.trans hbox))
  simp only [shiftRect_pack_normalize] at hrect
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
  have hvLen := (List.getElem?_eq_some_iff.mp hv).1
  obtain ⟨points, hpoints, hmiss⟩ : ∃ points : List Point,
      pr.points = points.map (routePointTransport execution.params.canvasMargin o.direction
        execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY) ∧
      ¬ Polyline.hitsRect points (frameRect execution.params cg run v) := by
    by_cases hself : edge.tail = edge.head
    · have hvTail : v = edge.tail := hside.elim id (fun h => h.trans hself.symm)
      have htailLen : edge.tail < cg.nodes.length := by
        rw [← hvTail]
        dsimp only [cg]
        rw [componentCandidate_nodes]
        simpa only [componentGraph, List.length_map] using hvLen
      obtain ⟨loop, hloop, _, hloopDecl, hplaced⟩ :=
        componentLoops_emitted_self_edge hloops hedge htailLen hself 0
      obtain ⟨owner, _, origin, horigin, horiginDecl, horiginTail, _, hmiss⟩ :=
        componentLoops_entry_misses_owner hloops hloop
      have hsame : origin = edge := nodup_map_eq_of_mem hnd (List.mem_filter.mp horigin).1
        (List.mem_of_getElem? hedge) (horiginDecl.symm.trans hloopDecl)
      have howner : owner = v :=
        horiginTail.symm.trans ((congrArg Edge.tail hsame).trans hvTail.symm)
      have hpartRoutes : q.1.2.routes =
          (placeComponent execution.params cg run 0 execution.measured loops).routes := by
        rw [hpart]
      rw [← hpartRoutes] at hplaced
      have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
        rw [hpartRoutes]
        exact placeComponent_routes_decls_nodup execution.params cg run 0
          execution.measured loops hnd
      have hsize : execution.componentsAcc.routes.size = inp.routes.length := by
        have h := components_fold_route_size execution.params inp o execution.graph
          execution.measured _ _ _ execution.components_eq
        simpa only [Array.size_replicate] using h
      have hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
        rw [hdecl, hsize]
        exact hrouteKey
      have hpackedRoute := Elegant.Layered.actual_components_packAcc_routes_getD
        (by rfl) execution.components_eq (measuredGraph_decls_nodup execution.graph_eq)
        packed execution.packed_eq hpacked c q hselected i _ _ [] hplaced hpartNodup hrouteSize
      rw [hdecl] at hpackedRoute
      rw [hpackedRoute, routePointTransport_eq] at hscene
      rw [howner] at hmiss
      exact ⟨loop.2.points, congrArg Route.points (Option.some.inj (hprIndex.symm.trans hscene)),
        hmiss⟩
    · have hnoLoop := componentLoops_excludes_ordinary_decl hloops hnd hedge hself
      obtain ⟨_, native, _, hnative, horig, hsceneNative⟩ :=
        execution.chosen_part_route_entry packed hpacked hselected hrun hpart hedge hnoLoop
      have hparams := checkedParams_valid execution.checked
      have hshape : CgShape cg := componentCandidate_shape
        (components_nodup _ _ hcomponent) (measuredGraph_shape execution.graph_eq) candidate
      obtain ⟨first, last, hfirst, hlast, htail, hhead⟩ :=
        componentRun_chain_endpoints hparams hnd hshape hrun hedge hself
      have hsrcFixed : inp.fixedSizes.find? (fun fixed => fixed.1 == src.id) = some entry := by
        simpa only [hsrcId] using hfixed
      have hsrcAt : inp.boxes[q.1.1[v]'hvLen]? = some src := by
        rw [(List.getElem?_eq_some_iff.mp hv).2]
        exact hsrc
      obtain ⟨node, hnode, hborder⟩ :=
        execution.fixed_candidate_node_border_zero q.1.1 candidate v hvLen hsrcAt hsrcFixed
      have hplain : (cg.nodes.getD v default).border = 0 := by
        simpa only [cg, List.getD_eq_getElem?_getD, hnode, Option.getD_some] using hborder
      have hend : v = (RouteImpl.edgeAt run.proper first).tail ∨
          v = (RouteImpl.edgeAt run.proper last).head :=
        hside.elim (fun ht => Or.inl (ht.trans htail.symm))
          (fun hh => Or.inr (hh.trans hhead.symm))
      have hfirst' : (RouteImpl.edgesOf run.proper native.original).head? = some first := by
        rw [horig]; exact hfirst
      have hlast' : (RouteImpl.edgesOf run.proper native.original).getLast? = some last := by
        rw [horig]; exact hlast
      have hmiss := componentRun_plain_endpoint_miss hparams hnd hshape hrun
        (List.mem_of_getElem? hnative) hfirst' hlast' hplain hend
      have hprDecl : res.scene.routes[edge.decl]? = some pr := by
        simpa only [hdecl] using hprIndex
      exact ⟨native.points, congrArg Route.points (Option.some.inj (hprDecl.symm.trans hsceneNative)),
        hmiss⟩
  have hmap : points.map (routePointTransport execution.params.canvasMargin o.direction
      execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY) =
      points.map (fun p => shiftPoint execution.params.canvasMargin execution.params.canvasMargin
        (orientPoint o.direction execution.packedAcc.canvasH
          (shiftPoint (q.2.x - bounds.minX) (q.2.y - bounds.minY) p))) := by
    apply List.map_congr_left
    intro p _
    rfl
  rw [hpoints, hrect, hmap]
  simpa only [List.map_map, Function.comp_def, bounds, cg] using
    not_hitsRect_shift_orient o.direction execution.packedAcc.canvasH
      execution.params.canvasMargin execution.params.canvasMargin _ _
      (not_hitsRect_shift (q.2.x - bounds.minX) (q.2.y - bounds.minY) _ _ hmiss)

end Elegant.Layered.PipelineImpl

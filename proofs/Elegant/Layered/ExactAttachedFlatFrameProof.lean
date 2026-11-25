import Elegant.Layered.ExactFlatC5SelfRoutes
import Elegant.Layered.ExpandChildParentAttachedMultiEdgeProof

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

/-- A route emitted by a flat exact execution misses the open interior of its
    attached fixed frame. The model route and frame share the same endpoint ID;
    fixing the frame prevents that endpoint from being replaced by a group alias. -/
theorem SceneExecutionX.attached_fixed_frame_miss
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {boxId : String} {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == boxId) = some entry)
    {frame : Box} (hframe : res.scene.layoutDump.box? boxId = some frame)
    {pr : Route} (hpr : pr ∈ res.scene.routes)
    (hattach : pr.fromId = boxId ∨ pr.toId = boxId) :
    ¬ Polyline.hitsRect pr.points frame.rect := by
  obtain ⟨key, hprIndex⟩ := List.mem_iff_getElem?.mp hpr
  have hkey : key < inp.routes.length := by
    rw [← sceneOf_routes_length execution.params inp o execution.lines
      execution.straightAcc execution.measured, ← execution.scene_eq]
    exact (List.getElem?_eq_some_iff.mp hprIndex).1
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_sourceX hkey
  obtain ⟨global, hglobal, hglobalTail, hsemantic⟩ :=
    componentCandidate_semantic_source (List.mem_of_getElem? hedge)
  have hglobal0 : global ∈ execution.graph0.edges := by
    simpa only [exactGraph_edges execution.graph_eq] using hglobal
  obtain ⟨index, route, raw, hroute, hraw, halias⟩ :=
    measuredGraph_edge_source execution.graph0_eq hglobal0
  obtain ⟨hrawDecl, hrawRev, source, target, hsource, hsourceId, htarget, htargetId⟩ :=
    edgeOf_semantic_endpoints hraw
  have hindex : key = index := by
    calc
      key = edge.decl := hdecl.symm
      _ = global.decl := by
        simpa only [Edge.original_decl] using congrArg Edge.decl hsemantic
      _ = raw.decl := by rw [halias, Compound.aliasEdge_decl]
      _ = index := hrawDecl
  rw [← hindex] at hroute
  have hrouteEq : inp.routes[key]'hkey = route := (List.getElem?_eq_some_iff.mp hroute).2
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.straightAcc execution.measured key hkey
  rw [← execution.scene_eq] at hscene
  have hprEq := Option.some.inj (hprIndex.symm.trans hscene)
  have hfrom : pr.fromId = route.fromId :=
    (congrArg Route.fromId hprEq).trans (congrArg ModelRoute.fromId hrouteEq)
  have hto : pr.toId = route.toId :=
    (congrArg Route.toId hprEq).trans (congrArg ModelRoute.toId hrouteEq)
  have hparts := (actual_components_parts_geometryX (by rfl) execution.components_eq).1
  have hcomponent : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
  obtain ⟨comp, hcomp, htail, hhead⟩ :=
    components_edge_endpoints (sceneExecutionX_edges_bounded execution)
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
  have hsrcFrame : res.scene.layoutDump.box? src.id = some frame := by
    simpa only [hsrcId] using hframe
  have hprDecl : res.scene.routes[edge.decl]? = some pr := by
    simpa only [hdecl] using hprIndex
  by_cases hself : edge.tail = edge.head
  · have hvTail : v = edge.tail := hside.elim id (fun h => h.trans hself.symm)
    rw [hvTail] at hv
    exact X_chosen_part_loop_attached_frame_miss execution hwf packed hpacked hselected
      hloops hpart hedge hself hv hsrc hprDecl hsrcFrame
  · have hsrcFixed : inp.fixedSizes.find? (fun fixed => fixed.1 == src.id) = some entry := by
      simpa only [hsrcId] using hfixed
    exact X_chosen_part_nonloop_attached_frame_miss execution hwf packed hpacked hselected
      hrun hloops hpart hedge hself hv hsrc hsrcFixed hside hprDecl hsrcFrame

end Elegant.Layered.PipelineImpl

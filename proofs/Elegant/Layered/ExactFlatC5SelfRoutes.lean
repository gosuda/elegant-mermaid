import Elegant.Layered.ExactFlatC5
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactFlatC5ChosenPart
import Elegant.Layered.ExecutedLoopPortsFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Routes of an exact-placed component cover the candidate edge decls. -/
private theorem X_placeComponentExact_routes_decls (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run cursor labels loops).routes.map (·.1) =
      cg.edges.map (·.decl) := by
  unfold placeComponentExact
  dsimp only
  rw [List.map_map]
  exact zipIdx_map_comp (·.decl) cg.edges 0

/-- Exact-placed routes keep declaration uniqueness. -/
private theorem X_placeComponentExact_routes_decls_nodup (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (hnd : (cg.edges.map (·.decl)).Nodup) :
    ((placeComponentExact P cg run cursor labels loops).routes.map (·.1)).Nodup := by
  rw [X_placeComponentExact_routes_decls]
  exact hnd

/-- Exact frame entry (copy of `chosen_part_frame_entry` over `placeComponentExact`). -/
private theorem X_chosen_part_frame_entry
    {P : Params} {graph : Graph} {component : List Nat} {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {part : Part} {area : Int}
    (hpart : part = { placeComponentExact P (componentCandidate graph component candidate)
      run 0 labels loops with area := area })
    {localIndex key : Nat} (hkey : component[localIndex]? = some key) :
    (component.zip part.rects)[localIndex]? =
      some (key, shiftRect
        (0 - (placeBoundsX P (componentCandidate graph component candidate) run labels loops).minX)
        (-(placeBoundsX P (componentCandidate graph component candidate) run labels loops).minY)
        (frameRect P (componentCandidate graph component candidate) run localIndex)) := by
  have hlocal : localIndex < (componentCandidate graph component candidate).nodes.length := by
    have hk := (List.getElem?_eq_some_iff.mp hkey).1
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using hk
  have hrect : (placeComponentExact P (componentCandidate graph component candidate)
      run 0 labels loops).rects[localIndex]? =
      some (shiftRect
        (0 - (placeBoundsX P (componentCandidate graph component candidate) run labels loops).minX)
        (-(placeBoundsX P (componentCandidate graph component candidate) run labels loops).minY)
        (frameRect P (componentCandidate graph component candidate) run localIndex)) := by
    unfold placeComponentExact placeBoundsX
    simp only [List.getElem?_map, List.getElem?_range hlocal, Option.map_some]
  apply List.getElem?_zip_eq_some.mpr
  refine ⟨hkey, ?_⟩
  rw [hpart]
  exact hrect

/-- Exact dump lookup from box ids (copy of `SceneExecution.source_box_lookup_of_box_ids_nodup`). -/
theorem SceneExecutionX.source_box_lookup_of_box_ids_nodupX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hboxIds : (inp.boxes.map (·.id)).Nodup)
    {index : Nat} {source : ModelBox}
    (hsource : inp.boxes[index]? = some source) :
    res.scene.layoutDump.box? source.id =
      some (Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD index default)))
        source.parent source.exclusive) := by
  let box := Box.mk source.id source.role.id
    (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD index default)))
    source.parent source.exclusive
  have hbox : res.scene.boxes[index]? = some box := by
    rw [execution.boxes_eq_mapX]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hsource,
      Option.map_some, Nat.zero_add]
    rfl
  have hids : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
    rw [execution.boxes_eq_mapX, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hids]
    exact hboxIds
  change res.scene.boxes.find? (fun candidate => candidate.id == source.id) = some box
  exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hnodup box
    (List.mem_of_getElem? hbox)

/-- Exact part-entry dump lookup (copy of `SceneExecution.part_entry_box_lookup_of_box_ids_nodup`). -/
private theorem SceneExecutionX.part_entry_box_lookup_of_box_ids_nodupX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} {rect : Rect}
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    {source : ModelBox} (hsource : inp.boxes[key]? = some source) :
    res.scene.layoutDump.box? source.id =
      some (Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y rect)))
        source.parent source.exclusive) := by
  have hsize : execution.componentsAcc.rects.size = inp.boxes.length :=
    execution.components_rects_size
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [hsize]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hrect := actual_components_packed_rect_valueX (by rfl) execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hkeysize default
  have hlookup := execution.source_box_lookup_of_box_ids_nodupX hids hsource
  rw [hrect] at hlookup
  exact hlookup
/-- Exact ownership: every exact-placed route decl is owned by its component. -/
private theorem X_actualPart_ownsX {P : Params} {exactIds : List String} {inp : Input} {o : Options}
    {g : Graph} {labels : List MeasuredLabel} {q : List Nat × Part}
    (h : ActualPartX P exactIds inp o g labels q) :
    ∀ d ∈ q.2.routes.map (·.1), ownsDecl g q.1 d := by
  obtain ⟨index, _, run, loops, _, _, _, _, _, hr⟩ := h
  rw [hr, X_placeComponentExact_routes_decls]
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  exact componentCandidate_edge_owns he

/-- Exact route-key noninterference across distinct actual parts. -/
private theorem X_actual_components_route_keys_disjointX {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel}
    {start out : Acc}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok out)
    (hnd : (g.edges.map (·.decl)).Nodup)
    {a b : List Nat × Part} (ha : a ∈ out.parts) (hb : b ∈ out.parts)
    (hne : a.1 ≠ b.1) {d : Nat} (hd : d ∈ a.2.routes.map (·.1)) :
    d ∉ b.2.routes.map (·.1) := by
  obtain ⟨hm, hall⟩ := actual_components_partsX hempty hfold
  have hca : a.1 ∈ components g := by
    rw [← hm]
    exact List.mem_map_of_mem ha
  have hcb : b.1 ∈ components g := by
    rw [← hm]
    exact List.mem_map_of_mem hb
  intro hd'
  exact components_ownsDecl_disjoint hnd hca hcb hne
    (X_actualPart_ownsX (hall a ha) d hd) (X_actualPart_ownsX (hall b hb) d hd')

/-- Exact later-route-key noninterference by indexed membership. -/
private theorem X_actual_components_later_route_key_neX {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel}
    {start out : Acc}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok out)
    (hnd : (g.edges.map (·.decl)).Nodup)
    {i j : Nat} {a b : List Nat × Part}
    (ha : out.parts[i]? = some a) (hb : out.parts[j]? = some b) (hij : i < j)
    {d : Nat} (hd : d ∈ a.2.routes.map (·.1)) :
    d ∉ b.2.routes.map (·.1) := by
  obtain ⟨hm, _⟩ := actual_components_partsX hempty hfold
  have hn : (out.parts.map (·.1)).Nodup := by
    rw [hm]
    exact components_entries_nodup g
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, hbj⟩ := List.getElem?_eq_some_iff.mp hb
  have hne : a.1 ≠ b.1 := by
    have hpair := List.pairwise_iff_getElem.mp hn
    have hnij := hpair i j (by simpa using hi) (by simpa using hj) hij
    simpa [hai, hbj] using hnij
  exact X_actual_components_route_keys_disjointX hempty hfold hnd
    (List.mem_iff_getElem?.mpr ⟨i, ha⟩) (List.mem_iff_getElem?.mpr ⟨j, hb⟩) hne hd

/-- Exact zip-later noninterference for the packed selection. -/
private theorem X_actual_components_zip_later_route_key_neX
    {P : Params} {exactIds : List String} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {start out : Acc} {positions : List Rect}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok out)
    (hnd : (g.edges.map (·.decl)).Nodup)
    {c : Nat} {a : List Nat × Part} {pos : Rect}
    (hsel : (out.parts.zip positions)[c]? = some (a, pos))
    {d : Nat} (hd : d ∈ a.2.routes.map (·.1))
    {q' : (List Nat × Part) × Rect}
    (hq' : q' ∈ (out.parts.zip positions).drop (c + 1)) :
    d ∉ q'.1.2.routes.map (·.1) := by
  obtain ⟨j, hjlt, hjget⟩ :=
    zip_drop_mem_later_getElem? (xs := out.parts) (ys := positions) hq'
  exact X_actual_components_later_route_key_neX hempty hfold hnd
    (zip_getElem?_left hsel) hjget hjlt hd

/-- Exact fold preserves the route array size. -/
private theorem X_components_fold_routes_sizeX (P : Params) (exactIds : List String)
    (inp : Input) (o : Options) (g : Graph) (measured : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentX P exactIds inp o g acc comp measured)
        start = .ok out → out.routes.size = start.routes.size
  | [], start, out, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
  | comp :: rest, start, out, h => by
    simp only [List.foldlM_cons] at h
    cases hc : layoutComponentX P exactIds inp o g start comp measured with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      exact (X_components_fold_routes_sizeX P exactIds inp o g measured rest next out h).trans
        (layoutComponentX_sizes hc).2.1.symm

/-- Exact execution keeps the route array length. -/
private theorem SceneExecutionX.components_routes_sizeX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.componentsAcc.routes.size = inp.routes.length := by
  have h := X_components_fold_routes_sizeX execution.params exactIds inp o execution.graph
    execution.measured (components execution.graph) _ _ execution.components_eq
  simpa only [Array.size_replicate] using h

/-- Exact packAcc route projection (copy of `actual_components_packAcc_routes_getD`). -/
private theorem X_actual_components_packAcc_routes_getDX
    {P : Params} {exactIds : List String} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {start mid out : Acc}
    (hempty : start.parts = [])
    (hfold : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok mid)
    (hnd : (g.edges.map (·.decl)).Nodup)
    (packed : Pack.State)
    (hpack : packAcc P o mid = .ok out)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hget_pair : (mid.parts.zip packed.boxes)[c]? = some q)
    (i : Nat) (k : Nat) (pts : List Point) (d : List Point)
    (hget_route : q.1.2.routes[i]? = some (k, pts))
    (hnodup : (q.1.2.routes.map (·.1)).Nodup)
    (hsize : k < mid.routes.size) :
    out.routes.getD k d = pts.map (shiftPoint q.2.x q.2.y) := by
  have hsel : (mid.parts.zip packed.boxes)[c]? = some (q.1, q.2) := hget_pair
  have hmem : k ∈ q.1.2.routes.map (·.1) := by
    have hp : (k, pts) ∈ q.1.2.routes := List.mem_iff_getElem?.mpr ⟨i, hget_route⟩
    exact List.mem_map_of_mem hp
  refine packAcc_routes_getD hpack packed hpacked c q hget_pair i k pts d hget_route hnodup hsize ?_
  intro q' hq'
  exact X_actual_components_zip_later_route_key_neX hempty hfold hnd hsel hmem hq'
/-- Scene ids mirror input ids for exact executions. -/
private theorem X_self_scene_ids_eq {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
  rw [execution.boxes_eq_mapX, List.map_map]
  exact zipIdx_map_comp (·.id) inp.boxes 0

/-- First-occurrence transfer across id-preserving maps. -/
private theorem X_self_findIdx_congr {α β : Type} {f : α → String} {g : β → String}
    {l1 : List α} {l2 : List β} (hmap : l1.map f = l2.map g)
    {target : String} {idx : Nat}
    (hidx : l2.findIdx? (fun b => g b == target) = some idx) :
    l1.findIdx? (fun a => f a == target) = some idx := by
  have hlen : l1.length = l2.length := by
    have h1 := congrArg List.length hmap
    simpa using h1
  obtain ⟨hilt, htrue, hearly⟩ :=
    (List.findIdx?_eq_some_iff_getElem).mp hidx
  have hilt' : idx < l1.length := by omega
  apply (List.findIdx?_eq_some_iff_getElem).mpr
  refine ⟨hilt', ?_, ?_⟩
  · have hmap_idx : (l1.map f)[idx]? = (l2.map g)[idx]? := by rw [hmap]
    rw [List.getElem?_map, List.getElem?_map] at hmap_idx
    have e2 : l2[idx]? = some (l2[idx]'hilt) := List.getElem?_eq_getElem hilt
    have e1 : l1[idx]? = some (l1[idx]'hilt') := List.getElem?_eq_getElem hilt'
    rw [e2, e1] at hmap_idx
    simp only [Option.map_some, Option.some.injEq] at hmap_idx
    show ((fun a => f a == target) (l1[idx]'hilt') = true)
    have htrue' : ((fun b => g b == target) (l2[idx]'hilt) = true) := htrue
    simp only at htrue'
    rw [← hmap_idx] at htrue'
    simpa using htrue'
  · intro j hj
    have hj2 : j < l2.length := by omega
    have hearly2 := hearly j hj
    have hj1 : j < l1.length := by omega
    have hmap_j : (l1.map f)[j]? = (l2.map g)[j]? := by rw [hmap]
    rw [List.getElem?_map, List.getElem?_map] at hmap_j
    have e2 : l2[j]? = some (l2[j]'hj2) := List.getElem?_eq_getElem hj2
    have e1 : l1[j]? = some (l1[j]'hj1) := List.getElem?_eq_getElem hj1
    rw [e2, e1] at hmap_j
    simp only [Option.map_some, Option.some.injEq] at hmap_j
    intro hcon
    apply hearly2
    rw [hmap_j] at hcon
    exact hcon


/-- Exact-run index list equation. -/
private theorem X_self_run_exact_eq {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    run.exact = cg.nodes.zipIdx.filterMap
      (fun q : Node × Nat => if exact.contains q.1.decl then some q.2 else none) := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, _, h⟩ := bind_ok h
  obtain ⟨p, _, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨lanes, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨shifted, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  rw [← he]

/-- Exact membership forward: an exact decl puts its position in `run.exact`. -/
private theorem X_self_run_exact_mem_of_contains {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hv : v < cg.nodes.length)
    (hmem : exact.contains ((cg.nodes[v]'hv).decl) = true) :
    v ∈ run.exact := by
  have heq := X_self_run_exact_eq h
  rw [heq]
  have hzipmem : ((cg.nodes[v]'hv), v) ∈ cg.nodes.zipIdx := by
    simpa using List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hv)
  apply List.mem_filterMap.mpr
  refine ⟨((cg.nodes[v]'hv), v), hzipmem, ?_⟩
  simp only [hmem, ↓reduceIte]




/-- Scene first-occurrence mirrors input first-occurrence. -/
private theorem X_self_scene_findIdx_eq {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {id : String} {idx : Nat}
    (hidx : inp.boxes.findIdx? (fun b => b.id == id) = some idx) :
    res.scene.boxes.findIdx? (fun b => b.id == id) = some idx :=
  X_self_findIdx_congr (X_self_scene_ids_eq execution) hidx

/-- Nodup-free exact dump lookup at a first occurrence. -/
private theorem SceneExecutionX.source_box_lookup_firstX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {idx : Nat} {source : ModelBox}
    (hfirst : inp.boxes.findIdx? (fun b => b.id == source.id) = some idx)
    (hsource : inp.boxes[idx]? = some source) :
    res.scene.layoutDump.box? source.id =
      some (Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD idx default)))
        source.parent source.exclusive) := by
  have hSceneIdx := X_self_scene_findIdx_eq execution hfirst
  have hSceneGet : res.scene.boxes[idx]? =
      some (Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD idx default)))
        source.parent source.exclusive) := by
    rw [execution.boxes_eq_mapX]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hsource,
      Option.map_some, Nat.zero_add]
  have hFind : res.scene.boxes.find? (fun b => b.id == source.id) =
      res.scene.boxes[idx]? := by
    rw [List.find?_eq_bind_findIdx?_getElem?, hSceneIdx]
    simp only [Option.bind_some]
  rw [hSceneGet] at hFind
  show res.scene.layoutDump.box? source.id = _
  simp only [Scene.layoutDump]
  exact hFind




/-- Exact original plain nodes keep their measured widths as lower bounds
(copy of the private `X_original_plain_record` of `ExactFlatC2.lean`). -/
private theorem X_self_original_plain_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.node.border = 0 ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ := componentRunX_spec h
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, _, hborder, hwidth, hheight⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hprojected := proxyWidths_plain_node hproxy hcoordinate hborder
  have hproper : run.proper.nodes[index]? = some actual := by
    rw [← hdrop]
    exact hprojected
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy2, _, _, _, _⟩ := componentRunX_spec h
  have hx := ((proxyWidths_rel hproxy2).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Exact emitted self edge (copy of `componentLoops_emitted_self_edge` over
`placeComponentExact`/`placeBoundsX`). -/
private theorem X_componentLoops_emitted_self_edgeX
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops P cg run labels = .ok loops)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hv : edge.tail < cg.nodes.length) (hself : edge.tail = edge.head)
    (cursor : Int) :
    ∃ q ∈ loops,
      loops.find? (fun loop => loop.1 == edge.decl) = some q ∧ q.1 = edge.decl ∧
      (placeComponentExact P cg run cursor labels loops).routes[i]? =
        some (edge.decl, q.2.points.map
          (shiftPoint (cursor - (placeBoundsX P cg run labels loops).minX)
            (-(placeBoundsX P cg run labels loops).minY))) := by
  obtain ⟨placement, hplacement⟩ := componentLoops_entry_of_self_edge hloops
    (List.mem_of_getElem? hedge) hv hself
  cases hfind : loops.find? (fun loop => loop.1 == edge.decl) with
  | none =>
    have hn := List.find?_eq_none.mp hfind (edge.decl, placement) hplacement
    simp only [beq_self_eq_true, not_true_eq_false] at hn
  | some q =>
    have hq := List.mem_of_find?_eq_some hfind
    have hdecl : q.1 = edge.decl := by
      simpa only [beq_iff_eq] using List.find?_some hfind
    refine ⟨q, hq, rfl, hdecl, ?_⟩
    unfold placeComponentExact placeBoundsX
    dsimp only
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some,
      hfind, Option.getD_some]

/-- Exact-index absence: if the run does not reserve `v`, the exact list
does not contain the node's declaration. Contrapositive of
`X_self_run_exact_mem_of_contains`. -/
private theorem X_self_run_exact_not_mem_of_not_contains {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hv : v < cg.nodes.length)
    (hnot : run.exact.contains v = false) :
    exact.contains ((cg.nodes[v]'hv).decl) = false := by
  cases he : exact.contains ((cg.nodes[v]'hv).decl) with
  | true =>
    have hmem := X_self_run_exact_mem_of_contains h hv he
    have hcon2 : run.exact.contains v = true := by
      rw [List.contains_eq_mem]
      simp [hmem]
    rw [hcon2] at hnot
    contradiction
  | false => rfl

/-- Index lookup on a member (copy of `X_comp_idxOf_lookup`). -/
private theorem X_self_comp_idxOf_lookup {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))

/-- On a duplicate-free component, `idxOf` is injective (copy of
`comp_idxOf_injective`). -/
private theorem X_self_idxOf_injective {comp : List Nat}
    {x y : Nat} (hx : x ∈ comp) (hy : y ∈ comp)
    (h : comp.idxOf x = comp.idxOf y) : x = y := by
  have e0 : comp[comp.idxOf x]? = comp[comp.idxOf y]? := by rw [h]
  have eL : comp[comp.idxOf x]? = some x := X_self_comp_idxOf_lookup hx
  have eR : comp[comp.idxOf y]? = some y := X_self_comp_idxOf_lookup hy
  exact Option.some.inj (eL.symm.trans (e0.trans eR))

/-- Endpoint case split on prepared boxes (copy of `endpoint_cases_local`). -/
private theorem X_self_endpoint_cases {boxes : List ModelBox} (s : Bool) (i j : Nat) :
    Compound.endpoint boxes s i j = i ∨
      (Compound.endpoint boxes s i j = Compound.bottomIndex boxes i ∧
        ∀ box, boxes[i]? = some box → box.role = .group) := by
  unfold Compound.endpoint
  cases hbi : boxes[i]? with
  | none => exact Or.inl rfl
  | some box =>
    cases hbj : boxes[j]? with
    | none => exact Or.inl rfl
    | some target =>
      dsimp only
      by_cases hc : (box.role != .group || i == j) = true
      · rw [ite_eq_left hc]
        exact Or.inl rfl
      · rw [ite_eq_right hc]
        by_cases hd : (s == Compound.inside boxes box.id target.id) = true
        · rw [ite_eq_left hd]
          exact Or.inl rfl
        · rw [ite_eq_right hd]
          refine Or.inr ⟨rfl, ?_⟩
          intro box' hb'
          have heq : box' = box := (Option.some.inj hb').symm
          rw [heq]
          cases hbr : box.role
          · exfalso
            have h1 : (box.role != .group || i == j) = true := by
              rw [hbr]
              cases hij : (i == j) <;> rfl
            exact hc h1
          · rfl

/-- `bottomIndex` is strictly increasing past a group box (copy of
`flat_bottomIndex_lt`). -/
private theorem X_self_bottomIndex_lt {boxes : List ModelBox} {i j : Nat}
    (hij : i < j) (hi : i < boxes.length)
    (hg : (boxes[i]'hi).role == .group) :
    Compound.bottomIndex boxes i < Compound.bottomIndex boxes j := by
  have h1 : (boxes.take j).take i ++ (boxes.take j).drop i = boxes.take j :=
    List.take_append_drop i (boxes.take j)
  have h2 : (boxes.take j).take i = boxes.take i := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  have h3 := congrArg (List.filter (fun box : ModelBox => box.role == .group)) h1
  rw [List.filter_append, h2] at h3
  have hmem : boxes[i]'hi ∈ (boxes.take j).drop i := by
    have h0 : ((boxes.take j).drop i)[0]? = some (boxes[i]'hi) := by
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_take, ite_eq_left hij,
        List.getElem?_eq_getElem hi]
    exact List.mem_of_getElem? h0
  have hfilter : 0 < (((boxes.take j).drop i).filter
      (fun box : ModelBox => box.role == .group)).length := by
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hmem, hg⟩
  have h4 := congrArg (fun l => l.length) h3
  rw [List.length_append] at h4
  unfold Compound.bottomIndex
  omega

/-- Two group-box indices with the same `bottomIndex` coincide (copy of
`flat_bottomIndex_injective`). -/
private theorem X_self_bottomIndex_injective {boxes : List ModelBox} {i j : Nat}
    {bi bj : ModelBox} (hbi : boxes[i]? = some bi) (hbj : boxes[j]? = some bj)
    (hgi : bi.role == .group) (hgj : bj.role == .group)
    (h : Compound.bottomIndex boxes i = Compound.bottomIndex boxes j) : i = j := by
  obtain ⟨hi, hie⟩ := List.getElem_of_getElem? hbi
  obtain ⟨hj, hje⟩ := List.getElem_of_getElem? hbj
  rw [← hie] at hgi
  rw [← hje] at hgj
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (X_self_bottomIndex_lt hlt hi hgi))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (X_self_bottomIndex_lt hgt hj hgj))
/-- A proper self edge of the exact candidate graph carries a model route
whose two endpoint ids coincide (exact replay of `flat_self_route_ids`: the
semantic source transfers through `exactGraph_edges`, bounds through
`sceneExecutionX_edges_bounded`). -/
private theorem X_self_route_ids {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat}
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head) :
    ∃ route : ModelRoute, inp.routes[edge.decl]? = some route ∧
      route.fromId = route.toId ∧
      ∃ src : ModelBox, src ∈ inp.boxes ∧ src.id = route.fromId := by
  have hedges : edge ∈ (componentCandidate execution.graph comp candidate).edges :=
    List.mem_of_getElem? hedge
  obtain ⟨index, route, raw, source, target, hroute, hrawOf, hdeclIdx,
    hrawsource, hsourceId, hrawtarget, htargetId, _⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq hedges
  obtain ⟨gEdge, hgEdge, hgTailMem, hsemG⟩ :=
    componentCandidate_semantic_source hedges
  have hgEdge0 : gEdge ∈ execution.graph0.edges := by
    rw [exactGraph_edges execution.graph_eq] at hgEdge
    exact hgEdge
  obtain ⟨index2, route2, raw2, hr2Route, hr2EdgeOf, hgeAlias⟩ :=
    measuredGraph_edge_source execution.graph0_eq hgEdge0
  obtain ⟨h2Decl, h2Rev, _, _, _, _⟩ := edgeOf_semantic_endpoints hr2EdgeOf
  have hgeRev : gEdge.reversed = false := by rw [hgeAlias]; exact h2Rev
  have hgeOrig : gEdge.original = gEdge := by
    cases gEdge with
    | mk _ _ _ _ rev => cases hgeRev; rfl
  have hgeDeclIdx : edge.decl = index2 := by
    have h1 : edge.decl = gEdge.decl := by
      have h := congrArg Edge.decl hsemG
      simpa only [Edge.original_decl] using h
    rw [h1, hgeAlias, Compound.aliasEdge_decl, h2Decl]
  have hidx2 : index2 = index := hgeDeclIdx.symm.trans hdeclIdx
  rw [hidx2] at hr2Route
  have hroute2Eq : route2 = route :=
    Option.some.inj (hr2Route.symm.trans hroute)
  rw [hidx2, hroute2Eq] at hr2EdgeOf
  have hrawEq : raw2 = raw := Except.ok.inj (hr2EdgeOf.symm.trans hrawOf)
  rw [hrawEq] at hgeAlias
  have hbd : ∀ e ∈ execution.graph.edges ++ Compound.constraints execution.graph,
      e.tail < execution.graph.nodes.length ∧ e.head < execution.graph.nodes.length :=
    sceneExecutionX_edges_bounded execution
  obtain ⟨comp', hcomp'In, hgTailC, hgHeadC⟩ :=
    components_edge_endpoints hbd (List.mem_append.mpr (Or.inl hgEdge))
  have hcompEq : comp' = comp :=
    components_shared_member_eq hcomp'In hcomp hgTailC hgTailMem
  have hgHeadMem : gEdge.head ∈ comp := by rw [← hcompEq]; exact hgHeadC
  have hgTailMem' : (aliasEdgeOf inp raw).tail ∈ comp := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgTailMem
  have hgHeadMem' : (aliasEdgeOf inp raw).head ∈ comp := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgHeadMem
  have hsemTail : edge.original.tail = comp.idxOf (aliasEdgeOf inp raw).tail := by
    have h := congrArg Edge.tail hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  have hsemHead : edge.original.head = comp.idxOf (aliasEdgeOf inp raw).head := by
    have h := congrArg Edge.head hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  have horig : edge.original.tail = edge.original.head := by
    cases hr : edge.reversed with
    | true => simp [Edge.original, hr, hself]
    | false => simp [Edge.original, hr, hself]
  have haliased : (aliasEdgeOf inp raw).tail = (aliasEdgeOf inp raw).head :=
    X_self_idxOf_injective hgTailMem' hgHeadMem'
      (by rw [← hsemTail, ← hsemHead, horig])
  have hT : (aliasEdgeOf inp raw).tail =
      Compound.endpoint (preparedBoxes inp) true raw.tail raw.head := rfl
  have hH : (aliasEdgeOf inp raw).head =
      Compound.endpoint (preparedBoxes inp) false raw.head raw.tail := rfl
  rcases X_self_endpoint_cases (boxes := preparedBoxes inp) true raw.tail raw.head
    with hflatT | ⟨hbotT, hgrpT⟩
  · rcases X_self_endpoint_cases (boxes := preparedBoxes inp) false raw.head raw.tail
      with hflatH | ⟨hbotH, hgrpH⟩
    · rw [hT, hflatT, hH, hflatH] at haliased
      refine ⟨route, by rw [hdeclIdx]; exact hroute, ?_, ?_⟩
      have hst : source = target := by
        rw [haliased] at hrawsource
        exact Option.some.inj (hrawsource.symm.trans hrawtarget)
      · exact hsourceId.symm.trans (by rw [hst]; exact htargetId)
      · exact ⟨source, List.mem_of_getElem? hrawsource, hsourceId⟩
    · rw [hT, hflatT, hH, hbotH] at haliased
      have hlt : raw.tail < (preparedBoxes inp).length := by
        simpa [preparedBoxes, List.length_map] using
          (List.getElem?_eq_some_iff.mp hrawsource).1
      have hge : (preparedBoxes inp).length ≤ Compound.bottomIndex
          (preparedBoxes inp) raw.head := by
        unfold Compound.bottomIndex; omega
      omega
  · rcases X_self_endpoint_cases (boxes := preparedBoxes inp) false raw.head raw.tail
      with hflatH | ⟨hbotH, hgrpH⟩
    · rw [hT, hbotT, hH, hflatH] at haliased
      have hlt : raw.head < (preparedBoxes inp).length := by
        simpa [preparedBoxes, List.length_map] using
          (List.getElem?_eq_some_iff.mp hrawtarget).1
      have hge : (preparedBoxes inp).length ≤ Compound.bottomIndex
          (preparedBoxes inp) raw.tail := by
        unfold Compound.bottomIndex; omega
      omega
    · rw [hT, hbotT, hH, hbotH] at haliased
      have hsame : raw.tail = raw.head :=
        X_self_bottomIndex_injective (preparedBoxes_lookup hrawsource)
          (preparedBoxes_lookup hrawtarget)
          (by simp [hgrpT _ (preparedBoxes_lookup hrawsource)])
          (by simp [hgrpH _ (preparedBoxes_lookup hrawtarget)]) haliased
      refine ⟨route, by rw [hdeclIdx]; exact hroute, ?_, ?_⟩
      have hst : source = target := by
        rw [hsame] at hrawsource
        exact Option.some.inj (hrawsource.symm.trans hrawtarget)
      · exact hsourceId.symm.trans (by rw [hst]; exact htargetId)
      · exact ⟨source, List.mem_of_getElem? hrawsource, hsourceId⟩

/-- `idxOf` inverts lookup on a duplicate-free component (copy of
`component_idxOf_eq_iff`). -/
private theorem X_self_component_idxOf_eq_iff {component : List Nat}
    (hn : component.Nodup) (v : Nat) (hv : v < component.length) (source : Nat) :
    component.idxOf source = v ↔ source = component[v] := by
  constructor
  · intro he
    have hb : component.idxOf source < component.length := by omega
    have hget := List.getElem_idxOf hb
    simpa only [he] using hget.symm
  · intro he
    subst source
    exact hn.idxOf_getElem v hv

/-- Candidate loop edges renumber global loop edges (copy of
`componentGraph_loopEdges_preserved`). -/
private theorem X_self_componentGraph_loopEdges_preserved (g : Graph) (component : List Nat)
    (hn : component.Nodup) (v : Nat) (hv : v < component.length) :
    loopEdges (componentGraph g component).edges v =
      (loopEdges g.edges component[v]).map fun edge =>
        { edge with tail := v, head := v } := by
  let renumber := fun edge : Edge =>
    { edge with tail := component.idxOf edge.tail, head := component.idxOf edge.head }
  have hlist : ∀ edges : List Edge,
      loopEdges ((edges.filter fun edge => component.contains edge.tail).map renumber) v =
      (loopEdges edges component[v]).map (fun edge => { edge with tail := v, head := v }) := by
    intro edges
    induction edges with
    | nil => rfl
    | cons edge edges ih =>
      have hiff :
          ((renumber edge).tail == v && (renumber edge).head == v) = true ↔
          (edge.tail == component[v] && edge.head == component[v]) = true := by
        simp only [renumber, Bool.and_eq_true, beq_iff_eq,
          X_self_component_idxOf_eq_iff hn v hv]
      by_cases he : (edge.tail == component[v] && edge.head == component[v]) = true
      · have hend : edge.tail = component[v] ∧ edge.head = component[v] := by
          simpa only [Bool.and_eq_true, beq_iff_eq] using he
        have hcontains : component.contains edge.tail = true := by
          rw [List.contains_eq_mem, hend.1]
          exact decide_eq_true (List.getElem_mem hv)
        have hrenumber : renumber edge = { edge with tail := v, head := v } := by
          simp only [renumber, hend.1, hend.2, hn.idxOf_getElem v hv]
        simp only [List.filter_cons, hcontains, ↓reduceIte, List.map_cons, loopEdges,
          he, hrenumber] at ih ⊢
        simpa using congrArg (List.cons { edge with tail := v, head := v }) ih
      · have hlocal : ((renumber edge).tail == v && (renumber edge).head == v) = false :=
          Bool.eq_false_iff.mpr (fun h => he (hiff.mp h))
        have he' : (edge.tail == component[v] && edge.head == component[v]) = false :=
          Bool.eq_false_iff.mpr he
        cases hc : component.contains edge.tail <;>
          simpa only [List.filter_cons, hc, Bool.false_eq_true, ↓reduceIte, List.map_cons,
            loopEdges, hlocal, he'] using ih
  exact hlist g.edges

/-- Candidate loop sizes agree with global loop sizes (copy of
`componentGraph_loopSizes_preserved`). -/
private theorem X_self_componentGraph_loopSizes_preserved (g : Graph) (component : List Nat)
    (hn : component.Nodup) (v : Nat) (hv : v < component.length)
    (labels : List MeasuredLabel) (slot : Int) :
    loopSizes (componentGraph g component).edges labels v slot =
      loopSizes g.edges labels component[v] slot := by
  unfold loopSizes
  rw [X_self_componentGraph_loopEdges_preserved g component hn v hv, List.map_map]
  rfl

/-- Loop sizes see through `original` (copy of `loopSizes_original`). -/
private theorem X_self_loopSizes_original (edges : List Edge) (labels : List MeasuredLabel)
    (v : Nat) (slot : Int) :
    loopSizes (edges.map Edge.original) labels v slot = loopSizes edges labels v slot := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
    by_cases ht : edge.tail = v <;> by_cases hh : edge.head = v <;>
      cases hr : edge.reversed <;>
      simp [loopSizes, loopEdges, Edge.original, hr, ht, hh] at ih ⊢ <;>
      exact ih

/-- Loop sizes agree when `original`s agree (copy of `loopSizes_of_originals`). -/
private theorem X_self_loopSizes_of_originals {left right : List Edge}
    (h : left.map Edge.original = right.map Edge.original)
    (labels : List MeasuredLabel) (v : Nat) (slot : Int) :
    loopSizes left labels v slot = loopSizes right labels v slot := by
  rw [← X_self_loopSizes_original left labels v slot, h,
    X_self_loopSizes_original right labels v slot]

/-- Loop sizes see through `cycleGraph` (copy of `loopSizes_cycleGraph`). -/
private theorem X_self_loopSizes_cycleGraph (g : Graph) (labels : List MeasuredLabel)
    (v : Nat) (slot : Int) :
    loopSizes (cycleGraph g).edges labels v slot = loopSizes g.edges labels v slot := by
  unfold cycleGraph
  split
  · exact X_self_loopSizes_of_originals
      (ProtectedCycles.semantic_identity g (Compound.constraints g)) labels v slot
  · apply X_self_loopSizes_of_originals ?_ labels v slot
    rw [breakCycles_edges_eq, List.map_map]
    apply List.map_congr_left
    intro edge _
    change (g.orient edge).original = edge.original
    unfold Graph.orient
    split
    · exact Edge.reverse_original edge
    · rfl

/-- Candidate loop sizes agree with global loop sizes (copy of
`componentCandidate_loopSizes_preserved`). -/
private theorem X_self_componentCandidate_loopSizes_preserved (g : Graph) (component : List Nat)
    (hn : component.Nodup) (candidate v : Nat) (hv : v < component.length)
    (labels : List MeasuredLabel) (slot : Int) :
    loopSizes (componentCandidate g component candidate).edges labels v slot =
      loopSizes g.edges labels component[v] slot := by
  rw [← X_self_componentGraph_loopSizes_preserved g component hn v hv labels slot]
  unfold componentCandidate
  dsimp only
  split
  · split
    · apply Eq.trans (X_self_loopSizes_of_originals
        (ProtectedCycles.semantic_identity _ _) labels v slot)
      exact (X_self_loopSizes_of_originals (breakCyclesGreedy_semantic_identity _) labels v slot).trans
        (X_self_loopSizes_original _ labels v slot)
    · exact (X_self_loopSizes_of_originals (breakCyclesGreedy_semantic_identity _) labels v slot).trans
        (X_self_loopSizes_original _ labels v slot)
  · exact (X_self_loopSizes_cycleGraph _ labels v slot).trans
      (X_self_loopSizes_original _ labels v slot)

/-- Candidate slots agree with global slots (copy of `componentCandidate_slot`). -/
private theorem X_self_componentCandidate_slot (g : Graph) (component : List Nat)
    (candidate : Nat) :
    (componentCandidate g component candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl
/-- Exact executions cover every input box with a measured line. -/
private theorem X_self_lines_len {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have hle := execution.lines_eq
  unfold boxLines at hle
  have hlen := (mapM_getElem? _ _ _ hle).1
  simpa only [List.length_zipIdx] using hlen

/-- Membership characterization of `exactDecls`: a global index is exact
exactly when its box is listed or is a fixed group. -/
private theorem X_self_exactDecls_contains {exactIds : List String} {inp : Input}
    {d : Nat} {box : ModelBox} (hb : inp.boxes[d]? = some box) :
    (exactDecls exactIds inp).contains d =
      (exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) := by
  have hchar : (d ∈ exactDecls exactIds inp) ↔
      (exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = true := by
    constructor
    · intro hm
      unfold exactDecls at hm
      obtain ⟨q, hq, hqq⟩ := List.mem_filterMap.mp hm
      have hpred : (exactIds.contains q.1.id || (q.1.role == .group && inp.fixedSizes.any (·.1 == q.1.id))) = true := by
        cases h : (exactIds.contains q.1.id || (q.1.role == .group && inp.fixedSizes.any (·.1 == q.1.id))) with
        | true => rfl
        | false => simp only [h] at hqq; simp at hqq
      have hqd : q.2 = d := by
        simp only [hpred, ↓reduceIte] at hqq
        exact Option.some.inj hqq
      obtain ⟨a, n⟩ := q
      have hmem : inp.boxes[n]? = some a := List.mem_zipIdx_iff_getElem?.mp hq
      have hnd : n = d := hqd
      subst hnd
      have ha : a = box := Option.some.inj (hmem.symm.trans hb)
      subst ha
      exact hpred
    · intro hR
      unfold exactDecls
      apply List.mem_filterMap.mpr
      refine ⟨(box, d), List.mem_zipIdx_iff_getElem?.mpr hb, ?_⟩
      show (if exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id)) then some d else none) = some d
      simp only [hR, ↓reduceIte]
  rw [List.contains_eq_mem]
  cases hR : (exactIds.contains box.id || (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) with
  | true =>
    have hm := hchar.mpr hR
    exact decide_eq_true hm
  | false =>
    have hm : d ∉ exactDecls exactIds inp := by
      intro h
      have ht := hchar.mp h
      rw [ht] at hR
      exact Bool.noConfusion hR
    exact decide_eq_false hm

/-- A non-exact global node survives `exactGraph` unchanged. -/
private theorem X_self_nonexact_node_eq {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {component : List Nat} {candidate v : Nat} {nk node : Node}
    (hv : v < component.length)
    (hk0 : execution.graph0.nodes[component[v]]? = some nk)
    (hnode : (componentCandidate execution.graph component candidate).nodes[v]? = some node)
    (hnexact : (exactDecls exactIds inp).contains node.decl = false) :
    node = nk := by
  have hklt : component[v] < execution.graph.nodes.length := by
    have h1 := (List.getElem?_eq_some_iff.mp hk0).1
    rw [exactGraph_length execution.graph_eq]
    exact h1
  obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key execution.graph_eq hk0
  have hnode_nd : node = nd' := by
    have hlocal : (component.map fun source => execution.graph.nodes.getD source default)[v]? = some node := by
      have h1 : (componentCandidate execution.graph component candidate).nodes =
          (componentGraph execution.graph component).nodes :=
        componentCandidate_nodes _ _ _
      rw [h1] at hnode
      have h2 : (componentGraph execution.graph component).nodes =
          component.map fun source => execution.graph.nodes.getD source default := rfl
      rw [h2] at hnode
      exact hnode
    simp only [List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some,
      Option.some.injEq] at hlocal
    have hgetD : execution.graph.nodes.getD component[v] default = nd' := by
      simp only [List.getD_eq_getElem?_getD, hnd', Option.getD_some]
    rw [hgetD] at hlocal
    exact hlocal.symm
  have hnexact_nd : (exactDecls exactIds inp).contains nd'.decl = false := by
    have hde : nd'.decl = node.decl := by rw [hnode_nd]
    rw [hde]; exact hnexact
  obtain ⟨nodes, hnodes, h⟩ := bind_ok execution.graph_eq
  obtain ⟨b, hfb, hmem⟩ := (mapM_getElem? _ _ _ hnodes).2 component[v] nk hk0
  have he : execution.graph = { execution.graph0 with nodes := nodes } := (Except.ok.inj h).symm
  have hnd2 : nodes[component[v]]? = some nd' := by rw [he] at hnd'; exact hnd'
  have hbnd : b = nd' := Option.some.inj (hmem.symm.trans hnd2)
  have hbnk : b = nk := by
    cases hbox' : inp.boxes[nk.decl]? with
    | none =>
      simp only [hbox'] at hfb
      exact (Except.ok.inj hfb).symm
    | some box' =>
      have hchar := X_self_exactDecls_contains (exactIds := exactIds) (inp := inp) hbox'
      have hnkd : nk.decl = nd'.decl := hnd.symm
      rw [← hnkd, hchar] at hnexact_nd
      have ha : exactIds.contains box'.id = false := by
        cases h1 : exactIds.contains box'.id with
        | true => rw [h1] at hnexact_nd; exact Bool.noConfusion hnexact_nd
        | false => rfl
      have hb2 : (box'.role == .group && inp.fixedSizes.any (·.1 == box'.id)) = false := by
        cases h1 : (box'.role == .group && inp.fixedSizes.any (·.1 == box'.id)) with
        | true => rw [ha, h1] at hnexact_nd; exact Bool.noConfusion hnexact_nd
        | false => rfl
      have hcond : (!exactIds.contains box'.id && !(box'.role == .group && inp.fixedSizes.any (·.1 == box'.id))) = true := by
        rw [ha, hb2]
        decide
      simp only [hbox', hcond] at hfb
      exact (Except.ok.inj hfb).symm
  rw [hnode_nd, ← hbnd, hbnk]

/-- The exact graph preserves the slot. -/
private theorem X_self_graph_slot_eq {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.graph.slot = execution.graph0.slot := by
  obtain ⟨nodes, hnodes, h⟩ := bind_ok execution.graph_eq
  have he := Except.ok.inj h
  rw [← he]

/-- Exact ordinary reservation: a non-exact node frame covers the loop height
(exact replay of `SceneExecution.ordinary_candidate_frame_loop_reservation`). -/
private theorem X_self_ordinary_reservation {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (component : List Nat) (hn : component.Nodup) (candidate v : Nat) (hv : v < component.length)
    {box : ModelBox} (hb : inp.boxes[component[v]]? = some box) (hrole : box.role = .node)
    {run : Run}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {node : Node}
    (hnode : (componentCandidate execution.graph component candidate).nodes[v]? = some node)
    (hexactFalse : run.exact.contains v = false) :
    Loops.requiredHeight (componentCandidate execution.graph component candidate).slot
      (loopSizes (componentCandidate execution.graph component candidate).edges execution.measured v
        (componentCandidate execution.graph component candidate).slot) ≤
      (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h := by
  have hlines := X_self_lines_len execution
  have hi : component[v] < execution.lines.length := by
    rw [hlines]; exact (List.getElem?_eq_some_iff.mp hb).1
  have hvCg : v < (componentCandidate execution.graph component candidate).nodes.length := by
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using hv
  have hnexact : (exactDecls exactIds inp).contains node.decl = false := by
    have h := X_self_run_exact_not_mem_of_not_contains hrun hvCg hexactFalse
    have hget : (componentCandidate execution.graph component candidate).nodes[v]? =
        some ((componentCandidate execution.graph component candidate).nodes[v]'hvCg) :=
      List.getElem?_eq_getElem hvCg
    have heq : node = (componentCandidate execution.graph component candidate).nodes[v]'hvCg :=
      Option.some.inj (hnode.symm.trans hget)
    rw [heq]; exact h
  have hklen : component[v] < execution.graph0.nodes.length := by
    have hge := measuredGraph_nodes_length_ge execution.graph0_eq hlines
    omega
  have hk0 : execution.graph0.nodes[component[v]]? =
      some (execution.graph0.nodes[component[v]]'hklen) := List.getElem?_eq_getElem hklen
  have hpre := X_self_nonexact_node_eq execution hv hk0 hnode hnexact
  obtain ⟨metric, labels, gnode, hm, hl, hgnode, hheight⟩ :=
    measuredGraph_ordinary_loop_reservation execution.graph0_eq hi hb hrole
  have hemetric : metric = execution.metric := Except.ok.inj (hm.symm.trans execution.metric_eq)
  subst hemetric
  have helabels : labels = execution.measured := Except.ok.inj (hl.symm.trans execution.measured_eq)
  subst helabels
  have hgnode_eq : gnode = node := by
    have e1 := Option.some.inj (hgnode.symm.trans hk0)
    rw [e1]; exact hpre.symm
  have hborder : node.border = 0 := by
    have hb0 := measuredGraph_ordinary_node_border_zero execution.graph0_eq hi hb hrole hk0
    rw [hpre]; exact hb0
  obtain ⟨actual, hcoordinate, hproper, hborderA, hwidth, hheightA, hxs⟩ :=
    X_self_original_plain_record hrun hnode hborder
  have hgetD : (componentCandidate execution.graph component candidate).nodes.getD v default = node := by
    simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hplain : ((componentCandidate execution.graph component candidate).nodes.getD v default).border ≠ -2 := by
    rw [hgetD, hborder]; decide
  have hframe := frameRect_plain_dims execution.params _ _ v actual hplain hproper
  have hslot := X_self_graph_slot_eq execution
  have hloop : Loops.requiredHeight (componentCandidate execution.graph component candidate).slot
      (loopSizes (componentCandidate execution.graph component candidate).edges execution.measured v
        (componentCandidate execution.graph component candidate).slot) =
      Loops.requiredHeight execution.graph0.slot
        (loopSizes execution.graph0.edges execution.measured component[v] execution.graph0.slot) := by
    rw [X_self_componentCandidate_slot execution.graph component candidate,
      X_self_componentCandidate_loopSizes_preserved execution.graph component hn candidate v hv
        execution.measured _,
      exactGraph_edges execution.graph_eq, hslot]
  have hframeH : (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h = node.h := by
    rw [hframe.2, hheightA]
  rw [hloop, hframeH]
  rw [hgnode_eq] at hheight
  exact hheight


/-- The border-`3` title reservation produced by `coordinateGraphX` for a
non-dummy border-`-2` node (exact replay of `coordinateGraph_title_copy`). -/
private theorem X_self_coordinateGraph_title_copy {P : Params} {exact : List Nat} {p : Proper}
    {i : Nat} {nd : ProperNode}
    (hi : p.nodes[i]? = some nd) (hb : nd.node.border = -2) (hd : nd.dummy = false) :
    ∃ (j : Nat) (res : ProperNode), (coordinateGraphX P exact p).nodes[p.nodes.length + j]? = some res ∧
      res.node.border = 3 ∧ res.node.h = nd.node.h ∧
      res.node.clusterPath = nd.node.clusterPath ∧ res.dummy = false := by
  classical
  have hsized : (sizeProperPortsX P exact p).nodes[i]? = some nd := by
    have hnodes : (sizeProperPortsX P exact p).nodes = p.nodes.zipIdx.map fun q =>
      if q.1.dummy || q.1.node.border != 0 || exact.contains q.1.node.decl then q.1
      else
        let incoming := ((p.edges.filter fun edge => edge.head == q.2).map (·.tail)).eraseDups.length
        let outgoing := ((p.edges.filter fun edge => edge.tail == q.2).map (·.head)).eraseDups.length
        { q.1 with node := { q.1.node with
          w := max q.1.node.w ((((max incoming outgoing : Nat) + 1 : Nat) : Int) * P.portGap) } } := rfl
    rw [hnodes]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hi, Option.map_some]
    have hb0 : (nd.node.border != 0) = true := by rw [hb]; decide
    simp [hb0]
  have hmem : (nd, i) ∈ titleNodes (sizeProperPortsX P exact p) := by
    unfold titleNodes
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · exact List.mem_zipIdx_iff_getElem?.mpr hsized
    · simp [hb]
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  have hjlt : j < (titleNodes (sizeProperPortsX P exact p)).length :=
    (List.getElem?_eq_some_iff.mp hj).1
  have hv_lt : p.nodes.length + j <
      (titleReservations (sizeProperPortsX P exact p)).nodes.length := by
    rw [titleReservations_nodes]
    simp only [List.length_append, List.length_map, sizeProperPortsX_length]
    omega
  have htr : (titleReservations (sizeProperPortsX P exact p)).nodes[p.nodes.length + j]? =
      some (copyF (nd, i)) := by
    rw [titleReservations_nodes]
    rw [List.getElem?_append_right (by
      simp only [List.length_map, sizeProperPortsX_length]
      omega : ((sizeProperPortsX P exact p).nodes.map titleF).length ≤ p.nodes.length + j)]
    have hsub : p.nodes.length + j - ((sizeProperPortsX P exact p).nodes.map titleF).length = j := by
      simp only [List.length_map, sizeProperPortsX_length]
      omega
    rw [hsub, List.getElem?_map, hj]
    rfl
  obtain ⟨extra, hcb_nodes, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hcb : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[p.nodes.length + j]? =
      some (copyF (nd, i)) := by
    rw [hcb_nodes, List.getElem?_append_left hv_lt]
    exact htr
  have hcf : clearF (copyF (nd, i)) = copyF (nd, i) := by
    simp [clearF, copyF]
  have hce : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[p.nodes.length + j]? =
      some (copyF (nd, i)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hcb]
    simp only [Option.map_some, Option.some.injEq]
    exact hcf
  obtain ⟨out, hout, -⟩ := materialize_exists _ hce
  obtain ⟨m, hm, -, -, -, hmeq⟩ := materialize_lookup _ hout
  have hmres : m = copyF (nd, i) := Option.some.inj (hm.symm.trans hce)
  subst m
  have hout_eq : out = copyF (nd, i) := hmeq hd
  subst out
  exact ⟨j, copyF (nd, i), hout, rfl, rfl, rfl, hd⟩

/-- A successful `componentRunX` on a border-`-2` node produces a border-`3`
reservation node preserving height and cluster path (exact replay of
`componentRun_group_reservation`). -/
private theorem X_self_componentRunX_group_reservation {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node) (hb : node.border = -2) :
    ∃ (v : Nat) (res : ProperNode), run.proper.nodes[v]? = some res ∧
      res.node.border = 3 ∧ res.node.h = node.h ∧
      res.node.clusterPath = node.clusterPath := by
  obtain ⟨_, p0, labeled, q0, hnorm, hlabels, hcoord, _, _, hproxy, hdrop,
    _, _, _⟩ := componentRunX_spec h
  have hp0 : p0.nodes[i]? = some ⟨node, false, none, false⟩ :=
    normalize_node_record hnorm hn
  have hlab : labeled.nodes[i]? = some ⟨node, false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels hp0 (by rfl)
  obtain ⟨j, res, hcoord', hb3, hres_h, hres_path, -⟩ :=
    X_self_coordinateGraph_title_copy hlab hb (by rfl)
  have hv : run.coordinateProper.nodes[labeled.nodes.length + j]? = some res := by
    rw [← hcoord]
    exact hcoord'
  obtain ⟨-, -, -, -, -, hrel2⟩ := proxyWidths_rel hproxy
  have hbnd : ¬ (res.node.border = -2 ∨ res.node.border = 2) := by
    rw [hb3]
    decide
  have hq0 : q0.nodes[labeled.nodes.length + j]? = some res :=
    (hrel2 _ res hv hbnd).1
  have hnodes : run.proper.nodes = q0.nodes := by
    have h := congrArg Proper.nodes hdrop
    rw [OrderImpl.dropSynthetic_nodes] at h
    exact h.symm
  have hproper : run.proper.nodes[labeled.nodes.length + j]? = some res := by
    rw [hnodes]
    exact hq0
  exact ⟨labeled.nodes.length + j, res, hproper, hb3, hres_h, hres_path⟩

/-- Actual height bound for a nonfixed group frame in a successful
`componentRunX` (exact replay of `componentRun_group_frame_height_ge`). -/
private theorem X_self_componentRunX_group_frame_height_ge {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node) (hb : node.border = -2)
    (hmem : node.clusterPath.contains node.decl)
    {th : Int} (hth : th + P.clusterPad ≤ node.h) :
    th + P.clusterPad ≤ (frameRect P cg run i).h := by
  obtain ⟨v, res, hv, -, hres_h, hres_path⟩ :=
    X_self_componentRunX_group_reservation h hn hb
  have hrect : Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains node.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    refine List.mem_filterMap.mpr ⟨(res, v), ?_, ?_⟩
    · exact List.mem_zipIdx_iff_getElem?.mpr hv
    · change (if res.node.clusterPath.contains node.decl then
          some (Labels.rectAt run.proper run.xs run.ys v) else none) = _
      rw [hres_path, ite_eq_left hmem]
  have hge := boundsOf_height_ge_member hrect
  have hrect_h : (Labels.rectAt run.proper run.xs run.ys v).h = node.h := by
    show RouteImpl.nodeH run.proper v = node.h
    unfold RouteImpl.nodeH
    rw [hv]
    exact hres_h
  rw [frameRect_group_height_eq_vertical_span hn hb]
  omega

/-- A nonempty loop-label list has positive extent (copy of
`nonempty_loop_extent_pos`). -/
private theorem X_self_nonempty_loop_extent_pos (slot : Int) (labels : List LoopLabel)
    (hs : 0 < slot) (hn : labels ≠ []) (hw : ∀ label ∈ labels, 0 ≤ label.width) :
    0 < Loops.extent slot labels := by
  cases labels with
  | nil => contradiction
  | cons label rest =>
    have he := Loops.outer_label_extent slot (label :: rest) (by omega) hw label (by simp)
    have hp := Int.mul_pos hs
      (show 0 < ((label :: rest).length : Int) + 1 by omega)
    have hl := hw label (by simp)
    omega

/-- A nonfixed group box of the exact measured graph carries a loop reservation
(copy of `SceneExecution.nonfixed_group_node_loop_reservation` over `graph0`). -/
private theorem X_self_nonfixed_group_node_loop_reservation {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {i : Nat} {box : ModelBox} (hb : inp.boxes[i]? = some box)
    (hrole : box.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false)
    (hloop : loopEdges execution.graph0.edges i ≠ []) :
    ∃ top : Node, execution.graph0.nodes[i]? = some top ∧ top.border = -2 ∧
      0 < top.loopExtent ∧
      Loops.requiredHeight execution.graph0.slot
        (loopSizes execution.graph0.edges execution.measured i execution.graph0.slot) ≤ top.h := by
  have hlines := X_self_lines_len execution
  have hi : i < execution.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hb).1
  have hslot : 0 < execution.params.slot := by
    have h := (checkedParams_valid execution.checked).2.2.1
    omega
  have hg := execution.graph0_eq
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, hm, hg⟩ := bind_ok hg
  obtain ⟨labels, hl, hg⟩ := bind_ok hg
  have hemetric : metric = execution.metric := Except.ok.inj (hm.symm.trans execution.metric_eq)
  subst hemetric
  have helabels : labels = execution.measured := Except.ok.inj (hl.symm.trans execution.measured_eq)
  subst helabels
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hprepare := (Except.ok.inj hg).symm
  let boxes := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box
  let titles := execution.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * execution.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  let raw : Graph := { nodes := nodes, edges := edges, slot := execution.params.slot }
  change execution.graph0 = Compound.prepare boxes execution.params.clusterPad titles raw at hprepare
  have hiboxes : i < boxes.length := by
    simpa only [boxes, List.length_map] using (List.getElem?_eq_some_iff.mp hb).1
  have hrawloops : loopEdges edges i ≠ [] := by
    have hp := prepare_loopEdges_preserved boxes execution.params.clusterPad titles raw i hiboxes
    rw [hprepare, hp] at hloop
    exact hloop
  have hsizes : loopSizes edges execution.measured i execution.params.slot ≠ [] := by
    intro he
    exact hrawloops (List.map_eq_nil_iff.mp he)
  have hwidth : ∀ label ∈ loopSizes edges execution.measured i execution.params.slot,
      0 ≤ label.width := by
    intro label hlabel
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hlabel
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hextent := X_self_nonempty_loop_extent_pos execution.params.slot
    (loopSizes edges execution.measured i execution.params.slot) hslot hsizes hwidth
  have hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial
  obtain ⟨before, _, hbefore⟩ :=
    hinit i (execution.lines[i], i)
      (by simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem hi,
        Option.map_some, Nat.zero_add])
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ :=
    hprocessed i (orientNode o.direction before, i)
      (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
        Option.map_some, Nat.zero_add])
  have hprops :
      after.h = Loops.requiredHeight execution.params.slot
        (loopSizes edges execution.measured i execution.params.slot) ∧
      0 < after.loopExtent := by
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hstep
    simp [hb, hfind, hrole, hfixed] at hstep
    split at hstep
    · cases hstep
    · split at hstep
      · cases hstep
      · have he := Except.ok.inj hstep
        subst after
        constructor
        · rfl
        · dsimp only
          omega
  have hinodes : i < nodes.length := (List.getElem?_eq_some_iff.mp hafter).1
  have hget : nodes[i]'hinodes = after := (List.getElem?_eq_some_iff.mp hafter).2
  have hbox : boxes[i]? = some box := by
    simp only [boxes, List.getElem?_map, hb, Option.map_some, hfixed,
      Bool.false_eq_true, ↓reduceIte]
  have hrecord := Compound.prepare_group_title_record boxes execution.params.clusterPad
    titles raw hinodes hbox hrole
  have hrecord' : execution.graph0.nodes[i]? =
      some { after with
        clusterPath := Compound.path boxes box ++ [i]
        border := -2
        w := (titles.getD i (0, 0)).1
        h := max ((titles.getD i (0, 0)).2 + execution.params.clusterPad) after.h } := by
    rw [hprepare]
    have hnonzero : (after.loopExtent == 0) = false :=
      Bool.eq_false_iff.mpr (by
        intro he
        have hz : after.loopExtent = 0 := beq_iff_eq.mp he
        omega)
    simpa only [raw, hget, hnonzero, Bool.false_eq_true, ↓reduceIte] using hrecord
  refine ⟨_, hrecord', rfl, hprops.2, ?_⟩
  rw [hprepare]
  change Loops.requiredHeight execution.params.slot
    (loopSizes (Compound.prepare boxes execution.params.clusterPad titles raw).edges
      execution.measured i execution.params.slot) ≤
    max ((titles.getD i (0, 0)).2 + execution.params.clusterPad) after.h
  rw [prepare_loopSizes_preserved boxes execution.params.clusterPad titles raw i hiboxes]
  rw [← hprops.1]
  exact Int.le_max_right _ _

private theorem X_self_group_candidate_frame_loop_reservation {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (component : List Nat) (hn : component.Nodup) (candidate v : Nat)
    (hv : v < component.length) {box : ModelBox}
    (hb : inp.boxes[component[v]]? = some box) (hrole : box.role = .group)
    {run : Run}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {node : Node}
    (hnode : (componentCandidate execution.graph component candidate).nodes[v]? = some node)
    (hexactFalse : run.exact.contains v = false)
    (hloop : loopEdges (componentCandidate execution.graph component candidate).edges v ≠ []) :
    Loops.requiredHeight (componentCandidate execution.graph component candidate).slot
      (loopSizes (componentCandidate execution.graph component candidate).edges execution.measured v
        (componentCandidate execution.graph component candidate).slot) ≤
      (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h := by
  have hlines := X_self_lines_len execution
  have hi : component[v] < execution.lines.length := by
    rw [hlines]; exact (List.getElem?_eq_some_iff.mp hb).1
  have hvCg : v < (componentCandidate execution.graph component candidate).nodes.length := by
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using hv
  have hnexact : (exactDecls exactIds inp).contains node.decl = false := by
    have h := X_self_run_exact_not_mem_of_not_contains hrun hvCg hexactFalse
    have hget : (componentCandidate execution.graph component candidate).nodes[v]? =
        some ((componentCandidate execution.graph component candidate).nodes[v]'hvCg) :=
      List.getElem?_eq_getElem hvCg
    have heq : node = (componentCandidate execution.graph component candidate).nodes[v]'hvCg :=
      Option.some.inj (hnode.symm.trans hget)
    rw [heq]; exact h
  have hklen : component[v] < execution.graph0.nodes.length := by
    have hge := measuredGraph_nodes_length_ge execution.graph0_eq hlines
    omega
  obtain ⟨nk, hk0⟩ : ∃ nk, execution.graph0.nodes[component[v]]? = some nk :=
    ⟨_, List.getElem?_eq_getElem hklen⟩
  have hpre := X_self_nonexact_node_eq execution hv hk0 hnode hnexact
  have hglobal : loopEdges execution.graph.edges component[v] ≠ [] := by
    intro he
    have hlen := congrArg List.length
      (X_self_componentCandidate_loopSizes_preserved execution.graph component hn candidate v hv
        execution.measured execution.graph.slot)
    simp only [loopSizes, List.length_map] at hlen
    rw [he, List.length_nil] at hlen
    exact hloop (List.length_eq_zero_iff.mp hlen)
  have hglobal0 : loopEdges execution.graph0.edges component[v] ≠ [] := by
    rw [exactGraph_edges execution.graph_eq] at hglobal
    exact hglobal
  obtain ⟨nodes, edges, titles, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hilen : component[v] < nodes.length := by
    rw [hlength, hlines]; exact (List.getElem?_eq_some_iff.mp hb).1
  have hrawk : nodes[component[v]]? = some (nodes[component[v]]'hilen) :=
    List.getElem?_eq_getElem hilen
  have hdraw : (nodes[component[v]]'hilen).decl = component[v] :=
    (hmetadata component[v] _ hrawk).1
  have hmap : ((inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box))[component[v]]? =
      some ((fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) box) := by
    simp only [List.getElem?_map, hb, Option.map_some]
  by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true
  · -- Fixed group: the box is exact, contradicting `hexactFalse`.
    have hFb : (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) = { box with role := .node } := by
      simp [hf]
    have hnotGroup : (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box : ModelBox).role ≠ .group := by
      rw [hFb]
      intro h
      exact BoxRole.noConfusion h
    have hrec0 := Compound.prepare_plain_node_record
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles
      { nodes := nodes, edges := edges, slot := execution.params.slot }
      hilen hmap hnotGroup
    have hnkd : nk.decl = component[v] := by
      have h1 : execution.graph0.nodes[component[v]]? = some nk := hk0
      rw [hprepared] at h1
      have heq := Option.some.inj (h1.symm.trans hrec0)
      rw [heq]; exact hdraw
    have hbeq : (box.role == .group) = true := by simp [hrole]
    have hpred : (exactIds.contains box.id ||
        (box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = true := by
      simp [hbeq, hf]
    have hmem : component[v] ∈ exactDecls exactIds inp := by
      unfold exactDecls
      apply List.mem_filterMap.mpr
      refine ⟨(box, component[v]), List.mem_zipIdx_iff_getElem?.mpr hb, ?_⟩
      show (if exactIds.contains box.id ||
        (box.role == .group && inp.fixedSizes.any (·.1 == box.id)) then
        some (component[v]) else none) = some (component[v])
      simp only [hpred, ↓reduceIte]
    have hcon : (exactDecls exactIds inp).contains component[v] = true := by
      rw [List.contains_eq_mem]; exact decide_eq_true hmem
    have hndd : node.decl = component[v] := by rw [hpre]; exact hnkd
    rw [hndd, hcon] at hnexact
    exact Bool.noConfusion hnexact
  · -- Nonfixed group: reservation transfers from the prepared node.
    have hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
      Bool.eq_false_of_ne_true hf
    have hFb : (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) = box := by
      simp [hfixed]
    have hmap' : ((inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box))[component[v]]? = some box := by
      simp [List.getElem?_map, hb, Option.map_some, hfixed]
    have hrec := Compound.prepare_group_title_record
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
      execution.params.clusterPad titles
      { nodes := nodes, edges := edges, slot := execution.params.slot }
      hilen hmap' hrole
    have hnkd : nk.decl = component[v] := by
      have h1 : execution.graph0.nodes[component[v]]? = some nk := hk0
      rw [hprepared] at h1
      have heq := Option.some.inj (h1.symm.trans hrec)
      rw [heq]; exact hdraw
    have hborder_nk : nk.border = -2 := by
      have h1 : execution.graph0.nodes[component[v]]? = some nk := hk0
      rw [hprepared] at h1
      have heq := Option.some.inj (h1.symm.trans hrec)
      rw [heq]
    have hborder' : node.border = -2 := by rw [hpre]; exact hborder_nk
    have htop0 : (componentCandidate execution.graph0 component candidate).nodes[v]? = some nk := by
      rw [componentCandidate_nodes]
      change (component.map fun source => execution.graph0.nodes.getD source default)[v]? = some nk
      simp only [List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some,
        List.getD_eq_getElem?_getD, hk0, Option.getD_some]
    have hbox' : inp.boxes[component.getD v 0]? = some box := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
        Option.getD_some] using hb
    have hmember := actual_group_self_membership execution.graph0_eq htop0 hborder_nk hbox'
    have hmember' : node.clusterPath.contains node.decl := by
      rw [hpre]; exact hmember
    obtain ⟨top, htop, hborder, _, hheight⟩ :=
      X_self_nonfixed_group_node_loop_reservation execution hb hrole hfixed hglobal0
    have htopnk : top = nk := Option.some.inj (htop.symm.trans hk0)
    rw [htopnk] at hheight
    have hslot := X_self_graph_slot_eq execution
    have hloopX :
        loopSizes (componentCandidate execution.graph component candidate).edges execution.measured v
          (componentCandidate execution.graph component candidate).slot =
        loopSizes execution.graph0.edges execution.measured component[v] execution.graph0.slot := by
      rw [X_self_componentCandidate_slot execution.graph component candidate,
        X_self_componentCandidate_loopSizes_preserved execution.graph component hn candidate v hv
          execution.measured _,
        exactGraph_edges execution.graph_eq, hslot]
    have hframe : nk.h ≤
        (frameRect execution.params (componentCandidate execution.graph component candidate) run v).h := by
      have h := X_self_componentRunX_group_frame_height_ge hrun hnode hborder' hmember'
        (th := nk.h - execution.params.clusterPad) (by rw [hpre]; omega)
      simpa only [Int.sub_add_cancel] using h
    rw [hloopX, X_self_componentCandidate_slot execution.graph component candidate, hslot]
    exact Int.le_trans hheight hframe
/-- Exact ordinary loop attachment (exact replay of
`SceneExecution.componentLoops_ordinary_attachment` over `componentRunX` /
`placeBoundsX`). -/
private theorem X_ordinary_attachment {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (component : List Nat) (hcomponent : component ∈ components execution.graph)
    (candidate : Nat) {run : Run}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph component candidate) run execution.measured = .ok loops)
    {q : Nat × LoopPlacement} (hq : q ∈ loops)
    (margin : Int) (direction : Direction) (canvasH boxX boxY : Int) :
    ∃ v, ∃ hv : v < component.length, ∃ placements : List LoopPlacement, ∃ edge : Edge,
      (edge, q.2) ∈
        (loopEdges (componentCandidate execution.graph component candidate).edges v).zip placements ∧
      q.1 = edge.decl ∧ edge.tail = v ∧ edge.head = v ∧
      (∀ box : ModelBox, inp.boxes[component[v]]? = some box → box.role = .node →
        ∃ start finish : Point,
          q.2.points.head? = some start ∧ q.2.points.getLast? = some finish ∧
          let bounds := placeBoundsX execution.params
            (componentCandidate execution.graph component candidate) run execution.measured loops
          let transport := routePointTransport margin direction canvasH boxX boxY bounds.minX bounds.minY
          let rect := shiftRect margin margin (orientRect direction canvasH
            (shiftRect (boxX - bounds.minX) (boxY - bounds.minY)
              (frameRect execution.params (componentCandidate execution.graph component candidate) run v)))
          Validator.onBoundary (transport start) rect ∧
            Validator.onBoundary (transport finish) rect) := by
  obtain ⟨v, hv, placements, hp, edge, he, hdecl, htail, hhead⟩ :=
    componentLoops_entry_origin hloops hq
  have hv' : v < component.length := by
    rw [componentCandidate_nodes] at hv
    simpa only [componentGraph, List.length_map] using hv
  refine ⟨v, hv', placements, edge, he, hdecl, htail, hhead, ?_⟩
  intro box hb hrole
  have hboundary : ∃ start finish : Point,
      q.2.points.head? = some start ∧ q.2.points.getLast? = some finish ∧
      Validator.onBoundary start
        (frameRect execution.params (componentCandidate execution.graph component candidate) run v) ∧
      Validator.onBoundary finish
        (frameRect execution.params (componentCandidate execution.graph component candidate) run v) := by
    by_cases hexact : run.exact.contains v = true
    · have hp' : (Loops.exactLoops
          (frameRect execution.params (componentCandidate execution.graph component candidate) run v)
          (componentCandidate execution.graph component candidate).slot
          (loopSizes (componentCandidate execution.graph component candidate).edges
            execution.measured v
            (componentCandidate execution.graph component candidate).slot)) = .ok placements := by
        rw [hexact] at hp; simpa using hp
      exact Loops.exactLoops_boundary hp' (List.of_mem_zip he).2
    · have hef : run.exact.contains v = false := by
        cases h : run.exact.contains v with
        | true => exact absurd h hexact
        | false => rfl
      have hp' : (Loops.loops
          (frameRect execution.params (componentCandidate execution.graph component candidate) run v)
          (componentCandidate execution.graph component candidate).slot
          (loopSizes (componentCandidate execution.graph component candidate).edges
            execution.measured v
            (componentCandidate execution.graph component candidate).slot)) = .ok placements := by
        rw [hef] at hp; simpa using hp
      have hvCg : v < (componentCandidate execution.graph component candidate).nodes.length := by
        rw [componentCandidate_nodes]
        simpa only [componentGraph, List.length_map] using hv'
      have hnode : (componentCandidate execution.graph component candidate).nodes[v]? =
          some ((componentCandidate execution.graph component candidate).nodes[v]'hvCg) :=
        List.getElem?_eq_getElem hvCg
      exact Loops.loops_boundary_of_reservation hp'
        (X_self_ordinary_reservation execution component
          (components_nodup _ _ hcomponent) candidate v hv' hb hrole hrun hnode hef)
        (List.of_mem_zip he).2
  obtain ⟨start, finish, hs, ht, hsb, htb⟩ := hboundary
  refine ⟨start, finish, hs, ht, ?_⟩
  dsimp only
  constructor
  · apply (onBoundary_shift _ _ _ _).mpr
    apply (onBoundary_orient _ _ _ _).mpr
    exact (onBoundary_shift _ _ _ _).mpr hsb
  · apply (onBoundary_shift _ _ _ _).mpr
    apply (onBoundary_orient _ _ _ _).mpr
    exact (onBoundary_shift _ _ _ _).mpr htb

/-- Exact group emitted-loop attachment (exact replay of
`SceneExecution.componentLoops_group_emitted_attachment` over `componentRunX` /
`placeBoundsX`). -/
private theorem X_group_emitted_attachment {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (component : List Nat) (hcomponent : component ∈ components execution.graph)
    (candidate : Nat) {run : Run}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph component candidate) run execution.measured = .ok loops)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph component candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head) {source : ModelBox}
    (hsource : inp.boxes[component.getD edge.tail 0]? = some source)
    (hrole : source.role = .group) :
    ∃ loop ∈ loops,
      loops.find? (fun q => q.1 == edge.decl) = some loop ∧ loop.1 = edge.decl ∧
      let bounds := placeBoundsX execution.params
        (componentCandidate execution.graph component candidate) run execution.measured loops
      let points := loop.2.points.map (shiftPoint (0 - bounds.minX) (-bounds.minY))
      let rect := shiftRect (0 - bounds.minX) (-bounds.minY)
        (frameRect execution.params (componentCandidate execution.graph component candidate) run edge.tail)
      (placeComponentExact execution.params (componentCandidate execution.graph component candidate)
        run 0 execution.measured loops).routes[i]? = some (edge.decl, points) ∧
      ∃ start finish : Point, points.head? = some start ∧ points.getLast? = some finish ∧
        Validator.onBoundary start rect ∧ Validator.onBoundary finish rect := by
  obtain ⟨_, _, _, _, hnormalize, _⟩ := componentRunX_spec hrun
  have hbounds := RankImpl.wellformed_spec (normalize_node_rank_alignment hnormalize).2
    edge (List.mem_of_getElem? hedge)
  have hv : edge.tail < component.length := by
    have h := hbounds.1
    rw [componentCandidate_nodes] at h
    simpa only [componentGraph, List.length_map] using h
  have hbox : inp.boxes[component[edge.tail]]? = some source := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
      Option.getD_some] using hsource
  obtain ⟨loop, hloop, hfind, hdecl, hemitted⟩ :=
    X_componentLoops_emitted_self_edgeX hloops hedge hbounds.1 hself 0
  obtain ⟨v, _, placements, hp, loopEdge, hzip, hloopDecl, htail, _⟩ :=
    componentLoops_entry_origin hloops hloop
  have hloopEdge : loopEdge ∈
      (componentCandidate execution.graph component candidate).edges :=
    (List.mem_filter.mp (List.of_mem_zip hzip).1).1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hloopEdge
  have hdecls := componentCandidate_decls_nodup execution.graph component candidate
    (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
  have hmap :
      ((componentCandidate execution.graph component candidate).edges.map Edge.decl)[i]? =
      ((componentCandidate execution.graph component candidate).edges.map Edge.decl)[j]? := by
    simp only [List.getElem?_map, hedge, hj, Option.map_some]
    exact congrArg some (hdecl.symm.trans hloopDecl)
  have hi : i < ((componentCandidate execution.graph component candidate).edges.map Edge.decl).length := by
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
  have hij : i = j := (hdecls.getElem?_inj hi).mp hmap
  have he : edge = loopEdge := by
    subst j
    exact Option.some.inj (hedge.symm.trans hj)
  subst loopEdge
  subst v
  have hboundary : ∃ start finish : Point,
      loop.2.points.head? = some start ∧ loop.2.points.getLast? = some finish ∧
      Validator.onBoundary start
        (frameRect execution.params (componentCandidate execution.graph component candidate) run edge.tail) ∧
      Validator.onBoundary finish
        (frameRect execution.params (componentCandidate execution.graph component candidate) run edge.tail) := by
    by_cases he : run.exact.contains edge.tail = true
    · have hp' : (Loops.exactLoops
          (frameRect execution.params (componentCandidate execution.graph component candidate) run edge.tail)
          (componentCandidate execution.graph component candidate).slot
          (loopSizes (componentCandidate execution.graph component candidate).edges
            execution.measured edge.tail
            (componentCandidate execution.graph component candidate).slot)) = .ok placements := by
        rw [he] at hp; simpa using hp
      exact Loops.exactLoops_boundary hp' (List.of_mem_zip hzip).2
    · have hef : run.exact.contains edge.tail = false := by
        cases h : run.exact.contains edge.tail with
        | true => exact absurd h he
        | false => rfl
      have hp' : (Loops.loops
          (frameRect execution.params (componentCandidate execution.graph component candidate) run edge.tail)
          (componentCandidate execution.graph component candidate).slot
          (loopSizes (componentCandidate execution.graph component candidate).edges
            execution.measured edge.tail
        (componentCandidate execution.graph component candidate).slot)) = .ok placements := by
        rw [hef] at hp; simpa using hp
      have hvCg : edge.tail < (componentCandidate execution.graph component candidate).nodes.length := by
        rw [componentCandidate_nodes]
        simpa only [componentGraph, List.length_map] using hv
      have hnode : (componentCandidate execution.graph component candidate).nodes[edge.tail]? =
          some ((componentCandidate execution.graph component candidate).nodes[edge.tail]'hvCg) :=
        List.getElem?_eq_getElem hvCg
      have hloopne : loopEdges (componentCandidate execution.graph component candidate).edges edge.tail ≠ [] := by
        intro hempty
        have hm := (List.of_mem_zip hzip).1
        rw [hempty] at hm
        cases hm
      exact Loops.loops_boundary_of_reservation hp'
        (X_self_group_candidate_frame_loop_reservation execution component
          (components_nodup _ _ hcomponent) candidate edge.tail hv hbox hrole hrun hnode
          hef hloopne)
        (List.of_mem_zip hzip).2
  obtain ⟨start, finish, hs, ht, hsb, htb⟩ := hboundary
  refine ⟨loop, hloop, hfind, hdecl, hemitted, ?_⟩
  let bounds := placeBoundsX execution.params
    (componentCandidate execution.graph component candidate) run execution.measured loops
  refine ⟨shiftPoint (0 - bounds.minX) (-bounds.minY) start,
    shiftPoint (0 - bounds.minX) (-bounds.minY) finish, ?_, ?_, ?_, ?_⟩
  · simp only [List.head?_map, hs, Option.map_some, bounds]
  · simp only [List.getLast?_map, ht, Option.map_some, bounds]
  · exact (onBoundary_shift _ _ _ _).mpr hsb
  · exact (onBoundary_shift _ _ _ _).mpr htb

/-- Point transport across exact emitted self-loop shifts (`-minY` form of
`routePointTransport_eq`). -/
private theorem X_self_routePointTransport_eq (margin : Int) (d : Direction) (h : Int)
    (boxX boxY minX minY : Int) (pts : List Point) :
    ((pts.map (shiftPoint (0 - minX) (-minY))).map (shiftPoint boxX boxY)).map
      (fun p => shiftPoint margin margin (orientPoint d h p)) =
    pts.map (routePointTransport margin d h boxX boxY minX minY) := by
  simp only [List.map_map]
  congr 1
  funext p
  have hs : shiftPoint boxX boxY (shiftPoint (0 - minX) (-minY) p) =
      shiftPoint (boxX - minX) (boxY - minY) p := by
    cases p
    simp only [shiftPoint, Point.mk.injEq]
    constructor <;> omega
  exact congrArg (fun q => shiftPoint margin margin (orientPoint d h q)) hs

/-- Rect transport across exact emitted self-loop shifts (`-minY` form of
`shiftRect_pack_normalize`). -/
private theorem X_self_shiftRect_pack_normalize (boxX boxY minX minY : Int) (rect : Rect) :
    shiftRect boxX boxY (shiftRect (0 - minX) (-minY) rect) =
      shiftRect (boxX - minX) (boxY - minY) rect := by
  dsimp only [shiftRect]
  congr 1 <;> omega

/-- Exact self-loop model key bundle: route/raw endpoint facts plus the
component-local tail key and the first-occurrence box index. -/
private theorem X_self_model_key {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {component : List Nat} (hcomponent : component ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph component candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph component candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head) :
    ∃ index route raw source target,
      inp.routes[index]? = some route ∧ edge.decl = index ∧
      edgeOf inp route index = .ok raw ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = route.toId ∧
      route.fromId = route.toId ∧ raw.tail = raw.head ∧
      component[edge.tail]? = some raw.tail ∧
      inp.boxes.findIdx? (fun b => b.id == route.fromId) = some raw.tail := by
  obtain ⟨index, route, raw, source, target, hroute, hrawOf, hdeclIdx,
    hsource, hsourceId, htarget, htargetId, hsem⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq
      (List.mem_of_getElem? hedge)
  obtain ⟨route', hroute', hselfId', _⟩ := X_self_route_ids execution hcomponent hedge hself
  have hroute'' : inp.routes[index]? = some route' := by
    rw [← hdeclIdx]; exact hroute'
  have hrt : route' = route := Option.some.inj (hroute''.symm.trans hroute)
  have hselfRoute : route.fromId = route.toId := by rw [← hrt]; exact hselfId'
  have hrawSelfFind : raw.tail = raw.head ∧
      inp.boxes.findIdx? (fun b => b.id == route.fromId) = some raw.tail := by
    unfold edgeOf at hrawOf
    rw [← hselfRoute] at hrawOf
    cases hfind : inp.boxes.findIdx? (fun b => b.id == route.fromId) with
    | none => simp only [hfind] at hrawOf; contradiction
    | some v =>
      simp only [hfind] at hrawOf
      have heq := Except.ok.inj hrawOf
      have htv : v = raw.tail := congrArg Edge.tail heq
      have hhv : v = raw.head := congrArg Edge.head heq
      exact ⟨htv.symm.trans hhv, congrArg some htv⟩
  obtain ⟨hrawSelf, hfindIdx⟩ := hrawSelfFind
  have halias : Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) raw = raw := by
    cases raw with
    | mk tail head minLen decl reversed =>
      dsimp only at hrawSelf
      subst head
      let boxes := inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box
      change Compound.aliasEdge boxes ⟨tail, tail, minLen, decl, reversed⟩ =
        ⟨tail, tail, minLen, decl, reversed⟩
      cases hbox : boxes[tail]? <;> simp [Compound.aliasEdge, Compound.endpoint, hbox]
  dsimp only at hsem
  rw [halias] at hsem
  have htail : (if edge.reversed then edge.head else edge.tail) =
      component.idxOf raw.tail := by
    have h := congrArg Edge.tail hsem
    cases hr : edge.reversed <;>
      simpa only [Edge.original, hr, Bool.false_eq_true, ↓reduceIte] using h
  have hhead : (if edge.reversed then edge.tail else edge.head) =
      component.idxOf raw.tail := by
    have h := congrArg Edge.head hsem
    rw [← hrawSelf] at h
    cases hr : edge.reversed <;>
      simpa only [Edge.original, hr, Bool.false_eq_true, ↓reduceIte] using h
  simp only [← hself, ite_self] at htail
  obtain ⟨_, _, _, _, hnormalize, _⟩ := componentRunX_spec hrun
  have hbounds := RankImpl.wellformed_spec (normalize_node_rank_alignment hnormalize).2
    edge (List.mem_of_getElem? hedge)
  have hlength : (componentCandidate execution.graph component candidate).nodes.length =
      component.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have hv : component.idxOf raw.tail < component.length := by omega
  refine ⟨index, route, raw, source, target, hroute, hdeclIdx, hrawOf, hsource,
    hsourceId, htarget, htargetId, hselfRoute, hrawSelf, ?_, hfindIdx⟩
  rw [htail, List.getElem?_eq_getElem hv]
  exact congrArg some (List.getElem_idxOf hv)

/-- Exact part-entry dump lookup without box-id nodup, via first-occurrence
index (`source_box_lookup_firstX` + `actual_components_packed_rect_valueX`). -/
private theorem SceneExecutionX.part_entry_box_lookup_firstX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} {rect : Rect}
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    {source : ModelBox}
    (hfirst : inp.boxes.findIdx? (fun b => b.id == source.id) = some key)
    (hsource : inp.boxes[key]? = some source) :
    res.scene.layoutDump.box? source.id =
      some (Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y rect)))
        source.parent source.exclusive) := by
  have hsize : execution.componentsAcc.rects.size = inp.boxes.length :=
    execution.components_rects_size
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [hsize]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hrect := actual_components_packed_rect_valueX (by rfl) execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hkeysize default
  have hlookup := execution.source_box_lookup_firstX hfirst hsource
  rw [hrect] at hlookup
  exact hlookup

/-- Exact self-loop route rows: every self-loop candidate edge of an executed
exact layout attaches both endpoints to the boundary of its endpoint dump
boxes. -/
theorem x_selfRoutes_holds (exactIds : List String) : X_SelfRoutes exactIds := by
  intro inp o res execution packed hpacked c q hselected candidate run loops area
    hrun hloops hpart i edge hedge hself mroute hrouteD
  obtain ⟨hparts, _⟩ := actual_components_parts_geometryX (by rfl) execution.components_eq
  have hcomponent : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
  obtain ⟨index, route, raw, source, target, hroute, hdeclIdx, hrawOf,
    hsource, hsourceId, htarget, htargetId, hselfRoute, hrawSelf, hfromKey, hfindIdx⟩ :=
    X_self_model_key execution hcomponent hrun hedge hself
  have hdecl : edge.decl = index := hdeclIdx
  have hrouteD' : inp.routes[index]? = some mroute := by rw [← hdecl]; exact hrouteD
  have hrt : route = mroute := Option.some.inj (hroute.symm.trans hrouteD')
  have hmrouteSelf : mroute.fromId = mroute.toId := by rw [← hrt]; exact hselfRoute
  have hsourceId' : source.id = mroute.fromId :=
    hsourceId.trans (congrArg ModelRoute.fromId hrt)
  have htargetId' : target.id = mroute.toId :=
    htargetId.trans (congrArg ModelRoute.toId hrt)
  have hst : source = target := by
    rw [hrawSelf] at hsource
    exact Option.some.inj (hsource.symm.trans htarget)
  have hfirst : inp.boxes.findIdx? (fun b => b.id == source.id) = some raw.tail := by
    rw [hsourceId]; exact hfindIdx
  have hsourceAt : inp.boxes[q.1.1.getD edge.tail 0]? = some source := by
    simpa only [List.getD_eq_getElem?_getD, hfromKey, Option.getD_some] using hsource
  have hedgeDecl : edge.decl < inp.routes.length :=
    (List.getElem?_eq_some_iff.mp hrouteD).1
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured edge.decl hedgeDecl
  rw [← execution.scene_eq] at hscene
  have hmrouteGet : inp.routes[edge.decl]'hedgeDecl = mroute :=
    Option.some.inj ((List.getElem?_eq_getElem hedgeDecl).symm.trans hrouteD)
  rw [hmrouteGet] at hscene
  let out : Route := ⟨mroute.id, mroute.fromId, mroute.toId, mroute.orthogonal,
    (execution.packedAcc.routes.getD edge.decl []).map (fun p =>
      shiftPoint execution.params.canvasMargin execution.params.canvasMargin
        (orientPoint o.direction execution.packedAcc.canvasH p))⟩
  have houtScene : res.scene.routes[edge.decl]? = some out := by
    exact hscene
  cases hrole : source.role with
  | node =>
    have hv : edge.tail <
        (componentCandidate execution.graph q.1.1 candidate).nodes.length := by
      rw [componentCandidate_nodes]
      simpa only [componentGraph, List.length_map] using
        (List.getElem?_eq_some_iff.mp hfromKey).1
    obtain ⟨native, hnative, _, hnativeDecl, hemitted⟩ :=
      X_componentLoops_emitted_self_edgeX hloops hedge hv hself 0
    have hpartRoutes : q.1.2.routes =
        (placeComponentExact execution.params
          (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
          loops).routes := by rw [hpart]
    rw [← hpartRoutes] at hemitted
    have hndCg : ((componentCandidate execution.graph q.1.1 candidate).edges.map
        (·.decl)).Nodup :=
      componentCandidate_decls_nodup execution.graph q.1.1 candidate
        (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
    have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
      rw [hpartRoutes]
      exact X_placeComponentExact_routes_decls_nodup execution.params
        (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
        loops hndCg
    have hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
      rw [execution.components_routes_sizeX]
      exact (List.getElem?_eq_some_iff.mp hrouteD).1
    have hpackedRoute := X_actual_components_packAcc_routes_getDX (by rfl)
      execution.components_eq (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
      packed execution.packed_eq hpacked c q hselected i _ _ [] hemitted hpartNodup hrouteSize
    obtain ⟨v, hvComponent, placements, origin, horigin, horiginDecl,
      horiginTail, _, hattachment⟩ :=
      X_ordinary_attachment execution q.1.1 hcomponent candidate hrun hloops hnative
        execution.params.canvasMargin o.direction execution.packedAcc.canvasH
        q.2.x q.2.y
    have horiginMem : origin ∈ (componentCandidate execution.graph q.1.1 candidate).edges :=
      (List.mem_filter.mp (show origin ∈
        loopEdges (componentCandidate execution.graph q.1.1 candidate).edges v from
        (List.of_mem_zip horigin).1)).1
    have horiginEq : origin = edge :=
      nodup_map_eq_of_mem hndCg horiginMem (List.mem_of_getElem? hedge)
        (horiginDecl.symm.trans hnativeDecl)
    have hvEq : v = edge.tail :=
      horiginTail.symm.trans (congrArg Edge.tail horiginEq)
    have hsourceAtV : inp.boxes[q.1.1[v]]? = some source := by
      have hkeyAt : q.1.1[v]? = some raw.tail := by rw [hvEq]; exact hfromKey
      have heq : q.1.1[v] = raw.tail :=
        Option.some.inj ((List.getElem?_eq_getElem hvComponent).symm.trans hkeyAt)
      rw [heq]
      exact hsource
    obtain ⟨start, finish, hstart, hfinish, hboundary⟩ :=
      hattachment source hsourceAtV hrole
    have hentry := X_chosen_part_frame_entry hpart
      (show q.1.1[v]? = some raw.tail by rw [hvEq]; exact hfromKey)
    have hlookup := execution.part_entry_box_lookup_firstX packed hpacked hselected
      hentry hfirst hsource
    rw [X_self_shiftRect_pack_normalize] at hlookup
    let bounds := placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops
    let transport := routePointTransport execution.params.canvasMargin o.direction
      execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
    have houtPoints : out.points = native.2.points.map transport := by
      show (execution.packedAcc.routes.getD edge.decl []).map
        (fun p => shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)) = _
      rw [hpackedRoute, X_self_routePointTransport_eq]
    let box := Box.mk source.id source.role.id
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v))))
      source.parent source.exclusive
    refine ⟨source, List.mem_of_getElem? hsource, target,
      List.mem_of_getElem? htarget, hsourceId', htargetId', out, transport start,
      transport finish, box, box, houtScene, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [houtPoints, List.head?_map, hstart]
      rfl
    · rw [houtPoints, List.getLast?_map, hfinish]
      rfl
    · have houtFrom : out.fromId = mroute.fromId := rfl
      rw [houtFrom, ← hsourceId']
      exact hlookup
    · have houtTo : out.toId = mroute.toId := rfl
      rw [houtTo, ← hmrouteSelf, ← hsourceId']
      exact hlookup
    · exact hboundary.1
    · exact hboundary.2
  | group =>
    obtain ⟨loop, hloop, hfind, hloopDecl, hemitted, start, finish, hstart,
      hfinish, hsb, htb⟩ :=
      X_group_emitted_attachment execution q.1.1 hcomponent candidate hrun hloops hedge
        hself hsourceAt hrole
    have hpartRoutes : q.1.2.routes =
        (placeComponentExact execution.params
          (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
          loops).routes := by rw [hpart]
    rw [← hpartRoutes] at hemitted
    have hndCg : ((componentCandidate execution.graph q.1.1 candidate).edges.map
        (·.decl)).Nodup :=
      componentCandidate_decls_nodup execution.graph q.1.1 candidate
        (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
    have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
      rw [hpartRoutes]
      exact X_placeComponentExact_routes_decls_nodup execution.params
        (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
        loops hndCg
    have hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
      rw [execution.components_routes_sizeX]
      exact (List.getElem?_eq_some_iff.mp hrouteD).1
    have hpackedRoute := X_actual_components_packAcc_routes_getDX (by rfl)
      execution.components_eq (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
      packed execution.packed_eq hpacked c q hselected i _ _ [] hemitted hpartNodup hrouteSize
    have hentry := X_chosen_part_frame_entry hpart hfromKey
    have hlookup := execution.part_entry_box_lookup_firstX packed hpacked hselected
      hentry hfirst hsource
    let bounds := placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops
    let points := loop.2.points.map (shiftPoint (0 - bounds.minX) (-bounds.minY))
    let rect := shiftRect (0 - bounds.minX) (-bounds.minY)
      (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run edge.tail)
    let transport := fun p => shiftPoint execution.params.canvasMargin
      execution.params.canvasMargin
      (orientPoint o.direction execution.packedAcc.canvasH (shiftPoint q.2.x q.2.y p))
    have houtPoints : out.points = points.map transport := by
      have hpoints : out.points =
          (execution.packedAcc.routes.getD edge.decl []).map
            (fun p => shiftPoint execution.params.canvasMargin
              execution.params.canvasMargin
              (orientPoint o.direction execution.packedAcc.canvasH p)) := rfl
      rw [hpackedRoute] at hpoints
      simpa only [List.map_map, Function.comp_def, points, bounds, transport] using hpoints
    let box := Box.mk source.id source.role.id
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y rect))) source.parent source.exclusive
    refine ⟨source, List.mem_of_getElem? hsource, target,
      List.mem_of_getElem? htarget, hsourceId', htargetId', out,
      transport start, transport finish, box, box, houtScene, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [houtPoints, List.head?_map, hstart]
      rfl
    · rw [houtPoints, List.getLast?_map, hfinish]
      rfl
    · have houtFrom : out.fromId = mroute.fromId := rfl
      rw [houtFrom, ← hsourceId']
      exact hlookup
    · have houtTo : out.toId = mroute.toId := rfl
      rw [houtTo, ← hmrouteSelf, ← hsourceId']
      exact hlookup
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsb
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htb

theorem X_chosen_part_loop_attached_frame_miss
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head)
    {key : Nat} (hkey : q.1.1[edge.tail]? = some key)
    {src : ModelBox} (hsrc : inp.boxes[key]? = some src)
    {pr : Route} (hpr : res.scene.routes[edge.decl]? = some pr)
    {frame : Box} (hframe : res.scene.layoutDump.box? src.id = some frame) :
    ¬ Polyline.hitsRect pr.points frame.rect := by
  let cg := componentCandidate execution.graph q.1.1 candidate
  have hv : edge.tail < cg.nodes.length := by
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using
      (List.getElem?_eq_some_iff.mp hkey).1
  obtain ⟨native, hnative, _, hnativeDecl, hemitted⟩ :=
    X_componentLoops_emitted_self_edgeX hloops hedge hv hself 0
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup execution.graph q.1.1 candidate
      (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
  obtain ⟨v, _, origin, horigin, horiginDecl, horiginTail, _, hmiss⟩ :=
    componentLoops_entry_misses_owner hloops hnative
  have horiginMem : origin ∈ cg.edges := (List.mem_filter.mp horigin).1
  have horiginEq : origin = edge :=
    nodup_map_eq_of_mem hnd horiginMem (List.mem_of_getElem? hedge)
      (horiginDecl.symm.trans hnativeDecl)
  have hvEq : v = edge.tail := horiginTail.symm.trans (congrArg Edge.tail horiginEq)
  rw [hvEq] at hmiss
  have hpartRoutes : q.1.2.routes =
      (placeComponentExact execution.params cg run 0 execution.measured loops).routes := by
    rw [hpart]
  rw [← hpartRoutes] at hemitted
  have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
    rw [hpartRoutes]
    exact X_placeComponentExact_routes_decls_nodup execution.params cg run 0 execution.measured loops hnd
  obtain ⟨index, route, _, _, _, hroute, _, hdeclIdx, _, _, _, _, _⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq
      (List.mem_of_getElem? hedge)
  have hroute' : inp.routes[edge.decl]? = some route := by rw [hdeclIdx]; exact hroute
  have hscene := X_chosen_part_route_from_points execution packed hpacked hselected
    hemitted hpartNodup hroute'
  have hbox := X_DumpLookup_holds exactIds execution hwf packed hpacked
    hselected hpart hkey hsrc
  have hrEq := Option.some.inj (hpr.symm.trans hscene)
  have hbEq := Option.some.inj (hframe.symm.trans hbox)
  rw [hrEq, hbEq]
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
    execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY

end PipelineImpl

end Layered
end Elegant

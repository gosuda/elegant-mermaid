import Elegant.Layered.ExactFlatForeignLoopProof
import Elegant.Layered.RegionGroupEndpointProof
import Elegant.Layered.RegionFlatInset
import Elegant.Layered.RegionPartSizingClosed

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem candidateDeclsR (spec : Option RegionSpec) (g : Graph) (comp : List Nat)
    (index : Nat) :
    (componentCandidateR spec g comp index).edges.map (·.decl) =
      (componentGraph g comp).edges.map (·.decl) := by
  cases spec with
  | none => exact componentCandidate_decls g comp index
  | some spec =>
    unfold componentCandidateR
    dsimp only
    let raw := componentGraph g comp
    let source := { raw with edges := raw.edges.map Edge.original }
    let flags := if index == 2 then groupGreedyFlags source
      else List.replicate source.edges.length false
    let orient := fun q : Edge × Nat => if flags.getD q.2 false then
      { q.1 with tail := q.1.head, head := q.1.tail, reversed := true } else q.1
    have hdecl : (fun e : Edge => e.decl) ∘ orient =
        (fun e : Edge => e.decl) ∘ Prod.fst := by
      funext q
      simp only [Function.comp_def, orient]
      split <;> rfl
    change (((source.edges.zipIdx).map orient).map (·.decl)) = raw.edges.map (·.decl)
    rw [List.map_map, hdecl, ← List.map_map, List.zipIdx_map_fst]
    simp only [source, List.map_map, Function.comp_def, Edge.original_decl]

private theorem actualPartRouteKeysR {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {labels : List MeasuredLabel} {q : List Nat × Part}
    (h : ActualPartGeometryR P exactIds spec inp o g labels q) :
    q.2.routes.map (·.1) = (componentGraph g q.1).edges.map (·.decl) := by
  obtain ⟨index, _, cg, run, loops, _, used, _, _, _, _, hrun, _, hpart⟩ := h
  rw [hpart]
  change (placeComponentExact P cg run 0 labels loops).routes.map (·.1) = _
  calc
    _ = cg.edges.map (·.decl) := by
      unfold placeComponentExact
      dsimp only
      rw [List.map_map]
      exact zipIdx_map_comp (·.decl) cg.edges 0
    _ = _ := (componentRunR_edges_declsR hrun).trans (candidateDeclsR used g q.1 index)

private theorem partRouteKey_owned {g : Graph} {comp : List Nat} {d : Nat}
    (h : d ∈ (componentGraph g comp).edges.map (·.decl)) : ownsDecl g comp d := by
  have hm : d ∈ (componentCandidate g comp 0).edges.map (·.decl) := by
    rwa [componentCandidate_decls]
  obtain ⟨edge, he, rfl⟩ := List.mem_map.mp hm
  exact componentCandidate_edge_owns he

private theorem componentFoldRoutesSizeR (P : Params) (exactIds : List String)
    (spec : Option RegionSpec) (inp : Input) (o : Options) (g : Graph)
    (measured : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp measured)
        start = .ok out → out.routes.size = start.routes.size
  | [], start, out, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
  | comp :: rest, start, out, h => by
    simp only [List.foldlM_cons] at h
    cases hc : layoutComponentR P exactIds spec inp o g start comp measured with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      exact (componentFoldRoutesSizeR P exactIds spec inp o g measured rest next out h).trans
        (layoutComponentR_sizes hc).2.1.symm

set_option maxHeartbeats 700000 in
theorem SceneExecutionR.chosenPartRoute_points
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} {pts : List Point} (hlocal : q.1.2.routes[i]? = some (key, pts))
    {route : Route} (hroute : res.scene.routes[key]? = some route) :
    route.points = (pts.map (shiftPoint q.2.x q.2.y)).map (fun p =>
      shiftPoint execution.params.canvasMargin execution.params.canvasMargin
        (orientPoint o.direction execution.packedAcc.canvasH p)) := by
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length execution.params inp o execution.lines
      execution.packedAcc execution.measured
  have hkey : key < inp.routes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hroute).1
  have hsize := componentFoldRoutesSizeR execution.params exactIds _ inp o execution.graph
    execution.measured (components execution.graph) _ _ execution.components_eq
  have hbound : key < execution.componentsAcc.routes.size := by
    rw [hsize, Array.size_replicate]
    exact hkey
  obtain ⟨hparts, hall⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  have hget := zip_getElem?_left hselected
  have hkeys := actualPartRouteKeysR (hall q.1 (List.mem_of_getElem? hget))
  have hndGraph := exactGraph_decls_nodup execution.graph0_eq execution.graph_eq
  have hnd : (q.1.2.routes.map (·.1)).Nodup := by
    rw [hkeys]
    exact componentGraph_decls_nodup _ _ hndGraph
  have hkeyMem : key ∈ q.1.2.routes.map (·.1) :=
    List.mem_map_of_mem (List.mem_of_getElem? hlocal)
  have hread := packAcc_routes_getD execution.packed_eq packed hpacked c q hselected
    i key pts [] hlocal hnd hbound (by
      intro other hother
      obtain ⟨j, hcj, hget'⟩ := zip_drop_mem_later_getElem? hother
      have hkey' := actualPartRouteKeysR (hall other.1 (List.mem_of_getElem? hget'))
      rw [hkey']
      intro hmem'
      have hqComp : q.1.1 ∈ components execution.graph := by
        rw [← hparts]
        exact List.mem_map_of_mem (List.mem_of_getElem? hget)
      have hotherComp : other.1.1 ∈ components execution.graph := by
        rw [← hparts]
        exact List.mem_map_of_mem (List.mem_of_getElem? hget')
      have hpNodup : (execution.componentsAcc.parts.map (·.1)).Nodup := by
        rw [hparts]
        exact components_entries_nodup execution.graph
      obtain ⟨hc, hq⟩ := List.getElem?_eq_some_iff.mp hget
      obtain ⟨hj, hq'⟩ := List.getElem?_eq_some_iff.mp hget'
      have hdifferent : q.1.1 ≠ other.1.1 := by
        have hne := (List.pairwise_iff_getElem.mp hpNodup) c j
          (by simpa only [List.length_map] using hc)
          (by simpa only [List.length_map] using hj) hcj
        simpa only [List.getElem_map, hq, hq'] using hne
      rw [hkeys] at hkeyMem
      exact components_ownsDecl_disjoint hndGraph hqComp hotherComp hdifferent
        (partRouteKey_owned hkeyMem) (partRouteKey_owned hmem'))
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured key hkey
  rw [← execution.scene_eq, hread] at hscene
  exact congrArg Route.points (Option.some.inj (hroute.symm.trans hscene))

private theorem sceneBoxKeyR {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} {box : Box} (hbox : res.scene.boxes[key]? = some box) : key < inp.boxes.length := by
  have h := (List.getElem?_eq_some_iff.mp hbox).1
  rw [execution.boxes_eq_mapR] at h
  simpa only [List.length_map, List.length_zipIdx] using h

private theorem chosenPartBox_rect {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {j key : Nat} {rect : Rect} (hentry : (q.1.1.zip q.1.2.rects)[j]? = some (key, rect))
    {box : Box} (hbox : res.scene.boxes[key]? = some box) :
    box.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH (shiftRect q.2.x q.2.y rect)) := by
  have hk := sceneBoxKeyR execution hbox
  have hsize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_sizeR]
    exact hk
  have hread := actual_components_packed_rect_valueR (by rfl) execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hsize default
  rw [execution.boxes_eq_mapR] at hbox
  simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hk,
    Option.map_some, Nat.zero_add, hread] at hbox
  exact congrArg Box.rect (Option.some.inj hbox).symm

private theorem shelfDimsR {P : Params} {o : Options} {parts : List (List Nat × Part)}
    {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (parts.zip packed.boxes)[c]? = some q) :
    q.2.w = q.1.2.width ∧ q.2.h = q.1.2.height := by
  obtain ⟨hpart, hshelf⟩ := List.getElem?_zip_eq_some.mp hselected
  have hdim := congrArg (fun ds : List (Int × Int) => ds[c]?) (Pack.pack_dimensions hpacked)
  simpa only [Pack.dimensions, List.getElem?_map, hpart, hshelf, Option.map_some,
    Option.some.injEq, Prod.mk.injEq] using hdim

set_option maxHeartbeats 700000 in
theorem SceneExecutionR.chosenRoute_misses_other_part
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c c' : Nat} {q q' : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    (hother : (execution.componentsAcc.parts.zip packed.boxes)[c']? = some q')
    (hne : c ≠ c')
    {i routeKey : Nat} {pts : List Point}
    (hlocal : q.1.2.routes[i]? = some (routeKey, pts))
    {j boxKey : Nat} {rect : Rect}
    (hentry : (q'.1.1.zip q'.1.2.rects)[j]? = some (boxKey, rect))
    {route : Route} {box : Box}
    (hroute : res.scene.routes[routeKey]? = some route)
    (hbox : res.scene.boxes[boxKey]? = some box) : ¬ Polyline.hitsRect route.points box.rect := by
  have hbounds := exactComponentPlacementR_bounded_of_residual execution
    (R_partSizingRResidual_holds exactIds idSets)
  have hq := hbounds q.1 (List.mem_of_getElem? (zip_getElem?_left hselected))
  have hq' := hbounds q'.1 (List.mem_of_getElem? (zip_getElem?_left hother))
  have hqDims := shelfDimsR (P := execution.params) (o := o) hpacked hselected
  have hq'Dims := shelfDimsR (P := execution.params) (o := o) hpacked hother
  have hrect := hq'.2.2.1 rect (List.mem_of_getElem? (List.getElem?_zip_eq_some.mp hentry).2)
  have hcontained : q'.2.Contained (shiftRect q'.2.x q'.2.y rect) := by
    simp only [Rect.Contained, shiftRect, hq'Dims.1, hq'Dims.2]
    omega
  have hsep := pack_shelves_axisSeparatedX hpacked hne
    (List.getElem?_zip_eq_some.mp hselected).2 (List.getElem?_zip_eq_some.mp hother).2
  have hsepRect : RectAxisSeparated q.2 (shiftRect q'.2.x q'.2.y rect) := by
    simp only [RectAxisSeparated] at hsep ⊢
    simp only [Rect.Contained] at hcontained
    omega
  have hp : ∀ p ∈ pts.map (shiftPoint q.2.x q.2.y), PointIn q.2 p := by
    intro p hp
    obtain ⟨localPoint, hmem, rfl⟩ := List.mem_map.mp hp
    have hb := hq.2.2.2.2.1 (routeKey, pts) (List.mem_of_getElem? hlocal) localPoint hmem
    simp only [PointIn, shiftPoint, hqDims.1, hqDims.2]
    omega
  have hmiss := Polyline.not_hits_of_allMiss (allSegsMiss_of_pointIn_of_separated hsepRect _ hp)
  rw [execution.chosenPartRoute_points hpacked hselected hlocal hroute,
    chosenPartBox_rect execution hpacked hother hentry hbox]
  exact not_hitsRect_shift_orient o.direction execution.packedAcc.canvasH
    execution.params.canvasMargin execution.params.canvasMargin _ _ hmiss

set_option maxHeartbeats 1200000 in
theorem SceneExecutionR.c6_hit_same_part
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {routeKey boxKey : Nat} {route : Route} {box : Box}
    (hroute : res.scene.routes[routeKey]? = some route)
    (hbox : res.scene.boxes[boxKey]? = some box)
    (hhit : Polyline.hitsRect route.points box.rect) :
    ∃ (packed : Pack.State) (c : Nat) (q : (List Nat × Part) × Rect)
      (candidate : Nat) (cg : Graph) (run : Run) (loops : List (Nat × LoopPlacement))
      (area : Int) (spec : Option RegionSpec) (i : Nat) (edge : Edge)
      (j : Nat) (pts : List Point) (rect : Rect),
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q ∧
      componentRunR execution.params (exactDecls exactIds inp) spec inp
        (componentCandidateR spec execution.graph q.1.1 candidate)
        execution.measured (candidateOrder candidate) = .ok (cg, run) ∧
      componentLoops execution.params cg run execution.measured = .ok loops ∧
      q.1.2 = { placeComponentExact execution.params cg run 0 execution.measured loops
        with area := area } ∧
      cg.edges[i]? = some edge ∧ edge.decl = routeKey ∧
      q.1.2.routes[i]? = some (routeKey, pts) ∧
      (q.1.1.zip q.1.2.rects)[j]? = some (boxKey, rect) ∧
      Polyline.hitsRect pts rect := by
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length execution.params inp o execution.lines execution.packedAcc
      execution.measured
  have hk : routeKey < inp.routes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hroute).1
  obtain ⟨packed, c, q, candidate, run, loops, area, spec, cg, i, edge, hpacked, hselected,
    hrun, hloops, hpart, hedge, hdecl⟩ := rgeRouteSourceR execution hk
  have hlocal : ∃ pts, q.1.2.routes[i]? = some (routeKey, pts) := by
    rw [hpart]
    change ∃ pts, (placeComponentExact execution.params cg run 0
      execution.measured loops).routes[i]? = some (routeKey, pts)
    unfold placeComponentExact
    dsimp only
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some, hdecl]
    exact ⟨_, rfl⟩
  obtain ⟨pts, hlocal⟩ := hlocal
  obtain ⟨part, hpmem, ⟨key, rect⟩, hentry, hkey⟩ :=
    sceneExecutionR_parts_entryR execution (sceneBoxKeyR execution hbox)
  change key = boxKey at hkey
  subst key
  obtain ⟨c', hpartAt⟩ := List.mem_iff_getElem?.mp hpmem
  obtain ⟨j, hentryAt⟩ := List.mem_iff_getElem?.mp hentry
  have hshelfLen : packed.boxes.length = execution.componentsAcc.parts.length := by
    simpa only [List.length_map] using Pack.pack_count hpacked
  have hc' : c' < packed.boxes.length := by
    rw [hshelfLen]
    exact (List.getElem?_eq_some_iff.mp hpartAt).1
  let q' : (List Nat × Part) × Rect := (part, packed.boxes[c']'hc')
  have hother : (execution.componentsAcc.parts.zip packed.boxes)[c']? = some q' :=
    List.getElem?_zip_eq_some.mpr ⟨hpartAt, List.getElem?_eq_getElem hc'⟩
  have hsame : c = c' := by
    by_cases heq : c = c'
    · exact heq
    · exact False.elim ((execution.chosenRoute_misses_other_part hpacked hselected hother heq
        hlocal hentryAt hroute hbox) hhit)
  rw [← hsame] at hother
  have hq : q' = q := Option.some.inj (hother.symm.trans hselected)
  have hentryAt' : (q.1.1.zip q.1.2.rects)[j]? = some (boxKey, rect) := by
    rw [← hq]
    exact hentryAt
  refine ⟨packed, c, q, candidate, cg, run, loops, area, spec, i, edge, j, pts, rect,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl, hlocal, hentryAt', ?_⟩
  rw [execution.chosenPartRoute_points hpacked hselected hlocal hroute,
    chosenPartBox_rect execution hpacked hselected hentryAt' hbox,
    hitsRect_shift_orient, hitsRect_shift] at hhit
  exact hhit

end Elegant.Layered.PipelineImpl

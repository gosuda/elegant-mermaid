import Elegant.Layered.RegionC5TerminalRank
import Elegant.Layered.RegionCrossRunC6
import Elegant.Layered.RegionC5ActiveBoundary

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

def c5EndpointPoint (front : Bool) (points : List Point) : Option Point :=
  if front then points.head? else points.getLast?

theorem c5EndpointPoint_map (front : Bool) (f : Point → Point) (ps : List Point) :
    c5EndpointPoint front (ps.map f) = (c5EndpointPoint front ps).map f := by
  cases front <;> simp [c5EndpointPoint]

private theorem sourceBoxLookup {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {key : Nat} {source : ModelBox} (hs : inp.boxes[key]? = some source) :
    res.scene.layoutDump.box? source.id = some (Box.mk source.id source.role.id
      (shiftRect e.params.canvasMargin e.params.canvasMargin
        (orientRect o.direction e.packedAcc.canvasH (e.packedAcc.rects.getD key default)))
      source.parent source.exclusive) := by
  let box := Box.mk source.id source.role.id
    (shiftRect e.params.canvasMargin e.params.canvasMargin
      (orientRect o.direction e.packedAcc.canvasH (e.packedAcc.rects.getD key default)))
    source.parent source.exclusive
  have hb : res.scene.boxes[key]? = some box := by
    rw [e.boxes_eq_mapR]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hs, Option.map_some, Nat.zero_add]
    rfl
  have hid : (res.scene.boxes.map (·.id)) = inp.boxes.map (·.id) := by
    rw [e.boxes_eq_mapR, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  have hn : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hid]
    exact Model.boxIds_nodup hwf
  change res.scene.boxes.find? (fun b => b.id == source.id) = some box
  exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hn box (List.mem_of_getElem? hb)

theorem c5TransportEndpoint {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      e.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (e.componentsAcc.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (e.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i j routeKey boxKey : Nat} {route : Route} {source : ModelBox} {points : List Point}
    {rect : Rect} {p : Point} {front : Bool}
    (hout : res.scene.routes[routeKey]? = some route)
    (hpoints : q.1.2.routes[i]? = some (routeKey, points))
    (hrect : (q.1.1.zip q.1.2.rects)[j]? = some (boxKey, rect))
    (hs : inp.boxes[boxKey]? = some source)
    (hp : c5EndpointPoint front points = some p) (hboundary : Validator.onBoundary p rect) :
    ∃ result box, c5EndpointPoint front route.points = some result ∧
      res.scene.layoutDump.box? source.id = some box ∧ Validator.onBoundary result box.rect := by
  have hsize : boxKey < e.componentsAcc.rects.size := by
    rw [e.components_rects_sizeR]
    exact (List.getElem?_eq_some_iff.mp hs).1
  have hpackedRect := actual_components_packed_rect_valueR (by rfl) e.components_eq e.packed_eq
    packed hpack hselected hrect hsize default
  have hbox := sourceBoxLookup e hwf hs
  rw [hpackedRect] at hbox
  have hroute := e.chosenPartRoute_points hpack hselected hpoints hout
  let packedPoint := shiftPoint q.2.x q.2.y p
  let packedRect := shiftRect q.2.x q.2.y rect
  let margin := e.params.canvasMargin
  let result : Point := shiftPoint margin margin (orientPoint o.direction e.packedAcc.canvasH packedPoint)
  let box : Box := Box.mk source.id source.role.id
    (shiftRect margin margin (orientRect o.direction e.packedAcc.canvasH packedRect))
    source.parent source.exclusive
  refine ⟨result, box, ?_, hbox, ?_⟩
  · rw [hroute, c5EndpointPoint_map, c5EndpointPoint_map, hp] <;> rfl
  · exact (onBoundary_shift_orient o.direction e.packedAcc.canvasH margin margin
      packedPoint packedRect).mpr ((onBoundary_shift q.2.x q.2.y p rect).mpr hboundary)

theorem c5TransportPlacedFrameEntry {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {part : List Nat × Part} {area : Int}
    (hpart : part.2 = { placeComponentExact P cg run 0 labels loops with area := area })
    {j key : Nat} (hj : j < cg.nodes.length) (hkey : part.1[j]? = some key) :
    let b := placeBoundsX P cg run labels loops
    (part.1.zip part.2.rects)[j]? = some (key,
      shiftRect (0 - b.minX) (-b.minY) (frameRect P cg run j)) := by
  apply List.getElem?_zip_eq_some.mpr
  refine ⟨hkey, ?_⟩
  rw [hpart]
  change (placeComponentExact P cg run 0 labels loops).rects[j]? = _
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some]

theorem c5TransportCandidateNodes (spec : Option RegionSpec) (g : Graph) (comp : List Nat)
    (index : Nat) : (componentCandidateR spec g comp index).nodes =
      (componentCandidate g comp index).nodes := by
  cases spec with
  | none => rfl
  | some _ => rw [componentCandidate_nodes]; rfl

theorem c5TransportRunNodes {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {candidate cg : Graph} {labels : List MeasuredLabel}
    {order : OrderOptions} {run : Run}
    (hrun : componentRunR P exact spec inp candidate labels order = .ok (cg, run)) :
    cg.nodes = candidate.nodes := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, hr⟩
  · exact congrArg Graph.nodes he
  · exact rankEquivalentR_nodes_eq hr

theorem c5TransportCandidateDecls (spec : Option RegionSpec) (g : Graph) (comp : List Nat)
    (index : Nat) : (componentCandidateR spec g comp index).edges.map (·.decl) =
      (componentGraph g comp).edges.map (·.decl) := by
  cases spec with
  | none => exact componentCandidate_decls g comp index
  | some _ =>
    unfold componentCandidateR
    dsimp only
    let raw := componentGraph g comp
    let source := { raw with edges := raw.edges.map Edge.original }
    let flags := if index == 2 then groupGreedyFlags source
      else List.replicate source.edges.length false
    let orient := fun q : Edge × Nat => if flags.getD q.2 false then
      { q.1 with tail := q.1.head, head := q.1.tail, reversed := true } else q.1
    have hdecl : (fun e : Edge => e.decl) ∘ orient = (fun e : Edge => e.decl) ∘ Prod.fst := by
      funext q
      simp only [Function.comp_def, orient]
      split <;> rfl
    change ((source.edges.zipIdx.map orient).map (·.decl)) = raw.edges.map (·.decl)
    rw [List.map_map, hdecl, ← List.map_map, List.zipIdx_map_fst]
    simp only [source, List.map_map, Function.comp_def, Edge.original_decl]

theorem c5TransportGroupFrameSource {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {s : Option RegionSpec}
    {comp : List Nat} {index t : Nat} {cg : Graph} {run : Run} {top : Node}
    (hrun : componentRunR e.params (exactDecls exactIds inp) s inp
      (componentCandidateR s e.graph comp index) e.measured (candidateOrder index) = .ok (cg, run))
    (htop : cg.nodes[t]? = some top) (htag : top.border = -2) :
    comp[t]? = some top.decl ∧ ∃ box, inp.boxes[top.decl]? = some box := by
  rw [c5TransportRunNodes hrun, c5TransportCandidateNodes] at htop
  obtain ⟨key, hkey, hn⟩ := componentCandidate_nonplain_source htop (by omega)
  have hk : key < e.graph0.nodes.length := by
    rw [← exactGraph_length e.graph_eq]
    exact (List.getElem?_eq_some_iff.mp hn).1
  obtain ⟨n, hget, hb, _, hd⟩ := exactGraph_node_key e.graph_eq (List.getElem?_eq_getElem hk)
  have he := Option.some.inj (hget.symm.trans hn)
  have hborder : (e.graph0.nodes[key]'hk).border = -2 := by rw [← hb, he]; exact htag
  have hd0 := (measuredGraph_group_origin e.graph0_eq (List.getElem?_eq_getElem hk) hborder).1
  rw [he, hd0] at hd
  exact ⟨by rw [hd]; exact hkey,
    by obtain ⟨box, hs, _⟩ := X_cg_group_box e.graph0_eq e.graph_eq htop htag; exact ⟨box, hs⟩⟩

private theorem semanticTerminalBox {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {s : Option RegionSpec}
    {comp : List Nat} {index v t : Nat} {cg : Graph} {run : Run}
    (hrun : componentRunR e.params (exactDecls exactIds inp) s inp
      (componentCandidateR s e.graph comp index) e.measured (candidateOrder index) = .ok (cg, run))
    (ht : SelectedC5SemanticGroupTerminal cg v t) :
    ∃ (key : Nat) (source : ModelBox), comp[t]? = some key ∧ inp.boxes[key]? = some source := by
  obtain ⟨_, top, _, ht, htag, _, _⟩ := ht
  obtain ⟨hkey, source, hs⟩ := c5TransportGroupFrameSource e hrun ht htag
  exact ⟨top.decl, source, hkey, hs⟩

/-- The selected rewritten non-loop route reaches the actual dump rectangle of each
    semantic group terminal, in the order picked by the returned graph's reversal flag. -/
theorem regionC5ChosenActiveEmittedGroupTerminals
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      e.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (e.componentsAcc.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (e.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {rm : ComponentRegions}
    (hregion : newComponentRegions (selectedC5TerminalSpec idSets e.params o e.lines)
      e.params inp (componentGraph e.graph q.1.1) = .ok (some rm)) :
    ∃ s index chosen cg run loops area,
      selectedC5TerminalSpec idSets e.params o e.lines = some s ∧
      Portfolio.portfolio o.thoroughness (componentTrialR e.params exactIds (some s)
        inp o e.graph q.1.1 e.measured) = .ok chosen ∧ chosen.value = (cg, run) ∧
      componentRunR e.params (exactDecls exactIds inp) (some s) inp
        (componentCandidateR (some s) e.graph q.1.1 index) e.measured
        (candidateOrder index) = .ok (cg, run) ∧
      componentLoops e.params cg run e.measured = .ok loops ∧
      q.1.2 = { placeComponentExact e.params cg run 0 e.measured loops with area := area } ∧
      ∀ {i first last : Nat} {edge : Edge}, cg.edges[i]? = some edge → edge.tail ≠ edge.head →
        (RouteImpl.edgesOf run.proper i).head? = some first →
        (RouteImpl.edgesOf run.proper i).getLast? = some last →
        ∃ out, res.scene.routes[edge.decl]? = some out ∧
          (∀ t, SelectedC5SemanticGroupTerminal cg (RouteImpl.edgeAt run.proper first).tail t →
            ∃ key source p box, q.1.1[t]? = some key ∧ inp.boxes[key]? = some source ∧
              c5EndpointPoint (!edge.reversed) out.points = some p ∧
              res.scene.layoutDump.box? source.id = some box ∧ Validator.onBoundary p box.rect) ∧
          (∀ t, SelectedC5SemanticGroupTerminal cg (RouteImpl.edgeAt run.proper last).head t →
            ∃ key source p box, q.1.1[t]? = some key ∧ inp.boxes[key]? = some source ∧
              c5EndpointPoint edge.reversed out.points = some p ∧
              res.scene.layoutDump.box? source.id = some box ∧ Validator.onBoundary p box.rect) := by
  obtain ⟨s, index, chosen, cg, run, loops, area, hs, _, hport, hvalue, hrun, _, hloops, hplace, ha⟩ :=
    regionC5ChosenActiveRouteGroupTerminals e hwf hfp
      (List.mem_of_getElem? (zip_getElem?_left hselected)) hregion
  refine ⟨s, index, chosen, cg, run, loops, area, hs, hport, hvalue, hrun, hloops, hplace, ?_⟩
  intro i first last edge hedge hne hf hl
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  have hrev : (cg.edges.map (·.reversed)).getD i false = edge.reversed := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hedge, Option.map_some, Option.getD_some]
  have hdecls := (componentRunR_edges_declsR hrun).trans
    (c5TransportCandidateDecls (some s) e.graph q.1.1 index)
  have hn : (cg.edges.map Edge.decl).Nodup := by
    rw [hdecls]
    exact componentGraph_decls_nodup _ _ (exactGraph_decls_nodup e.graph0_eq e.graph_eq)
  have hloop' := componentLoops_excludes_ordinary_decl hloops hn hedge hne
  have hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl := by
    simpa only [he] using hloop'
  have hmem : edge.decl ∈ (cg.edges.map (·.decl)) := List.mem_map_of_mem (List.mem_of_getElem? hedge)
  rw [hdecls] at hmem
  obtain ⟨localEdge, hlocal, hsame⟩ := List.mem_map.mp hmem
  change localEdge ∈ (e.graph.edges.filter fun ed => q.1.1.contains ed.tail).map
    (fun ed => { ed with tail := q.1.1.idxOf ed.tail, head := q.1.1.idxOf ed.head }) at hlocal
  obtain ⟨globalEdge, hglobal, hlocalEq⟩ := List.mem_map.mp hlocal
  have hglobalDecl : globalEdge.decl = edge.decl := (congrArg Edge.decl hlocalEq).trans hsame
  have hmem : edge.decl ∈ e.graph.edges.map (·.decl) :=
    List.mem_map.mpr ⟨globalEdge, (List.mem_filter.mp hglobal).1, hglobalDecl⟩
  rw [exactGraph_decl_rangeX e.graph0_eq e.graph_eq, ← List.range_eq_range'] at hmem
  have hbound : edge.decl < inp.routes.length := List.mem_range.mp hmem
  have hout := sceneOf_routes_getElem? e.params inp o e.lines e.packedAcc e.measured edge.decl hbound
  rw [← e.scene_eq] at hout
  obtain ⟨rt, hrt, htail, hhead⟩ := ha hi hf hl
  rw [hrev] at htail hhead
  let b := placeBoundsX e.params cg run e.measured loops
  have hp := rcbPlaceEntryR hrun 0 loops i hi hloop
  rw [(List.getElem?_eq_some_iff.mp hrt).2, he] at hp
  have hlocalPoints : q.1.2.routes[i]? = some (edge.decl,
      rt.points.map (shiftPoint (0 - b.minX) (-b.minY))) := by
    rw [hplace]
    exact hp
  refine ⟨_, hout, ?_, ?_⟩
  · intro t ht
    obtain ⟨p, hp, hb⟩ := htail t ht
    obtain ⟨key, source, hk, hsource⟩ := semanticTerminalBox e hrun ht
    have hj : t < cg.nodes.length := by
      obtain ⟨_, _, _, htop, _, _, _⟩ := ht
      exact (List.getElem?_eq_some_iff.mp htop).1
    obtain ⟨p', box, hstart, hbox, hboundary⟩ := c5TransportEndpoint e hwf hpack hselected hout
      hlocalPoints (c5TransportPlacedFrameEntry hplace hj hk) hsource
      (front := !edge.reversed) (p := shiftPoint (0 - b.minX) (-b.minY) p)
      (by
        rw [c5EndpointPoint_map]
        by_cases hr : edge.reversed = true
        · rw [ite_eq_left hr] at hp
          rw [hr]
          change Option.map _ rt.points.getLast? = _
          rw [hp] <;> rfl
        · rw [ite_eq_right hr] at hp
          rw [Bool.eq_false_iff.mpr hr]
          change Option.map _ rt.points.head? = _
          rw [hp] <;> rfl)
      ((onBoundary_shift _ _ _ _).mpr hb)
    exact ⟨key, source, p', box, hk, hsource, hstart, hbox, hboundary⟩
  · intro t ht
    obtain ⟨p, hp, hb⟩ := hhead t ht
    obtain ⟨key, source, hk, hsource⟩ := semanticTerminalBox e hrun ht
    have hj : t < cg.nodes.length := by
      obtain ⟨_, _, _, htop, _, _, _⟩ := ht
      exact (List.getElem?_eq_some_iff.mp htop).1
    obtain ⟨p', box, hfinish, hbox, hboundary⟩ := c5TransportEndpoint e hwf hpack hselected hout
      hlocalPoints (c5TransportPlacedFrameEntry hplace hj hk) hsource
      (front := edge.reversed) (p := shiftPoint (0 - b.minX) (-b.minY) p)
      (by
        rw [c5EndpointPoint_map]
        by_cases hr : edge.reversed = true
        · rw [ite_eq_left hr] at hp
          rw [hr]
          change Option.map _ rt.points.head? = _
          rw [hp] <;> rfl
        · rw [ite_eq_right hr] at hp
          rw [Bool.eq_false_iff.mpr hr]
          change Option.map _ rt.points.getLast? = _
          rw [hp] <;> rfl)
      ((onBoundary_shift _ _ _ _).mpr hb)
    exact ⟨key, source, p', box, hk, hsource, hfinish, hbox, hboundary⟩

end Elegant.Layered.PipelineImpl

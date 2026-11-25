import Elegant.Layered.RegionFlatC6Selected
import Elegant.Layered.RegionC5NativeEndpoints
import Elegant.Layered.ExactFlatC6ChainClosedProof

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Elegant.Layered.PipelineImpl.RegionOrdinaryC6

open RegionImpl RouteImpl

structure SelectedOrdinaryPair {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) (i j : Nat) (pts : List Point) (rect : Rect) where
  native : EdgeRoute
  edge : Edge
  node : Node
  first : Nat
  last : Nat
  nativeAt : s.run.routes[i]? = some native
  original : native.original = i
  edgeAt : s.cg.edges[i]? = some edge
  nonloop : edge.tail ≠ edge.head
  nodeAt : s.cg.nodes[j]? = some node
  plain : node.border = 0
  bound : j < s.run.proper.nodes.length
  real : IsReal s.run.proper j
  firstAt : (edgesOf s.run.proper native.original).head? = some first
  lastAt : (edgesOf s.run.proper native.original).getLast? = some last
  foreignFirst : j ≠ (RouteImpl.edgeAt s.run.proper first).tail
  foreignLast : j ≠ (RouteImpl.edgeAt s.run.proper last).head
  hit : Polyline.hitsRect pts rect ↔
    Polyline.hitsRect native.points (boxRect s.run.proper s.run.xs s.run.ys j)

private theorem sceneBoxSource {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} {box : Box} (hbox : res.scene.boxes[key]? = some box) :
    ∃ b, inp.boxes[key]? = some b ∧ box.id = b.id ∧ box.exclusive = b.exclusive := by
  have hk := (List.getElem?_eq_some_iff.mp hbox).1
  rw [e.boxes_eq_mapR] at hk
  have hkey : key < inp.boxes.length := by
    simpa only [List.length_map, List.length_zipIdx] using hk
  rw [e.boxes_eq_mapR] at hbox
  simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hkey,
    Option.map_some, Nat.zero_add] at hbox
  have heq := (Option.some.inj hbox).symm
  exact ⟨inp.boxes[key], List.getElem?_eq_getElem hkey, congrArg Box.id heq,
    congrArg Box.exclusive heq⟩

private theorem endpoint_eq_or_past (boxes : List ModelBox) (source : Bool) (i j : Nat) :
    Compound.endpoint boxes source i j = i ∨
      boxes.length ≤ Compound.endpoint boxes source i j := by
  generalize h : Compound.endpoint boxes source i j = k
  unfold Compound.endpoint at h
  split at h
  all_goals
    first
    | exact Or.inl h.symm
    | split at h
      · exact Or.inl h.symm
      · dsimp only at h
        split at h
        · exact Or.inl h.symm
        · rw [← h]
          exact Or.inr (Nat.le_add_right _ _)

private theorem foreignAliasKeys {inp : Input} {raw : Edge} {key : Nat}
    (hbound : key < inp.boxes.length) (ht : key ≠ raw.tail) (hh : key ≠ raw.head) :
    key ≠ (aliasEdgeOf inp raw).tail ∧ key ≠ (aliasEdgeOf inp raw).head := by
  have hlen : (preparedBoxes inp).length = inp.boxes.length := List.length_map ..
  change key ≠ Compound.endpoint (preparedBoxes inp) true raw.tail raw.head ∧
    key ≠ Compound.endpoint (preparedBoxes inp) false raw.head raw.tail
  constructor
  · intro he
    rcases endpoint_eq_or_past (preparedBoxes inp) true raw.tail raw.head with h | h
    · exact ht (he.trans h)
    · rw [hlen, ← he] at h
      omega
  · intro he
    rcases endpoint_eq_or_past (preparedBoxes inp) false raw.head raw.tail with h | h
    · exact hh (he.trans h)
    · rw [hlen, ← he] at h
      omega

private theorem foreignRawKeys {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    {routeKey boxKey : Nat} {route : Route} {box : Box} {source : ModelRoute} {raw : Edge}
    {b : ModelBox} (hb : inp.boxes[boxKey]? = some b) (hboxId : box.id = b.id)
    (hroute : res.scene.routes[routeKey]? = some route)
    (hscope : box.id ∉ LayoutDump.routeScope res.scene.layoutDump route)
    (hsource : inp.routes[routeKey]? = some source)
    (hraw : edgeOf inp source routeKey = .ok raw) :
    boxKey ≠ raw.tail ∧ boxKey ≠ raw.head := by
  obtain ⟨hk, hmodel⟩ := List.getElem?_eq_some_iff.mp hsource
  have hr := sceneOf_routes_getElem? e.params inp o e.lines e.packedAcc e.measured routeKey hk
  rw [← e.scene_eq] at hr
  have he := Option.some.inj (hroute.symm.trans hr)
  have hfrom : route.fromId = source.fromId :=
    (congrArg Route.fromId he).trans (congrArg ModelRoute.fromId hmodel)
  have hto : route.toId = source.toId :=
    (congrArg Route.toId he).trans (congrArg ModelRoute.toId hmodel)
  obtain ⟨_, _, fromBox, toBox, hfromBox, hfromId, htoBox, htoId⟩ := edgeOf_semantic_endpoints hraw
  constructor
  · intro heq
    rw [heq] at hb
    have h := hboxId.trans ((congrArg ModelBox.id (Option.some.inj (hb.symm.trans hfromBox))).trans
      (hfromId.trans hfrom.symm))
    exact hscope (by simp [LayoutDump.routeScope, h])
  · intro heq
    rw [heq] at hb
    have h := hboxId.trans ((congrArg ModelBox.id (Option.some.inj (hb.symm.trans htoBox))).trans
      (htoId.trans hto.symm))
    exact hscope (by simp [LayoutDump.routeScope, h])

private theorem selectedEdgeAt {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) {i routeKey : Nat} {pts : List Point}
    (hlocal : part.2.routes[i]? = some (routeKey, pts)) :
    ∃ edge, s.cg.edges[i]? = some edge ∧ edge.decl = routeKey := by
  rw [s.hPlaced] at hlocal
  change (placeComponentExact e.params s.cg s.run 0 e.measured s.loops).routes[i]? = _ at hlocal
  unfold placeComponentExact at hlocal
  dsimp only at hlocal
  cases hedge : s.cg.edges[i]? with
  | none =>
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_none, reduceCtorEq] at hlocal
  | some edge =>
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at hlocal
    exact ⟨edge, by first | exact hedge | rfl, hlocal.1⟩

private theorem foreignChainEnds {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part)
    {i routeKey j boxKey : Nat} {edge : Edge} {route : Route} {box : Box} {b : ModelBox}
    (hedge : s.cg.edges[i]? = some edge) (hdecl : edge.decl = routeKey)
    (hroute : res.scene.routes[routeKey]? = some route)
    (hscope : box.id ∉ LayoutDump.routeScope res.scene.layoutDump route)
    (hkey : part.1[j]? = some boxKey) (hb : inp.boxes[boxKey]? = some b)
    (hboxId : box.id = b.id) : j ≠ edge.tail ∧ j ≠ edge.head := by
  obtain ⟨source, raw, hr, hraw, htail, hhead, _, _⟩ := c5NativeRouteOrigin e s.hComp s.hRun hedge
  rw [hdecl] at hr hraw
  obtain ⟨ht, hh⟩ := foreignRawKeys e hb hboxId hroute hscope hr hraw
  obtain ⟨hat, hah⟩ := foreignAliasKeys (List.getElem?_eq_some_iff.mp hb).1 ht hh
  have ha : j ≠ edge.original.tail := by
    intro he
    rw [he] at hkey
    exact hat (Option.some.inj (hkey.symm.trans htail))
  have hz : j ≠ edge.original.head := by
    intro he
    rw [he] at hkey
    exact hah (Option.some.inj (hkey.symm.trans hhead))
  cases rev : edge.reversed with
  | false => simpa [Edge.original, rev] using And.intro ha hz
  | true => simpa [Edge.original, rev] using And.intro hz ha

/-- The validator's two indices select an ordinary native route and a real, plain victim in
one executed component. Translation by its placement origin preserves interior hits. -/
theorem selectedOrdinaryPair {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) (hwf : WellFormed (inputModel inp o))
    {i routeKey j boxKey : Nat} {pts : List Point} {rect : Rect}
    (pair : R6_SelectedPartPairR e s i routeKey j boxKey pts rect)
    (hfind : s.loops.find? (fun l => l.1 == routeKey) = none) :
    Nonempty (SelectedOrdinaryPair s i j pts rect) := by
  obtain ⟨route, box, hroute, hbox, hex, hscope⟩ := pair.scenePair
  obtain ⟨edge, hedge, hdecl⟩ := selectedEdgeAt s pair.routeAt
  obtain ⟨hkey, hrect⟩ := List.getElem?_zip_eq_some.mp pair.boxAt
  obtain ⟨b, hb, hboxId, hbEx⟩ := sceneBoxSource e hbox
  have hnonGroup := wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hb)
    (hbEx.symm.trans hex)
  have hl : boxKey < e.lines.length := by
    rw [boxLines_length e.lines_eq]
    exact (List.getElem?_eq_some_iff.mp hb).1
  obtain ⟨node₀, hn₀, hb₀⟩ := measuredGraph_exclusive_node_border_zero e.checked e.graph0_eq
    (List.getElem?_eq_getElem hl) hb hnonGroup
  obtain ⟨node, hn, hborder, _, _⟩ := exactGraph_node_key e.graph_eq hn₀
  have hnodeCandidate := component_node_lookupR (spec := s.used) (cand := s.candidate) hkey hn
  have hnode : s.cg.nodes[j]? = some node := by
    rw [c5TransportRunNodes s.hRun]
    exact hnodeCandidate
  have hzero : node.border = 0 := hborder.trans hb₀
  have hj := (List.getElem?_eq_some_iff.mp hnode).1
  have hv := componentRunR_original_nodes_covered s.hRun j hj
  have hplain : (s.cg.nodes.getD j default).border ≠ -2 := by
    rw [List.getD_eq_getElem?_getD, hnode, Option.getD_some, hzero]
    decide
  have hnonloop : edge.tail ≠ edge.head := by
    intro hself
    obtain ⟨_, _, hnorm, _, _⟩ := rcbNormalizedSourceR s.hRun
    have hbounds := RankImpl.wellformed_spec (normalize_node_rank_alignment hnorm).2
      edge (List.mem_of_getElem? hedge)
    obtain ⟨placement, hplacement⟩ := componentLoops_entry_of_self_edge s.hLoops
      (List.mem_of_getElem? hedge) hbounds.1 hself
    exact (List.find?_eq_none.mp hfind (edge.decl, placement) hplacement) (by simp [hdecl])
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have hic : i < s.run.proper.chains.length := by rwa [rcbProperChainsR s.hRun]
  obtain ⟨native, hnative, horiginal, _⟩ := componentRunR_route_of_indexR s.hRun hic
  obtain ⟨first, last, hf, hl, htail, hhead⟩ := c5ChainEnds% s.hRun hedge hnonloop
  obtain ⟨hforeignTail, hforeignHead⟩ := foreignChainEnds s hedge hdecl hroute hscope hkey hb hboxId
  have hnoLoop : ∀ l ∈ s.loops, l.1 ≠ (s.cg.edges[i]).decl := by
    have he := (List.getElem?_eq_some_iff.mp hedge).2
    intro l hl heq
    have hlkey : l.1 = routeKey := heq.trans ((congrArg Edge.decl he).trans hdecl)
    exact List.find?_eq_none.mp hfind l hl (by simp [hlkey])
  let bounds := placeBoundsX e.params s.cg s.run e.measured s.loops
  have hpts : pts = native.points.map (shiftPoint (0 - bounds.minX) (-bounds.minY)) := by
    have hpl := rcbPlaceEntryR s.hRun 0 s.loops i hi hnoLoop
    have hn := (List.getElem?_eq_some_iff.mp hnative).2
    have he := (List.getElem?_eq_some_iff.mp hedge).2
    have hlocal := pair.routeAt
    rw [s.hPlaced] at hlocal
    change (placeComponentExact e.params s.cg s.run 0 e.measured s.loops).routes[i]? =
      some (routeKey, pts) at hlocal
    rw [hn, he, hdecl] at hpl
    exact congrArg Prod.snd (Option.some.inj (hlocal.symm.trans hpl))
  have hrect' : rect = shiftRect (0 - bounds.minX) (-bounds.minY)
      (frameRect e.params s.cg s.run j) := by
    have hpl : (placeComponentExact e.params s.cg s.run 0 e.measured s.loops).rects[j]? =
        some (shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect e.params s.cg s.run j)) := by
      dsimp only [bounds]
      unfold placeComponentExact placeBoundsX
      simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some]
    rw [s.hPlaced] at hrect
    change (placeComponentExact e.params s.cg s.run 0 e.measured s.loops).rects[j]? =
      some rect at hrect
    exact Option.some.inj (hrect.symm.trans hpl)
  refine ⟨⟨native, edge, node, first, last, hnative, horiginal, hedge, hnonloop, hnode, hzero, hv,
    rgeIsRealR s.hRun hnodeCandidate, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rwa [horiginal]
  · rwa [horiginal]
  · rwa [htail]
  · rwa [hhead]
  · rw [hpts, hrect', hitsRect_shift, plain_frame_eq_boxRect e.params s.cg s.run j hv hplain]

end Elegant.Layered.PipelineImpl.RegionOrdinaryC6

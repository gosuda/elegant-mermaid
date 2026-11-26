import Elegant.Layered.ExactBottomBracketVacancyProof
import Elegant.Layered.ExactFlatForeignLoopProof
import Elegant.Layered.ExactStraightenFacts
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

/-- A straightened corridor misses a packed rectangle once the obstacle check
agrees: endpoint touches miss, otherwise the boolean hit test is false. -/
private theorem Xc_corridor_miss_of_check {ptsCorr : List Point} {rectF tailRect headRect : Rect}
    {col top bottom : Int}
    (hshape : top = tailRect.y + tailRect.h ∧ bottom = headRect.y)
    (hlt : top < bottom)
    (hptsEq : ptsCorr = [⟨col, top⟩, ⟨col, bottom⟩])
    (hcond : (rectF == tailRect || rectF == headRect || false ||
      !Polyline.hitsRectB [⟨col, top⟩, ⟨col, bottom⟩] rectF) = true) :
    ¬ Polyline.hitsRect ptsCorr rectF := by
  cases hEqT : rectF == tailRect with
  | true =>
    have hRectEqT : rectF = tailRect := beq_iff_eq.mp hEqT
    have hmissTail := ExactStraighten.corridor_misses_tail (c := col) hshape.1 hlt
    have hgoalT : ¬ Polyline.hitsRect ptsCorr rectF := by
      rw [hptsEq, hRectEqT]
      exact hmissTail
    exact hgoalT
  | false =>
    cases hEqH : rectF == headRect with
    | true =>
      have hRectEqH : rectF = headRect := beq_iff_eq.mp hEqH
      have hmissHead := ExactStraighten.corridor_misses_head (c := col) hshape.2 hlt
      have hgoalH : ¬ Polyline.hitsRect ptsCorr rectF := by
        rw [hptsEq, hRectEqH]
        exact hmissHead
      exact hgoalH
    | false =>
      cases hB : Polyline.hitsRectB [⟨col, top⟩, ⟨col, bottom⟩] rectF with
      | true =>
        rw [hEqT, hEqH, hB] at hcond
        cases hcond
      | false =>
        have hBpts : Polyline.hitsRectB ptsCorr rectF = false := by
          rw [hptsEq]
          exact hB
        exact (Polyline.hitsRectB_eq_false_iff _ _).mp hBpts

/-- A plain node's label survives exact coordinate construction. -/
private theorem Xc_coordinateGraphX_plain_label {P : Params} {exact : List Nat} {p : Proper}
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.label = nd.label ∧ out.edge = nd.edge ∧ out.node.border = 0 := by
  obtain ⟨sized, hs, hlabS, heS, hb'⟩ :
      ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
        sized.label = nd.label ∧ sized.edge = nd.edge ∧ sized.node.border = 0 := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, rfl, rfl, hb⟩
    · refine ⟨_, rfl, rfl, rfl, hb⟩
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have hlabT : (titleF sized).label = sized.label := by
    unfold titleF
    split <;> rfl
  have hedgeT : (titleF sized).edge = sized.edge := by
    unfold titleF
    split <;> rfl
  have hbT : (titleF sized).node.border = 0 := by
    have hkeep := (titleF_keys sized).2.1
    rw [hkeep]
    exact hb'
  have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? = some (titleF sized) := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp only [List.getElem?_map, hs, Option.map_some]
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? =
      some (titleF sized) := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hcneg : ¬((titleF sized).node.border == -2 ||
      (titleF sized).node.border == 2) = true := by
    rw [hbT]
    decide
  have hclT : clearF (titleF sized) = titleF sized := by
    unfold clearF
    exact ite_eq_right hcneg
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
      some (titleF sized) := by
    rw [clearProxyExtents_nodes]
    simp only [List.getElem?_map, hplaced, Option.map_some, hclT]
  have hlabX : (titleF sized).label = nd.label := hlabT.trans hlabS
  have hedgeX : (titleF sized).edge = nd.edge := hedgeT.trans heS
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split
  · exact ⟨_, rfl, hlabX, hedgeX, hbT⟩
  · exact ⟨_, rfl, hlabX, hedgeX, hbT⟩

/-- Exact proper nodes transfer unchanged for non-proxy borders. -/
private theorem Xc_plain_node_dims {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode}
    (hnode : run.coordinateProper.nodes[i]? = some nd)
    (hborder : nd.node.border = 0) :
    run.proper.nodes[i]? = some nd := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hprojected := proxyWidths_plain_node hproxy hnode hborder
  rw [← hdrop]
  exact hprojected

/-- Original exact component nodes keep their label flag through the run. -/
private theorem Xc_original_node_facts {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {gn : Node} (hcand : cg.nodes[v]? = some gn) (hbord : gn.border = 0) :
    ∃ out, run.proper.nodes[v]? = some out ∧ out.label = false ∧ out.node.border = 0 := by
  obtain ⟨ranks, p0, labeled, _, hn, hl, hcoord, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have hnorm : p0.nodes[v]? = some (⟨gn, false, none, false⟩ : ProperNode) :=
    normalize_node_record hn hcand
  have hlab : labeled.nodes[v]? = some (⟨gn, false, none, false⟩ : ProperNode) :=
    addLabelNodes_untouched_node hl hnorm rfl
  obtain ⟨out, hout, hlabO, _, hbordO⟩ :=
    Xc_coordinateGraphX_plain_label hlab hbord
  rw [hcoord] at hout
  have houtP := Xc_plain_node_dims h hout hbordO
  have hlabF : out.label = false := hlabO
  exact ⟨out, houtP, hlabF, hbordO⟩

/-- A real exact component node with a plain candidate box is a real straightening node. -/
private theorem Xc_installed_component_node_real {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {gn : Node} (hcand : cg.nodes[v]? = some gn) (hbord : gn.border = 0)
    (hreal : RouteImpl.IsReal run.proper v) :
    straightRealNode run.proper v := by
  obtain ⟨out, houtP, hlabF, hbordO⟩ := Xc_original_node_facts hrun hcand hbord
  have hdum : out.dummy = false := hreal out houtP
  unfold straightRealNode
  simp only [houtP, hdum, hlabF, hbordO, Bool.not_false, beq_self_eq_true, Bool.true_and]

set_option maxHeartbeats 2500000 in
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
      execution.straightAcc execution.measured, ← execution.scene_eq]
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
    execution.straightAcc execution.measured edge.decl hmodelAt'.1
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
  obtain ⟨source, hsource, hsourceId, _, _, hframeEq⟩ := sceneBox_source_rectX execution hframeAt
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
    have hsuff : res.scene.routes[edge.decl]? =
        some (Route.mk model.id model.fromId model.toId model.orthogonal
          (native.points.map (routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY))) →
        ¬ Polyline.hitsRect route.points frame.rect := by
      intro hscene0
      rw [Option.some.inj (hrouteAt.symm.trans hscene0), Option.some.inj (hframeLookup.symm.trans hbox)]
      exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
        execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
    rcases hscene with hscene | hcorr
    · exact hsuff hscene
    · obtain ⟨ptsCorr, hcor, hrouteC⟩ := hcorr
      obtain ⟨_, _, _, _, hptsCorr⟩ := hcor
      have hgetD : execution.straightAcc.routes.getD edge.decl [] = ptsCorr :=
        ExactStraighten.straight_points_of_scene execution hrouteC
      have hptsNe : ptsCorr ≠ [] := by
        rw [hptsCorr]
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
      have hnormSrc : ∀ {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
          {orderOptions : OrderOptions}, componentRunX execution.params exact cg labels
            orderOptions = .ok run →
          ∃ ranks normalized, normalize cg ranks = .ok normalized ∧
            run.proper.edges = normalized.edges ∧ run.proper.chains = normalized.chains :=
        fun hrun => X_componentRun_normalized_source hrun
      rcases ExactStraighten.route_cases_clear execution hnormSrc hpts with hpackedPts | hinstW
      · have hsize : edge.decl < execution.componentsAcc.routes.size := by
          have hltP : edge.decl < execution.packedAcc.routes.size :=
            (Array.getElem?_eq_some_iff.mp hpackedPts).1
          rwa [Elegant.Layered.packAcc_routes_size execution.packed_eq] at hltP
        have hpackedRoute := ExactStraighten.actual_components_packAcc_routes_getD (by rfl)
          execution.components_eq
          (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
          packed execution.packed_eq hpacked c q hselected hIndex _ _ [] hrouteLocal hpartNodup hsize
        have hgd : execution.packedAcc.routes.getD edge.decl [] = ptsCorr := by
          rw [Array.getD_eq_getD_getElem?, hpackedPts, Option.getD_some]
        have hPlaced : (native.points.map (shiftPoint (0 - bounds.minX) (-bounds.minY))).map
            (shiftPoint q.2.x q.2.y) = ptsCorr :=
          hpackedRoute.symm.trans hgd
        have hneg : -bounds.minY = 0 - bounds.minY := by omega
        have hEq : (ptsCorr.map fun p => shiftPoint execution.params.canvasMargin
            execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH p)) =
            (native.points.map (routePointTransport execution.params.canvasMargin o.direction
              execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY)) := by
          rw [← hPlaced, hneg, routePointTransport_eq]
        have hScenePacked : res.scene.routes[edge.decl]? =
            some (Route.mk model.id model.fromId model.toId model.orthogonal
              (native.points.map (routePointTransport execution.params.canvasMargin o.direction
                execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY))) := by
          rw [hEq] at hrouteC
          exact hrouteC
        exact hsuff hScenePacked
      · obtain ⟨qW, ctx0W, oxW, oyW, iW, eW, routingW, spanW, hmemW, hctxW, hoffW,
          heW, hdeclW, hspanW, hptsW, hclrW⟩ := hinstW
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
        have hltW : spanW.top < spanW.bottom := straightSpanOf_top_lt hspanW
        have hptsEqW : ptsCorr = [⟨spanW.column, spanW.top⟩, ⟨spanW.column, spanW.bottom⟩] :=
          hptsW.trans rfl
        have hsizeR : key < execution.packedAcc.rects.size := by
          have h1 : key < inp.boxes.length := hkeyLen
          have h2 : execution.packedAcc.rects.size = execution.componentsAcc.rects.size :=
            installed_packAcc_rects_size execution.packed_eq
          have h3 : execution.componentsAcc.rects.size = inp.boxes.length :=
            execution.components_rects_size
          omega
        have hlook : execution.packedAcc.rects[key]? =
            some (execution.packedAcc.rects.getD key default) := by
          simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsizeR,
            Option.getD_some]
        by_cases hrole : source.role = BoxRole.node
        · have hflag : decide (source.role == BoxRole.node) = true := by
            have hb : (source.role == BoxRole.node) = true := by
              rw [hrole]
              exact beq_self_eq_true _
            rw [decide_eq_true_eq]
            exact hb
          have hmemG := ExactStraighten.installed_global_mem hlook hsource
          rw [hflag] at hmemG
          have hcond := List.all_eq_true.mp hclrW _ (List.mem_append.mpr (Or.inl hmemG))
          have hcondBeta : (execution.packedAcc.rects.getD key default == spanW.tailRect ||
              execution.packedAcc.rects.getD key default == spanW.headRect || false ||
              !Polyline.hitsRectB [⟨spanW.column, spanW.top⟩, ⟨spanW.column, spanW.bottom⟩]
                (execution.packedAcc.rects.getD key default)) = true := hcond
          have hmissC : ¬ Polyline.hitsRect ptsCorr
              (execution.packedAcc.rects.getD key default) :=
            Xc_corridor_miss_of_check hshapeW hltW hptsEqW hcondBeta
          have hrouteEqC : route.points = ptsCorr.map fun p => shiftPoint
              execution.params.canvasMargin execution.params.canvasMargin
              (orientPoint o.direction execution.packedAcc.canvasH p) :=
            congrArg Route.points (Option.some.inj (hrouteAt.symm.trans hrouteC))
          rw [hrouteEqC, hframeEq]
          exact not_hitsRect_shift_orient o.direction execution.packedAcc.canvasH
            execution.params.canvasMargin execution.params.canvasMargin _ _ hmissC
        · have hneW : eW.tail ≠ eW.head := by
            obtain ⟨eW', heW', heligW, _, _⟩ := ExactStraighten.straightSpanOf_inv hspanW
            have heqW : eW' = eW := Option.some.inj (heW'.symm.trans heW)
            rw [heqW] at heligW
            unfold straightEdgeEligible at heligW
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at heligW
            obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hNe⟩, _⟩, _⟩ := heligW
            intro hcon
            rw [hcon] at hNe
            simp at hNe
          have hinstW' : Installed execution.packedAcc edge.decl ptsCorr :=
            ⟨qW, ctx0W, oxW, oyW, iW, eW, spanW, hmemW, hctxW, hoffW, heW, hdeclW, hneW,
              routingW, hspanW, hptsW⟩
          obtain ⟨hqW1, hqW2, _⟩ := execution.installed_edge_installer hinstW' hselected
            hedge rfl hrun hpart qW ctx0W iW eW hmemW hctxW heW hdeclW
          have hposW : qW.1[pos]? = some key := by
            rw [hqW1]
            exact hpos
          have hbord0 : node.border = 0 := hborder.trans hzero
          have hrealW_run : straightRealNode run.proper pos = true :=
            Xc_installed_component_node_real hrun hnodeLocal hbord0
              (X_componentRun_source_isReal hrun hnodeLocal)
          have hproperW : ctx0W.proper = run.proper := by
            have hc := hctxW
            rw [hqW2, hpart] at hc
            unfold placeComponentExact at hc
            dsimp only at hc
            exact congrArg StraightenCtx.proper (Option.some.inj hc).symm
          have hrealW : straightRealNode ctx0W.proper pos = true := by
            rw [hproperW]
            exact hrealW_run
          have hmemP := installed_part_box_mem hposW hrealW hlook hsource hrole
          have hcond := List.all_eq_true.mp hclrW _ hmemP
          have hcondBeta : (execution.packedAcc.rects.getD key default == spanW.tailRect ||
              execution.packedAcc.rects.getD key default == spanW.headRect || false ||
              !Polyline.hitsRectB [⟨spanW.column, spanW.top⟩, ⟨spanW.column, spanW.bottom⟩]
                (execution.packedAcc.rects.getD key default)) = true := hcond
          have hmissC : ¬ Polyline.hitsRect ptsCorr
              (execution.packedAcc.rects.getD key default) :=
            Xc_corridor_miss_of_check hshapeW hltW hptsEqW hcondBeta
          have hrouteEqC : route.points = ptsCorr.map fun p => shiftPoint
              execution.params.canvasMargin execution.params.canvasMargin
              (orientPoint o.direction execution.packedAcc.canvasH p) :=
            congrArg Route.points (Option.some.inj (hrouteAt.symm.trans hrouteC))
          rw [hrouteEqC, hframeEq]
          exact not_hitsRect_shift_orient o.direction execution.packedAcc.canvasH
            execution.params.canvasMargin execution.params.canvasMargin _ _ hmissC
  · exact execution.chosenRoute_misses_other_part hpacked hselected hrouteLocal hpartNodup
      hmodelAt hrouteAt (Ne.symm hsame) hentry hpos hframeAt

end Elegant.Layered.PipelineImpl

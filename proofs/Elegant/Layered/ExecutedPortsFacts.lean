import Elegant.Layered.PipelineFacts
import Elegant.Layered.RouteTransport
import Elegant.Layered.SizingFacts
import Elegant.Layered.Assembly
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.StraightenFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem plain_frame_eq_boxRect (P : Params) (cg : Graph) (run : Run)
    (v : Nat) (hv : v < run.proper.nodes.length)
    (hplain : (cg.nodes.getD v default).border ≠ -2) :
    frameRect P cg run v = RouteImpl.boxRect run.proper run.xs run.ys v := by
  have hb : ((cg.nodes.getD v default).border != -2) = true := by
    simp only [bne_iff_ne]
    exact hplain
  unfold frameRect
  dsimp only
  rw [ite_eq_left hb]
  simp only [nodeRect,
    RouteImpl.boxRect, RouteImpl.xAt, RouteImpl.yAt,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
    Option.getD_some, RouteImpl.nodeW, RouteImpl.nodeH]

theorem componentRun_ordinary_route_attachment
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < cg.edges.length) {first last : Nat}
    (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last)
    (hsource : (cg.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border ≠ -2)
    (htarget : (cg.nodes.getD (RouteImpl.edgeAt run.proper last).head default).border ≠ -2)
    (cursor : Int) (loops : List (Nat × LoopPlacement))
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (margin : Int) (direction : Direction) (canvasH boxX boxY : Int) :
    ∃ rt : EdgeRoute, ∃ start finish : Point,
      run.routes[i]? = some rt ∧ rt.original = i ∧
      (placeComponent P cg run cursor labels loops).routes[i]? =
        some ((cg.edges[i]).decl, rt.points.map
          (shiftPoint (cursor - (placeBounds P cg run labels loops).minX)
            (0 - (placeBounds P cg run labels loops).minY))) ∧
      rt.points.head? = some start ∧ rt.points.getLast? = some finish ∧
      let source := frameRect P cg run (RouteImpl.edgeAt run.proper first).tail
      let target := frameRect P cg run (RouteImpl.edgeAt run.proper last).head
      let reversed := (cg.edges.map (·.reversed)).getD i false
      let bounds := placeBounds P cg run labels loops
      let transport := routePointTransport margin direction canvasH boxX boxY bounds.minX bounds.minY
      let transportRect := fun rect => shiftRect margin margin
        (orientRect direction canvasH
          (shiftRect (boxX - bounds.minX) (boxY - bounds.minY) rect))
      Validator.onBoundary (transport start) (transportRect (if reversed then target else source)) ∧
      Validator.onBoundary (transport finish) (transportRect (if reversed then source else target)) := by
  obtain ⟨rt, hrt, horiginal, _⟩ := componentRun_route_of_index hrun hi
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouting, _, _, _, hroutes⟩ :=
    componentRun_spec hrun
  have hm : rt ∈ run.routes := List.mem_iff_getElem?.mpr ⟨i, hrt⟩
  have hfirst' : (RouteImpl.edgesOf run.proper rt.original).head? = some first := by
    simpa only [horiginal] using hfirst
  have hlast' : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last := by
    simpa only [horiginal] using hlast
  obtain ⟨px, qx, _, _, hpx0, hpx1, hqx0, hqx1, hend⟩ :=
    Elegant.Layered.route_endpoints_on_ports hrouting hroutes rt hm first last hfirst' hlast'
  rw [horiginal] at hend
  have hgeometry := RouteImpl.routeWithLanes_geometry hrouting
  obtain ⟨_, hdims, _, _, hedge⟩ := RouteImpl.layersOk_spec hgeometry.1
  have hf := hedge first (RouteImpl.mem_edgesOf (RouteImpl.mem_of_head' hfirst))
  have hl := hedge last (RouteImpl.mem_edgesOf (List.mem_of_getLast? hlast))
  have hsh := (hdims _ hf.1).2
  have hth := (hdims _ hl.2.1).2
  have hsboundary : Validator.onBoundary
      ⟨px, RouteImpl.tailPortY run.proper run.ys (RouteImpl.edgeAt run.proper first).tail⟩
      (RouteImpl.boxRect run.proper run.xs run.ys (RouteImpl.edgeAt run.proper first).tail) := by
    by_cases hfk : RouteImpl.frameKind run.proper (RouteImpl.edgeAt run.proper first).tail = -2
    · simp only [Validator.onBoundary, RouteImpl.tailPortY, RouteImpl.boxRect, hfk, ↓reduceIte]
      exact ⟨hpx0, hpx1, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
    · simp only [Validator.onBoundary, RouteImpl.tailPortY, RouteImpl.boxRect, hfk, ↓reduceIte]
      exact ⟨hpx0, hpx1, by omega, by omega, Or.inr (Or.inr (Or.inr True.intro))⟩
  have htboundary : Validator.onBoundary
      ⟨qx, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head).y⟩
      (RouteImpl.boxRect run.proper run.xs run.ys (RouteImpl.edgeAt run.proper last).head) := by
    simp only [Validator.onBoundary, RouteImpl.boxRect]
    exact ⟨hqx0, hqx1, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
  have hplaced := placeComponent_route_entry_of_producer hrun cursor loops i hi hloop
  have hget : run.routes[i]'(by
      rw [componentRun_routes_length hrun, componentRun_proper_chains_length hrun]
      exact hi) = rt := (List.getElem?_eq_some_iff.mp hrt).2
  rw [hget] at hplaced
  rw [plain_frame_eq_boxRect P cg run _ hf.1 hsource,
    plain_frame_eq_boxRect P cg run _ hl.2.1 htarget]
  split at hend
  · rename_i hrev
    obtain ⟨hhead, htail⟩ := hend
    refine ⟨rt, _, _, hrt, horiginal, hplaced, hhead, htail, ?_⟩
    dsimp only
    simp only [hrev, ↓reduceIte]
    constructor
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htboundary
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsboundary
  · rename_i hrev
    obtain ⟨hhead, htail⟩ := hend
    refine ⟨rt, _, _, hrt, horiginal, hplaced, hhead, htail, ?_⟩
    dsimp only
    simp only [hrev]
    constructor
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsboundary
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htboundary

theorem componentRun_normalized_source
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) :
    ∃ ranks normalized,
      normalize cg ranks = .ok normalized ∧
      run.proper.edges = normalized.edges ∧
      run.proper.chains = normalized.chains := by
  obtain ⟨ranks, normalized, labeled, projected, hn, hlabels, hcoordinate,
    _, _, hproxy, hdrop, _⟩ := componentRun_spec hrun
  obtain ⟨hlabelEdges, _, hlabelChains, _⟩ := Labels.addLabelNodes_metadata hlabels
  have hclean : ∀ e ∈ (titleReservations (sizeProperPorts P labeled)).edges,
      e.synthetic = false := by
    intro e he
    have hedge : (titleReservations (sizeProperPorts P labeled)).edges =
        normalized.edges := hlabelEdges
    rw [hedge] at he
    exact normalize_clean hn e he
  have hprojectedEdges := (proxyWidths_rel hproxy).1
  have hdropEdges : (OrderImpl.dropSynthetic projected).edges =
      (OrderImpl.dropSynthetic
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
          P.clusterBorderW)).edges := by
    show projected.edges.filter (fun e => !e.synthetic) = _
    rw [hprojectedEdges, ← hcoordinate]
    rfl
  refine ⟨ranks, normalized, hn, ?_, ?_⟩
  · rw [← hdrop, hdropEdges,
      OrderImpl.dropSynthetic_addClusterBorders_edges _ _ hclean]
    exact hlabelEdges
  · rw [← hdrop, OrderImpl.dropSynthetic_chains, proxyWidths_chains hproxy,
      ← hcoordinate, coordinateGraph_chains, hlabelChains]

theorem componentRun_semantic_node_chain
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ chain : List Nat,
      run.proper.chains[i]? = some chain ∧ 2 ≤ chain.length ∧
      chain.head? = some edge.tail ∧ chain.getLast? = some edge.head ∧
      ∀ (j : Nat) (hj : j < chain.length) (hj1 : j + 1 < chain.length),
        ∃ properEdge ∈ run.proper.edges,
          properEdge.original = i ∧ properEdge.decl = edge.decl ∧
          properEdge.tail = chain[j] ∧ properEdge.head = chain[j + 1] := by
  obtain ⟨ranks, normalized, hn, he, hc⟩ := componentRun_normalized_source hrun
  have hchain := (normalize_ok hn).2.2 i (List.getElem?_eq_some_iff.mp hedge).1 edge hedge
  change NormalizeImpl.ChainFact cg.edges normalized (edge, i) normalized.chains[i]? at hchain
  obtain ⟨_, hchain⟩ := hchain
  rw [ite_eq_right hne] at hchain
  obtain ⟨chain, hget, hlen, hhead, hlast, hsegments⟩ := hchain
  refine ⟨chain, ?_, hlen, hhead, hlast, ?_⟩
  · rw [hc]
    exact hget
  · intro j hj hj1
    obtain ⟨properEdge, hm, ho, hd, ht, hh⟩ := hsegments j hj hj1
    refine ⟨properEdge, ?_, ho, hd, ht, hh⟩
    rw [he]
    exact hm

theorem componentRun_source_isReal
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node) :
    RouteImpl.IsReal run.proper v := by
  obtain ⟨_, normalized, labeled, projected, hn, hl, hc, _, _, hp, hd, _⟩ :=
    componentRun_spec hrun
  have hnormalized := normalize_node_record hn hnode
  have hlabeled := addLabelNodes_untouched_node hl hnormalized rfl
  have hsized : Metadata.NodeMetadata labeled (sizeProperPorts P labeled) := by
    apply Metadata.nodeMetadata_of_lookup_maps
    intro index
    have hk := congrArg (Option.map (fun t : Bool × Int × List Nat => t.1))
      (sizeProperPorts_key P labeled index)
    simpa only [Option.map_map, Function.comp_def] using hk
  have htitled : Metadata.NodeMetadata (sizeProperPorts P labeled)
      (titleReservations (sizeProperPorts P labeled)) :=
    Metadata.nodeMetadata_map_append titleF (fun nd => (titleF_keys nd).1) _
      (titleReservations_nodes _)
  have hbordered := Metadata.nodeMetadata_borderExtension
    (OrderImpl.addClusterBorders_metadata (titleReservations (sizeProperPorts P labeled))
      P.clusterBorderW)
  have hcleared : Metadata.NodeMetadata
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW)
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)) :=
    Metadata.nodeMetadata_map clearF (fun nd => (clearF_keys nd).1)
      (clearProxyExtents_nodes _)
  obtain ⟨sized, hs, hsd⟩ := hsized v _ hlabeled
  obtain ⟨titled, ht, htd⟩ := htitled v _ hs
  obtain ⟨bordered, hb, hbd⟩ := hbordered v _ ht
  obtain ⟨cleared, hclear, hcd⟩ := hcleared v _ hb
  obtain ⟨coordinate, hcoordinate, hmd⟩ := materialize_exists _ hclear
  have hcoordinate' : run.coordinateProper.nodes[v]? = some coordinate := by
    rw [← hc]
    exact hcoordinate
  obtain ⟨out, hout, hod, _, _⟩ := (proxyWidths_rel hp).2.2.2.2.1 v _ hcoordinate'
  have hfinal : run.proper.nodes[v]? = some out := by
    rw [← hd]
    exact hout
  intro nd hnd
  have heq := Option.some.inj (hnd.symm.trans hfinal)
  subst nd
  exact hod.trans (hmd.trans (hcd.trans (hbd.trans (htd.trans hsd))))

private theorem real_tail_first {p : Proper} {v : Nat} (hv : RouteImpl.IsReal p v) :
    ∀ es : List Nat, RouteImpl.chainRel (RouteImpl.ChainLink p) es →
      ∀ e ∈ es, (RouteImpl.edgeAt p e).tail = v →
        ∃ first, es.head? = some first ∧ (RouteImpl.edgeAt p first).tail = v
  | [], _, _, hm, _ => by simp at hm
  | [a], _, e, hm, ht => by
    have he : e = a := by simpa only [List.mem_singleton] using hm
    subst e
    exact ⟨a, rfl, ht⟩
  | a :: b :: rest, hc, e, hm, ht => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, rfl, ht⟩
    · obtain ⟨first, hfirst, htail⟩ := real_tail_first hv (b :: rest) hc.2 e hm ht
      have hbf : b = first := Option.some.inj hfirst
      have hb : (RouteImpl.edgeAt p b).tail = v := by simpa only [hbf] using htail
      obtain ⟨_, _, _, nd, hnd, hdummy⟩ := hc.1
      have hreal := hv nd (by rw [← hb]; exact hnd)
      rw [hreal] at hdummy
      contradiction

private theorem real_head_last {p : Proper} {v : Nat} (hv : RouteImpl.IsReal p v) :
    ∀ es : List Nat, RouteImpl.chainRel (RouteImpl.ChainLink p) es →
      ∀ e ∈ es, (RouteImpl.edgeAt p e).head = v →
        ∃ last, es.getLast? = some last ∧ (RouteImpl.edgeAt p last).head = v
  | [], _, _, hm, _ => by simp at hm
  | [a], _, e, hm, ht => by
    have he : e = a := by simpa only [List.mem_singleton] using hm
    subst e
    exact ⟨a, rfl, ht⟩
  | a :: b :: rest, hc, e, hm, ht => by
    rcases List.mem_cons.mp hm with rfl | hm
    · obtain ⟨_, _, hlink, nd, hnd, hdummy⟩ := hc.1
      have hb : (RouteImpl.edgeAt p b).tail = v := hlink.symm.trans ht
      have hreal := hv nd (by rw [← hb]; exact hnd)
      rw [hreal] at hdummy
      contradiction
    · obtain ⟨last, hlast, hhead⟩ := real_head_last hv (b :: rest) hc.2 e hm ht
      exact ⟨last, by simpa only [List.getLast?_cons_cons] using hlast, hhead⟩

private theorem mem_edgesOf_of_record {p : Proper} {i : Nat} {edge : ProperEdge}
    (hm : edge ∈ p.edges) (ho : edge.original = i) :
    ∃ k ∈ RouteImpl.edgesOf p i, RouteImpl.edgeAt p k = edge := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  have hb := (List.getElem?_eq_some_iff.mp hk).1
  have hrecord : RouteImpl.edgeAt p k = edge := by
    simp only [RouteImpl.edgeAt, List.getD_eq_getElem?_getD, hk, Option.getD_some]
  refine ⟨k, ?_, hrecord⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr hb, by simp only [hrecord, ho, beq_self_eq_true]⟩

theorem componentRun_chain_endpoints
    {P : Params} (hP : P.Valid) {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hd : (cg.edges.map (·.decl)).Nodup) (hshape : CgShape cg)
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ first last,
      (RouteImpl.edgesOf run.proper i).head? = some first ∧
      (RouteImpl.edgesOf run.proper i).getLast? = some last ∧
      (RouteImpl.edgeAt run.proper first).tail = edge.tail ∧
      (RouteImpl.edgeAt run.proper last).head = edge.head := by
  obtain ⟨chain, hchain, hlen, hhead, hlast, hsegments⟩ :=
    componentRun_semantic_node_chain hrun hedge hne
  obtain ⟨ranks, normalized, hn, _, _⟩ := componentRun_normalized_source hrun
  have hwf := (normalize_node_rank_alignment hn).2
  have hbounds := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
  have htailReal : RouteImpl.IsReal run.proper edge.tail :=
    componentRun_source_isReal hrun
      (List.getElem?_eq_getElem hbounds.1)
  have hheadReal : RouteImpl.IsReal run.proper edge.head :=
    componentRun_source_isReal hrun
      (List.getElem?_eq_getElem hbounds.2.1)
  have hproper := (componentRun_facts hP hd hshape hrun).1 i
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp hhead
  obtain ⟨firstEdge, hfirstMem, hfirstOriginal, _, hfirstTail, _⟩ :=
    hsegments 0 (by omega) (by omega)
  obtain ⟨firstIndex, hfirstIndex, hfirstRecord⟩ :=
    mem_edgesOf_of_record hfirstMem hfirstOriginal
  have hfirstValue : (RouteImpl.edgeAt run.proper firstIndex).tail = edge.tail := by
    rw [hfirstRecord]
    exact hfirstTail
  obtain ⟨first, hfirst, hfirstTail⟩ :=
    real_tail_first htailReal _ hproper firstIndex hfirstIndex hfirstValue
  have hlastValue : (edge.tail :: rest)[(edge.tail :: rest).length - 1]'(by omega) =
      edge.head := by
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega)] at hlast
    exact Option.some.inj hlast
  obtain ⟨lastEdge, hlastMem, hlastOriginal, _, _, hlastHead⟩ :=
    hsegments ((edge.tail :: rest).length - 2) (by omega) (by omega)
  obtain ⟨lastIndex, hlastIndex, hlastRecord⟩ :=
    mem_edgesOf_of_record hlastMem hlastOriginal
  have hlastValue' : (RouteImpl.edgeAt run.proper lastIndex).head = edge.head := by
    rw [hlastRecord, hlastHead]
    have hk : (edge.tail :: rest).length - 2 + 1 =
        (edge.tail :: rest).length - 1 := by omega
    simpa only [hk] using hlastValue
  obtain ⟨last, hlast, hlastHead⟩ :=
    real_head_last hheadReal _ hproper lastIndex hlastIndex hlastValue'
  exact ⟨first, last, hfirst, hlast, hfirstTail, hlastHead⟩

theorem componentRun_ordinary_edge_attachment
    {P : Params} (hP : P.Valid) {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hd : (cg.edges.map (·.decl)).Nodup) (hshape : CgShape cg)
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head)
    (hsource : (cg.nodes.getD edge.tail default).border ≠ -2)
    (htarget : (cg.nodes.getD edge.head default).border ≠ -2)
    (loops : List (Nat × LoopPlacement))
    (hloop : ∀ l ∈ loops, l.1 ≠ edge.decl)
    (margin : Int) (direction : Direction) (canvasH boxX boxY : Int) :
    ∃ rt : EdgeRoute, ∃ start finish : Point,
      run.routes[i]? = some rt ∧ rt.original = i ∧
      (placeComponent P cg run 0 labels loops).routes[i]? =
        some (edge.decl, rt.points.map
          (shiftPoint (0 - (placeBounds P cg run labels loops).minX)
            (0 - (placeBounds P cg run labels loops).minY))) ∧
      rt.points.head? = some start ∧ rt.points.getLast? = some finish ∧
      let bounds := placeBounds P cg run labels loops
      let transport := routePointTransport margin direction canvasH boxX boxY bounds.minX bounds.minY
      let transportRect := fun rect => shiftRect margin margin
        (orientRect direction canvasH
          (shiftRect (boxX - bounds.minX) (boxY - bounds.minY) rect))
      Validator.onBoundary (transport start)
        (transportRect (frameRect P cg run (if edge.reversed then edge.head else edge.tail))) ∧
      Validator.onBoundary (transport finish)
        (transportRect (frameRect P cg run (if edge.reversed then edge.tail else edge.head))) := by
  obtain ⟨first, last, hfirst, hlast, htail, hhead⟩ :=
    componentRun_chain_endpoints hP hd hshape hrun hedge hne
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  have hs : (cg.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border ≠ -2 := by
    simpa only [htail] using hsource
  have ht : (cg.nodes.getD (RouteImpl.edgeAt run.proper last).head default).border ≠ -2 := by
    simpa only [hhead] using htarget
  have hl : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl := by simpa only [he] using hloop
  obtain ⟨rt, start, finish, hget, ho, hplaced, hstart, hfinish, hports⟩ :=
    componentRun_ordinary_route_attachment hrun hi hfirst hlast hs ht 0 loops hl
      margin direction canvasH boxX boxY
  refine ⟨rt, start, finish, hget, ho, ?_, hstart, hfinish, ?_⟩
  · simpa only [he] using hplaced
  · dsimp only at hports ⊢
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hedge,
      Option.map_some, Option.getD_some, htail, hhead] at hports
    cases hr : edge.reversed <;> simpa only [hr, Bool.false_eq_true, ↓reduceIte] using hports

theorem SceneExecution.source_box_lookup_of_box_ids_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
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
    rw [execution.boxes_eq_map]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hsource,
      Option.map_some, Nat.zero_add]
    rfl
  have hids : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
    rw [execution.boxes_eq_map, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hids]
    exact hboxIds
  change res.scene.boxes.find? (fun candidate => candidate.id == source.id) = some box
  exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hnodup box
    (List.mem_of_getElem? hbox)

theorem SceneExecution.source_box_lookup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {index : Nat} {source : ModelBox}
    (hsource : inp.boxes[index]? = some source) :
    res.scene.layoutDump.box? source.id =
      some (Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD index default)))
        source.parent source.exclusive) :=
  execution.source_box_lookup_of_box_ids_nodup (Model.boxIds_nodup hwf) hsource

theorem edgeOf_semantic_endpoints
    {inp : Input} {route : ModelRoute} {index : Nat} {edge : Edge}
    (h : edgeOf inp route index = .ok edge) :
    edge.decl = index ∧ edge.reversed = false ∧
      ∃ source target : ModelBox,
        inp.boxes[edge.tail]? = some source ∧ source.id = route.fromId ∧
        inp.boxes[edge.head]? = some target ∧ target.id = route.toId := by
  unfold edgeOf at h
  cases hs : inp.boxes.findIdx? (fun box => box.id == route.fromId) with
  | none => simp only [hs] at h; contradiction
  | some sourceIndex =>
    cases ht : inp.boxes.findIdx? (fun box => box.id == route.toId) with
    | none => simp only [hs, ht] at h; contradiction
    | some targetIndex =>
      simp only [hs, ht, Except.ok.injEq] at h
      subst edge
      obtain ⟨hsbound, hsid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hs
      obtain ⟨htbound, htid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp ht
      refine ⟨rfl, rfl, inp.boxes[sourceIndex], inp.boxes[targetIndex],
        List.getElem?_eq_getElem hsbound, ?_, List.getElem?_eq_getElem htbound, ?_⟩
      · exact beq_iff_eq.mp hsid
      · exact beq_iff_eq.mp htid

private theorem original_idempotent (edge : Edge) : edge.original.original = edge.original := by
  cases hr : edge.reversed <;> simp [Edge.original, hr]

private theorem cycleGraph_semantic_edges (graph : Graph) :
    (cycleGraph graph).edges.map Edge.original = graph.edges.map Edge.original := by
  unfold cycleGraph
  split
  · exact ProtectedCycles.semantic_identity graph (Compound.constraints graph)
  · rw [breakCycles_edges_eq, List.map_map]
    apply List.map_congr_left
    intro edge _
    change (graph.orient edge).original = edge.original
    unfold Graph.orient
    split
    · exact Edge.reverse_original edge
    · rfl

theorem componentCandidate_semantic_edges (graph : Graph) (component : List Nat)
    (index : Nat) :
    (componentCandidate graph component index).edges.map Edge.original =
      (componentGraph graph component).edges.map Edge.original := by
  unfold componentCandidate
  split
  · dsimp only
    split
    · rw [show ∀ g : Graph, (Compound.protect g).edges.map Edge.original =
          g.edges.map Edge.original from
          fun g => ProtectedCycles.semantic_identity g (Compound.constraints g),
        breakCyclesGreedy_semantic_identity]
      simp only [List.map_map, Function.comp_def, original_idempotent]
    · rw [breakCyclesGreedy_semantic_identity]
      simp only [List.map_map, Function.comp_def, original_idempotent]
  · rw [cycleGraph_semantic_edges]
    simp only [List.map_map, Function.comp_def, original_idempotent]

private theorem original_remap (edge : Edge) (f : Nat → Nat) :
    ({ edge with tail := f edge.tail, head := f edge.head }).original =
      { edge.original with tail := f edge.original.tail, head := f edge.original.head } := by
  cases hr : edge.reversed <;> simp [Edge.original, hr]

theorem componentCandidate_semantic_source
    {graph : Graph} {component : List Nat} {index : Nat} {edge : Edge}
    (hedge : edge ∈ (componentCandidate graph component index).edges) :
    ∃ source ∈ graph.edges, source.tail ∈ component ∧
      edge.original = { source.original with
        tail := component.idxOf source.original.tail,
        head := component.idxOf source.original.head } := by
  have hm : edge.original ∈ (componentGraph graph component).edges.map Edge.original := by
    rw [← componentCandidate_semantic_edges graph component index]
    exact List.mem_map_of_mem hedge
  obtain ⟨localEdge, hlocal, heq⟩ := List.mem_map.mp hm
  change localEdge ∈ (graph.edges.filter fun e => component.contains e.tail).map
    (fun e => { e with tail := component.idxOf e.tail, head := component.idxOf e.head }) at hlocal
  obtain ⟨source, hsource, hlocal⟩ := List.mem_map.mp hlocal
  obtain ⟨hsource, htail⟩ := List.mem_filter.mp hsource
  refine ⟨source, hsource, List.contains_iff_mem.mp htail, ?_⟩
  rw [← heq, ← hlocal]
  exact original_remap source component.idxOf

private theorem graphEdgesFrom_entry (inp : Input) :
    ∀ (routes : List ModelRoute) (offset : Nat) (edges : List Edge),
      graphEdgesFrom inp offset routes = .ok edges →
      ∀ (i : Nat) (edge : Edge), edges[i]? = some edge →
        ∃ route, routes[i]? = some route ∧ edgeOf inp route (offset + i) = .ok edge
  | [], _, edges, h, _, _, hi => by
    cases Except.ok.inj h
    simp at hi
  | route :: routes, offset, edges, h, i, edge, hi => by
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    cases Except.ok.inj h
    cases i with
    | zero =>
      have he : first = edge := Option.some.inj hi
      exact ⟨route, rfl, by simpa only [Nat.add_zero, he] using hfirst⟩
    | succ i =>
      obtain ⟨source, hs, he⟩ := graphEdgesFrom_entry inp routes (offset + 1) rest hrest i edge hi
      refine ⟨source, hs, ?_⟩
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using he

theorem measuredGraph_edge_source
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {edge : Edge} (hedge : edge ∈ graph.edges) :
    ∃ index route source,
      inp.routes[index]? = some route ∧ edgeOf inp route index = .ok source ∧
      edge = Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) source := by
  unfold measuredGraph at hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  obtain ⟨edges, hedges, hgraph⟩ := bind_ok hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  have hg := Except.ok.inj hgraph
  subst graph
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hedge
  obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hsource
  obtain ⟨route, hroute, hconstructor⟩ :=
    graphEdgesFrom_entry inp inp.routes 0 edges hedges index source hindex
  exact ⟨index, route, source, hroute, by simpa only [Nat.zero_add] using hconstructor,
    heq.symm⟩

theorem componentCandidate_model_endpoint_source
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {component : List Nat} {candidate : Nat} {edge : Edge}
    (hedge : edge ∈ (componentCandidate graph component candidate).edges) :
    ∃ index route raw source target,
      inp.routes[index]? = some route ∧ edgeOf inp route index = .ok raw ∧
      edge.decl = index ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = route.toId ∧
      let prepared := inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box
      let aliased := Compound.aliasEdge prepared raw
      edge.original = { aliased with
        tail := component.idxOf aliased.tail, head := component.idxOf aliased.head } := by
  obtain ⟨globalEdge, hglobal, _, hsemantic⟩ := componentCandidate_semantic_source hedge
  obtain ⟨index, route, raw, hroute, hraw, halias⟩ := measuredGraph_edge_source hgraph hglobal
  obtain ⟨hdecl, hreversed, source, target, hsource, hsourceId, htarget, htargetId⟩ :=
    edgeOf_semantic_endpoints hraw
  have hglobalReversed : globalEdge.reversed = false := by
    rw [halias]
    exact hreversed
  have horiginal : globalEdge.original = globalEdge := by
    cases globalEdge with
    | mk tail head minLen decl reversed =>
      cases hglobalReversed
      rfl
  have hdecl' : edge.decl = index := by
    calc
      edge.decl = globalEdge.decl := by
        simpa only [Edge.original_decl] using congrArg Edge.decl hsemantic
      _ = raw.decl := by rw [halias]; rfl
      _ = index := hdecl
  refine ⟨index, route, raw, source, target, hroute, hraw, hdecl',
    hsource, hsourceId, htarget, htargetId, ?_⟩
  dsimp only
  rw [horiginal, halias] at hsemantic
  exact hsemantic

private theorem guarded_rect_write (a : Array Rect) (key : Nat) (rect : Rect) :
    (if key < a.size then a.set! key rect else a) = a.set! key rect := by
  by_cases h : key < a.size
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, Array.set!_eq_setIfInBounds]
    simp only [Array.setIfInBounds, h, ↓reduceDIte]

private theorem guarded_rect_fold (entries : List (Nat × Rect)) (a : Array Rect)
    (transform : Rect → Rect) :
    entries.foldl (fun out entry =>
      if entry.1 < out.size then out.set! entry.1 (transform entry.2) else out) a =
      entries.foldl (fun out entry => out.set! entry.1 (transform entry.2)) a := by
  have hstep : (fun (out : Array Rect) (entry : Nat × Rect) =>
      if entry.1 < out.size then out.set! entry.1 (transform entry.2) else out) =
      (fun out entry => out.set! entry.1 (transform entry.2)) := by
    funext out entry
    exact guarded_rect_write out entry.1 (transform entry.2)
  rw [hstep]

private theorem pack_rects_eq_fold (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects =
      pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
        (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) start.rects := by
  induction pairs generalizing start with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    unfold packStep
    dsimp only
    rw [guarded_rect_fold]

private theorem pack_rects_fold_untouched (pairs : List ((List Nat × Part) × Rect))
    (a : Array Rect) (key : Nat) (fallback : Rect)
    (hnot : ∀ q ∈ pairs, key ∉ q.1.1) :
    (pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
      (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) a).getD key fallback =
      a.getD key fallback := by
  induction pairs generalizing a with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q' hq' => hnot q' (List.mem_cons_of_mem _ hq'))]
    apply routes_foldl_getD_ne
    intro hm
    obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hm
    exact hnot q List.mem_cons_self (hkey ▸ (List.of_mem_zip hentry).1)

private theorem zip_rect_keys_nodup (keys : List Nat) (rects : List Rect)
    (hn : keys.Nodup) : ((keys.zip rects).map (·.1)).Nodup := by
  induction keys generalizing rects with
  | nil => simp
  | cons key keys ih =>
    cases rects with
    | nil => simp
    | cons rect rects =>
      obtain ⟨hkey, hkeys⟩ := List.nodup_cons.mp hn
      simp only [List.zip_cons_cons, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih rects hkeys⟩
      intro hm
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hm
      exact hkey (heq ▸ (List.of_mem_zip hentry).1)

private theorem pack_rects_fold_selected
    (pairs : List ((List Nat × Part) × Rect)) (a : Array Rect)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hselected : pairs[c]? = some q)
    (i key : Nat) (rect fallback : Rect)
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    (hnodup : q.1.1.Nodup) (hsize : key < a.size)
    (hnot : ∀ q' ∈ pairs.drop (c + 1), key ∉ q'.1.1) :
    (pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
      (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) a).getD key fallback =
      shiftRect q.2.x q.2.y rect := by
  induction pairs generalizing a c with
  | nil => simp at hselected
  | cons current rest ih =>
    simp only [List.foldl_cons]
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hselected
      subst current
      simp only [List.drop_succ_cons, List.drop_zero] at hnot
      rw [pack_rects_fold_untouched rest _ key fallback hnot]
      exact routes_foldl_getD_mem (shiftRect q.2.x q.2.y) _ a i key rect fallback
        hentry (zip_rect_keys_nodup _ _ hnodup) hsize
    | succ c =>
      simp only [List.getElem?_cons_succ] at hselected
      simp only [List.drop_succ_cons] at hnot
      apply ih _ c hselected
      · rw [routes_foldl_size]
        exact hsize
      · exact hnot

theorem actual_components_packed_rect_value
    {P : Params} {inp : Input} {o : Options} {graph : Graph}
    {labels : List MeasuredLabel} {start mid out : Acc}
    (hempty : start.parts = [])
    (hfold : (components graph).foldlM
      (fun acc comp => layoutComponent P inp o graph acc comp labels) start = .ok mid)
    (hpack : packAcc P o mid = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (mid.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} {rect : Rect}
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    (hsize : key < mid.rects.size) (fallback : Rect) :
    out.rects.getD key fallback = shiftRect q.2.x q.2.y rect := by
  obtain ⟨hparts, _⟩ := actual_components_parts hempty hfold
  have hpart : mid.parts[c]? = some q.1 := zip_getElem?_left hselected
  have hmember : q.1 ∈ mid.parts := List.mem_of_getElem? hpart
  have hcomponent : q.1.1 ∈ components graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hmember
  have hnodup : q.1.1.Nodup := components_nodup graph q.1.1 hcomponent
  have hkey : key ∈ q.1.1 := (List.of_mem_zip (List.mem_of_getElem? hentry)).1
  have hnot : ∀ later ∈ (mid.parts.zip packed.boxes).drop (c + 1), key ∉ later.1.1 := by
    intro later hlater
    obtain ⟨j, hcj, hj⟩ := zip_drop_mem_later_getElem? hlater
    have hpartsNodup : (mid.parts.map (·.1)).Nodup := by
      rw [hparts]
      exact components_entries_nodup graph
    obtain ⟨hc, hqc⟩ := List.getElem?_eq_some_iff.mp hpart
    obtain ⟨hjbound, hqj⟩ := List.getElem?_eq_some_iff.mp hj
    have hne : q.1.1 ≠ later.1.1 := by
      have hp := List.pairwise_iff_getElem.mp hpartsNodup
      have hneq := hp c j (by simpa using hc) (by simpa using hjbound) hcj
      simpa only [List.getElem_map, hqc, hqj] using hneq
    have hlaterComponent : later.1.1 ∈ components graph := by
      rw [← hparts]
      exact List.mem_map_of_mem (List.mem_of_getElem? hj)
    exact components_disjoint hcomponent hlaterComponent hne hkey
  unfold packAcc at hpack
  obtain ⟨actualPacked, hactualPacked, hpack⟩ := bind_ok hpack
  have heq : actualPacked = packed := by
    rw [hpacked] at hactualPacked
    exact (Except.ok.inj hactualPacked).symm
  subst actualPacked
  have hout := Except.ok.inj hpack
  subst out
  change ((mid.parts.zip packed.boxes).foldl packStep
    { mid with canvasW := packed.width, canvasH := packed.height, titles := [] }).rects.getD
      key fallback = _
  rw [pack_rects_eq_fold]
  exact pack_rects_fold_selected _ _ c q hselected i key rect fallback hentry hnodup hsize hnot

theorem actual_components_packed_frame_source
    {P : Params} {inp : Input} {o : Options} {graph : Graph}
    {labels : List MeasuredLabel} {start mid out : Acc}
    (hempty : start.parts = [])
    (hfold : (components graph).foldlM
      (fun acc comp => layoutComponent P inp o graph acc comp labels) start = .ok mid)
    (hpack : packAcc P o mid = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (mid.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} (hkey : q.1.1[i]? = some key)
    (hsize : key < mid.rects.size) (fallback : Rect) :
    ∃ candidate run loops area,
      componentRun P (componentCandidate graph q.1.1 candidate) labels
        (candidateOrder candidate) = .ok run ∧
      componentLoops P (componentCandidate graph q.1.1 candidate) run labels = .ok loops ∧
      q.1.2 = { placeComponent P (componentCandidate graph q.1.1 candidate) run 0 labels loops
        with area := area } ∧
      let cg := componentCandidate graph q.1.1 candidate
      let bounds := placeBounds P cg run labels loops
      out.rects.getD key fallback =
        shiftRect q.2.x q.2.y
          (shiftRect (0 - bounds.minX) (0 - bounds.minY) (frameRect P cg run i)) := by
  obtain ⟨_, hall⟩ := actual_components_parts_geometry hempty hfold
  have hpart : q.1 ∈ mid.parts := List.mem_of_getElem? (zip_getElem?_left hselected)
  obtain ⟨candidate, _, run, loops, area, _, _, _, hrun, hloops, hpartdef⟩ := hall q.1 hpart
  let cg := componentCandidate graph q.1.1 candidate
  let bounds := placeBounds P cg run labels loops
  let rect := shiftRect (0 - bounds.minX) (0 - bounds.minY) (frameRect P cg run i)
  have hi : i < cg.nodes.length := by
    have hk := (List.getElem?_eq_some_iff.mp hkey).1
    dsimp only [cg]
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using hk
  have hrect : q.1.2.rects[i]? = some rect := by
    rw [hpartdef]
    change (placeComponent P cg run 0 labels loops).rects[i]? = some rect
    unfold placeComponent
    dsimp only
    simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
    rfl
  have hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect) :=
    List.getElem?_zip_eq_some.mpr ⟨hkey, hrect⟩
  refine ⟨candidate, run, loops, area, hrun, hloops, hpartdef, ?_⟩
  exact actual_components_packed_rect_value hempty hfold hpack packed hpacked
    hselected hentry hsize fallback

private theorem components_fold_rects_size (P : Params) (inp : Input) (o : Options)
    (graph : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o graph acc comp labels) start = .ok out →
      out.rects.size = start.rects.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, hnext, hrest⟩ := bind_ok h
    rw [components_fold_rects_size P inp o graph labels comps next out hrest]
    exact (layoutComponent_sizes hnext).1.symm

theorem SceneExecution.source_box_frame_lookup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} (hkey : q.1.1[i]? = some key)
    {source : ModelBox} (hsource : inp.boxes[key]? = some source) :
    ∃ candidate run loops area,
      componentRun execution.params
        (componentCandidate execution.graph q.1.1 candidate) execution.measured
        (candidateOrder candidate) = .ok run ∧
      componentLoops execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops ∧
      q.1.2 = { placeComponent execution.params
        (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
        with area := area } ∧
      let cg := componentCandidate execution.graph q.1.1 candidate
      let bounds := placeBounds execution.params cg run execution.measured loops
      res.scene.layoutDump.box? source.id =
        some (Box.mk source.id source.role.id
          (shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect q.2.x q.2.y
                (shiftRect (0 - bounds.minX) (0 - bounds.minY)
                  (frameRect execution.params cg run i)))))
          source.parent source.exclusive) := by
  have hsize : execution.componentsAcc.rects.size = inp.boxes.length := by
    have h := components_fold_rects_size execution.params inp o execution.graph
      execution.measured _ _ _ execution.components_eq
    simpa only [Array.size_replicate] using h
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [hsize]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨candidate, run, loops, area, hrun, hloops, hpartdef, hrect⟩ :=
    actual_components_packed_frame_source (by rfl) execution.components_eq execution.packed_eq
      packed hpacked hselected hkey hkeysize default
  refine ⟨candidate, run, loops, area, hrun, hloops, hpartdef, ?_⟩
  dsimp only at hrect ⊢
  have hlookup := execution.source_box_lookup hwf hsource
  rw [hrect] at hlookup
  exact hlookup

private theorem prepared_alias_of_effective_node_roles
    {inp : Input} {raw : Edge} {source target : ModelBox}
    (hsource : inp.boxes[raw.tail]? = some source)
    (htarget : inp.boxes[raw.head]? = some target)
    (hs : source.role = .node ∨
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true)
    (ht : target.role = .node ∨
      inp.fixedSizes.any (fun fixed => fixed.1 == target.id) = true) :
    Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) raw = raw := by
  cases hsf : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) <;>
    cases htf : inp.fixedSizes.any (fun fixed => fixed.1 == target.id) <;>
      rcases hs with hs | hs <;> rcases ht with ht | ht <;>
        simp [Compound.aliasEdge, Compound.endpoint, List.getElem?_map,
          hsource, htarget, hsf, htf, hs, ht] at *

theorem componentCandidate_effective_node_model_keys
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {component : List Nat} {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    (hrun : componentRun P (componentCandidate graph component candidate) labels
      (candidateOrder candidate) = .ok run)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate graph component candidate).edges[i]? = some edge) :
    ∃ (index : Nat) (route : ModelRoute) (raw : Edge) (source target : ModelBox),
      inp.routes[index]? = some route ∧ edge.decl = index ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = route.toId ∧
      (source.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true →
        target.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == target.id) = true →
        component[(if edge.reversed then edge.head else edge.tail)]? = some raw.tail ∧
        component[(if edge.reversed then edge.tail else edge.head)]? = some raw.head) := by
  obtain ⟨index, route, raw, source, target, hroute, _, hdecl,
    hsource, hsourceId, htarget, htargetId, hsemantic⟩ :=
    componentCandidate_model_endpoint_source hgraph (List.mem_of_getElem? hedge)
  refine ⟨index, route, raw, source, target, hroute, hdecl,
    hsource, hsourceId, htarget, htargetId, ?_⟩
  intro hs ht
  dsimp only at hsemantic
  rw [prepared_alias_of_effective_node_roles hsource htarget hs ht] at hsemantic
  have hfrom : (if edge.reversed then edge.head else edge.tail) = component.idxOf raw.tail := by
    have h := congrArg Edge.tail hsemantic
    cases hr : edge.reversed <;> simpa only [Edge.original, hr, Bool.false_eq_true, ↓reduceIte] using h
  have hto : (if edge.reversed then edge.tail else edge.head) = component.idxOf raw.head := by
    have h := congrArg Edge.head hsemantic
    cases hr : edge.reversed <;> simpa only [Edge.original, hr, Bool.false_eq_true, ↓reduceIte] using h
  obtain ⟨_, _, hn, _, _⟩ := componentRun_normalized_source hrun
  have hbounds := RankImpl.wellformed_spec (normalize_node_rank_alignment hn).2
    edge (List.mem_of_getElem? hedge)
  have hlength : (componentCandidate graph component candidate).nodes.length = component.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have hf : component.idxOf raw.tail < component.length := by
    rw [← hfrom]
    split <;> omega
  have ht' : component.idxOf raw.head < component.length := by
    rw [← hto]
    split <;> omega
  constructor
  · rw [hfrom, List.getElem?_eq_getElem hf]
    exact congrArg some (List.getElem_idxOf hf)
  · rw [hto, List.getElem?_eq_getElem ht']
    exact congrArg some (List.getElem_idxOf ht')

private theorem prepared_alias_of_node_roles
    {inp : Input} {raw : Edge} {source target : ModelBox}
    (hsource : inp.boxes[raw.tail]? = some source)
    (htarget : inp.boxes[raw.head]? = some target)
    (hs : source.role = .node) (ht : target.role = .node) :
    Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) raw = raw := by
  exact prepared_alias_of_effective_node_roles hsource htarget (Or.inl hs) (Or.inl ht)

theorem componentCandidate_ordinary_model_keys
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {component : List Nat} {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    (hrun : componentRun P (componentCandidate graph component candidate) labels
      (candidateOrder candidate) = .ok run)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate graph component candidate).edges[i]? = some edge) :
    ∃ (index : Nat) (route : ModelRoute) (raw : Edge) (source target : ModelBox),
      inp.routes[index]? = some route ∧ edge.decl = index ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = route.toId ∧
      (source.role = .node → target.role = .node →
        component[(if edge.reversed then edge.head else edge.tail)]? = some raw.tail ∧
        component[(if edge.reversed then edge.tail else edge.head)]? = some raw.head) := by
  obtain ⟨index, route, raw, source, target, hroute, hdecl,
    hsource, hsourceId, htarget, htargetId, hkeys⟩ :=
    componentCandidate_effective_node_model_keys hgraph hrun hedge
  exact ⟨index, route, raw, source, target, hroute, hdecl,
    hsource, hsourceId, htarget, htargetId, fun hs ht => hkeys (Or.inl hs) (Or.inl ht)⟩

theorem componentCandidate_self_model_key
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {component : List Nat} {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    (hrun : componentRun P (componentCandidate graph component candidate) labels
      (candidateOrder candidate) = .ok run)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate graph component candidate).edges[i]? = some edge) :
    ∃ (index : Nat) (route : ModelRoute) (raw : Edge) (source : ModelBox),
      inp.routes[index]? = some route ∧ edge.decl = index ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      (route.fromId = route.toId →
        edge.tail = edge.head ∧ component[edge.tail]? = some raw.tail) := by
  obtain ⟨index, route, raw, source, target, hroute, hraw, hdecl,
    hsource, hsourceId, _, _, hsemantic⟩ :=
    componentCandidate_model_endpoint_source hgraph (List.mem_of_getElem? hedge)
  refine ⟨index, route, raw, source, hroute, hdecl, hsource, hsourceId, ?_⟩
  intro hselfId
  have hrawSelf : raw.tail = raw.head := by
    unfold edgeOf at hraw
    rw [← hselfId] at hraw
    cases hfind : inp.boxes.findIdx? (fun box => box.id == route.fromId) with
    | none => simp only [hfind] at hraw; contradiction
    | some v =>
      simp only [hfind] at hraw
      have heq := Except.ok.inj hraw
      rw [← heq]
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
  dsimp only at hsemantic
  rw [halias] at hsemantic
  have htail : (if edge.reversed then edge.head else edge.tail) =
      component.idxOf raw.tail := by
    have h := congrArg Edge.tail hsemantic
    cases hr : edge.reversed <;>
      simpa only [Edge.original, hr, Bool.false_eq_true, ↓reduceIte] using h
  have hhead : (if edge.reversed then edge.tail else edge.head) =
      component.idxOf raw.tail := by
    have h := congrArg Edge.head hsemantic
    rw [← hrawSelf] at h
    cases hr : edge.reversed <;>
      simpa only [Edge.original, hr, Bool.false_eq_true, ↓reduceIte] using h
  have hself : edge.tail = edge.head := by
    cases hr : edge.reversed <;> simp only [hr, Bool.false_eq_true, ↓reduceIte] at htail hhead
    all_goals omega
  simp only [← hself, ite_self] at htail
  obtain ⟨_, _, hn, _, _⟩ := componentRun_normalized_source hrun
  have hbounds := RankImpl.wellformed_spec (normalize_node_rank_alignment hn).2
    edge (List.mem_of_getElem? hedge)
  have hlength : (componentCandidate graph component candidate).nodes.length = component.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have hv : component.idxOf raw.tail < component.length := by omega
  refine ⟨hself, ?_⟩
  rw [htail, List.getElem?_eq_getElem hv]
  exact congrArg some (List.getElem_idxOf hv)

theorem SceneExecution.fixed_candidate_node_border_zero
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (component : List Nat) (candidate v : Nat) (hv : v < component.length)
    {source : ModelBox} (hsource : inp.boxes[component[v]]? = some source)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry) :
    ∃ node : Node,
      (componentCandidate execution.graph component candidate).nodes[v]? = some node ∧
      node.border = 0 := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hi : component[v] < execution.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨_, _, node, _, _, hnode, hborder, _⟩ :=
    measuredGraph_fixed_loop_reservation execution.graph_eq hi hsource hfixed
  refine ⟨node, ?_, hborder⟩
  rw [componentCandidate_nodes]
  change (component.map (fun key => execution.graph.nodes.getD key default))[v]? = some node
  simp only [List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

private theorem components_fold_routes_size (P : Params) (inp : Input) (o : Options)
    (graph : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o graph acc comp labels) start = .ok out →
      out.routes.size = start.routes.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, hnext, hrest⟩ := bind_ok h
    rw [components_fold_routes_size P inp o graph labels comps next out hrest]
    exact (layoutComponent_sizes hnext).2.1.symm

theorem SceneExecution.chosen_part_route_entry
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hloop : ∀ l ∈ loops, l.1 ≠ edge.decl) :
    ∃ route : ModelRoute, ∃ native : EdgeRoute,
      inp.routes[edge.decl]? = some route ∧
      run.routes[i]? = some native ∧ native.original = i ∧
      let cg := componentCandidate execution.graph q.1.1 candidate
      let bounds := placeBounds execution.params cg run execution.measured loops
      (res.scene.routes[edge.decl]? =
        some (Route.mk route.id route.fromId route.toId route.orthogonal
          (native.points.map (routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY))) ∨
       ∃ pts : List Point, IsCorridor pts ∧
         res.scene.routes[edge.decl]? =
           some (Route.mk route.id route.fromId route.toId route.orthogonal
             (pts.map fun p => shiftPoint execution.params.canvasMargin execution.params.canvasMargin
               (orientPoint o.direction execution.packedAcc.canvasH p)))) := by
  let cg := componentCandidate execution.graph q.1.1 candidate
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  have hlo : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl := by simpa only [cg, he] using hloop
  have hk : (cg.edges[i]).decl < inp.routes.length :=
    componentCandidate_edge_index_decl_lt execution.graph_eq q.1.1 candidate hi
  have hsize : execution.componentsAcc.routes.size = inp.routes.length := by
    have h := components_fold_routes_size execution.params inp o execution.graph
      execution.measured _ _ _ execution.components_eq
    simpa only [Array.size_replicate] using h
  have hrouteSize : (cg.edges[i]).decl < execution.componentsAcc.routes.size := by
    rw [hsize]
    exact hk
  have hget := placeComponent_route_entry_of_producer hrun 0 loops i hi hlo
  have hpartRoutes : q.1.2.routes =
      (placeComponent execution.params cg run 0 execution.measured loops).routes := by
    rw [hpart]
  rw [← hpartRoutes] at hget
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
  have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
    rw [hpartRoutes]
    exact placeComponent_routes_decls_nodup execution.params cg run 0 execution.measured loops hnd
  have hpackedRoute := Elegant.Layered.actual_components_packAcc_routes_getD
    (by rfl) execution.components_eq (measuredGraph_decls_nodup execution.graph_eq)
    packed execution.packed_eq hpacked c q hselected i _ _ [] hget hpartNodup hrouteSize
  obtain ⟨native, hnative, horiginal, _⟩ := componentRun_route_of_index hrun hi
  have hnativeGet := (List.getElem?_eq_some_iff.mp hnative).2
  have hk' : edge.decl < inp.routes.length := by rw [← he]; exact hk
  have hstraight := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.straightAcc execution.measured edge.decl hk'
  rw [← execution.scene_eq] at hstraight
  have hsizeEq : execution.straightAcc.routes.size = execution.packedAcc.routes.size := by
    have hpb := execution.packedAcc_bounded execution.components_parts_bounded
    obtain ⟨_, _, _, _, _, hsz, _⟩ := straightenAcc_bounded execution.straight_eq hpb.routes_bounded
    exact hsz
  have hpsize : execution.packedAcc.routes.size = inp.routes.length := by
    rw [Elegant.Layered.packAcc_routes_size execution.packed_eq, hsize]
  have hssize : edge.decl < execution.straightAcc.routes.size := by
    rw [hsizeEq, hpsize]
    exact hk'
  have hgetS : execution.straightAcc.routes[edge.decl]? =
      some (execution.straightAcc.routes.getD edge.decl []) := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hssize, Option.getD_some]
  rcases straightenAcc_route_cases execution.straight_eq edge.decl _ hgetS with hpacked | hcor
  · have hbridge : execution.packedAcc.routes.getD edge.decl [] =
        execution.straightAcc.routes.getD edge.decl [] := by
      simp only [Array.getD_eq_getD_getElem?, hpacked, Option.getD_some]
    rw [he, hbridge] at hpackedRoute
    rw [hpackedRoute, execution.straight_canvasH, routePointTransport_eq, hnativeGet] at hstraight
    refine ⟨inp.routes[edge.decl], native, List.getElem?_eq_getElem hk',
      hnative, horiginal, Or.inl ?_⟩
    simpa using hstraight
  · rw [execution.straight_canvasH] at hstraight
    refine ⟨inp.routes[edge.decl], native, List.getElem?_eq_getElem hk',
      hnative, horiginal,
      Or.inr ⟨execution.straightAcc.routes.getD edge.decl [], hcor, ?_⟩⟩
    simpa using hstraight

theorem SceneExecution.part_entry_box_lookup_of_box_ids_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
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
  have hsize : execution.componentsAcc.rects.size = inp.boxes.length := by
    have h := components_fold_rects_size execution.params inp o execution.graph
      execution.measured _ _ _ execution.components_eq
    simpa only [Array.size_replicate] using h
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [hsize]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hrect := actual_components_packed_rect_value (by rfl) execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hkeysize default
  have hlookup := execution.source_box_lookup_of_box_ids_nodup hids hsource
  rw [hrect] at hlookup
  exact hlookup

theorem SceneExecution.part_entry_box_lookup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
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
        source.parent source.exclusive) :=
  execution.part_entry_box_lookup_of_box_ids_nodup
    (Model.boxIds_nodup hwf) packed hpacked hselected hentry hsource




theorem chosen_part_frame_entry
    {P : Params} {graph : Graph} {component : List Nat} {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {part : Part} {area : Int}
    (hpart : part = { placeComponent P (componentCandidate graph component candidate)
      run 0 labels loops with area := area })
    {localIndex key : Nat} (hkey : component[localIndex]? = some key) :
    let cg := componentCandidate graph component candidate
    let bounds := placeBounds P cg run labels loops
    (component.zip part.rects)[localIndex]? =
      some (key, shiftRect (0 - bounds.minX) (0 - bounds.minY) (frameRect P cg run localIndex)) := by
  let cg := componentCandidate graph component candidate
  have hlocal : localIndex < cg.nodes.length := by
    have hk := (List.getElem?_eq_some_iff.mp hkey).1
    dsimp only [cg]
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using hk
  apply List.getElem?_zip_eq_some.mpr
  refine ⟨hkey, ?_⟩
  rw [hpart]
  change (placeComponent P cg run 0 labels loops).rects[localIndex]? = _
  unfold placeComponent
  dsimp only
  simp only [List.getElem?_map, List.getElem?_range hlocal, Option.map_some]
  rfl

theorem shiftRect_pack_normalize (boxX boxY minX minY : Int) (rect : Rect) :
    shiftRect boxX boxY (shiftRect (0 - minX) (0 - minY) rect) =
      shiftRect (boxX - minX) (boxY - minY) rect := by
  dsimp only [shiftRect]
  congr 1 <;> omega
theorem SceneExecution.chosen_part_ordinary_ports
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head)
    (hsource : ((componentCandidate execution.graph q.1.1 candidate).nodes.getD
      edge.tail default).border ≠ -2)
    (htarget : ((componentCandidate execution.graph q.1.1 candidate).nodes.getD
      edge.head default).border ≠ -2)
    (hloop : ∀ l ∈ loops, l.1 ≠ edge.decl) :
    ∃ modelRoute : ModelRoute, ∃ out : Route, ∃ start finish : Point,
      inp.routes[edge.decl]? = some modelRoute ∧
      res.scene.routes[edge.decl]? = some out ∧
      out.fromId = modelRoute.fromId ∧ out.toId = modelRoute.toId ∧
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      let cg := componentCandidate execution.graph q.1.1 candidate
      let bounds := placeBounds execution.params cg run execution.measured loops
      let transportRect := fun rect =>
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY) rect))
      Validator.onBoundary start
        (transportRect (frameRect execution.params cg run
          (if edge.reversed then edge.head else edge.tail))) ∧
      Validator.onBoundary finish
        (transportRect (frameRect execution.params cg run
          (if edge.reversed then edge.tail else edge.head))) := by
  let cg := componentCandidate execution.graph q.1.1 candidate
  obtain ⟨hparts, _⟩ := actual_components_parts (by rfl) execution.components_eq
  have hmember : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  have hcomponent : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hmember
  have hshape : CgShape cg := componentCandidate_shape
    (components_nodup execution.graph q.1.1 hcomponent)
    (measuredGraph_shape execution.graph_eq) candidate
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
  obtain ⟨modelRoute, native, hmodelRoute, hnative, _, hscene⟩ :=
    execution.chosen_part_route_entry packed hpacked hselected hrun hpart hedge hloop
  rcases hscene with hscene | ⟨_pts, _hcor, hrouteC⟩
  · obtain ⟨native', start, finish, hnative', _, _, hstart, hfinish, hports⟩ :=
      componentRun_ordinary_edge_attachment (checkedParams_valid execution.checked)
        hnd hshape hrun hedge hne hsource htarget loops hloop execution.params.canvasMargin
        o.direction execution.packedAcc.canvasH q.2.x q.2.y
    have heq : native' = native := Option.some.inj (hnative'.symm.trans hnative)
    subst native'
    let bounds := placeBounds execution.params cg run execution.measured loops
    let transform := routePointTransport execution.params.canvasMargin o.direction
      execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
    let out := Route.mk modelRoute.id modelRoute.fromId modelRoute.toId modelRoute.orthogonal
      (native.points.map transform)
    refine ⟨modelRoute, out, transform start, transform finish, hmodelRoute,
      hscene, rfl, rfl, ?_, ?_, ?_⟩
    · simp only [out, List.head?_map, hstart, Option.map_some]
    · simp only [out, List.getLast?_map, hfinish, Option.map_some]
    · exact hports
  · have _hlengthC : res.scene.routes.length = inp.routes.length := by
      rw [execution.scene_eq]
      simp only [sceneOf, List.length_map, List.length_zipIdx]
    have _hkeyC : edge.decl < inp.routes.length := by
      have hltC := (List.getElem?_eq_some_iff.mp hrouteC).1
      rw [_hlengthC] at hltC
      exact hltC
    have _hsizeC : execution.componentsAcc.routes.size = inp.routes.length := by
      have hfoldC := components_fold_routes_size execution.params inp o execution.graph
        execution.measured _ _ _ execution.components_eq
      simpa only [Array.size_replicate] using hfoldC
    have _hsizeSC : edge.decl < execution.straightAcc.routes.size := by
      have hpbC := execution.packedAcc_bounded execution.components_parts_bounded
      obtain ⟨_, _, _, _, _, hszC, _⟩ :=
        straightenAcc_bounded execution.straight_eq hpbC.routes_bounded
      have hpsizeC : execution.packedAcc.routes.size = inp.routes.length := by
        rw [Elegant.Layered.packAcc_routes_size execution.packed_eq, _hsizeC]
      rw [hszC, hpsizeC]
      exact _hkeyC
    have _hgetSC : execution.straightAcc.routes[edge.decl]? =
        some (execution.straightAcc.routes.getD edge.decl []) := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem _hsizeSC, Option.getD_some]
    rcases execution.route_cases _hgetSC with _hpackedSC | hinstC
    · have hiP := (List.getElem?_eq_some_iff.mp hedge).1
      have heP := (List.getElem?_eq_some_iff.mp hedge).2
      have hloP : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl := by
        simpa only [cg, heP] using hloop
      have hkP : (cg.edges[i]).decl < inp.routes.length :=
        componentCandidate_edge_index_decl_lt execution.graph_eq q.1.1 candidate hiP
      have hrouteSizeP : (cg.edges[i]).decl < execution.componentsAcc.routes.size := by
        rw [_hsizeC]
        exact hkP
      have hgetP := placeComponent_route_entry_of_producer hrun 0 loops i hiP hloP
      have hpartRoutesP : q.1.2.routes =
          (placeComponent execution.params cg run 0 execution.measured loops).routes := by
        rw [hpart]
      rw [← hpartRoutesP] at hgetP
      have hpartNodupP : (q.1.2.routes.map (·.1)).Nodup := by
        rw [hpartRoutesP]
        exact placeComponent_routes_decls_nodup execution.params cg run 0 execution.measured loops hnd
      have hpackedRouteP := Elegant.Layered.actual_components_packAcc_routes_getD
        (by rfl) execution.components_eq (measuredGraph_decls_nodup execution.graph_eq)
        packed execution.packed_eq hpacked c q hselected i _ _ [] hgetP hpartNodupP hrouteSizeP
      have hnativeGetP := (List.getElem?_eq_some_iff.mp hnative).2
      have hstraightP := sceneOf_routes_getElem? execution.params inp o execution.lines
        execution.straightAcc execution.measured edge.decl _hkeyC
      rw [← execution.scene_eq] at hstraightP
      have hmodelP : inp.routes[edge.decl]'_hkeyC = modelRoute :=
        Option.some.inj ((List.getElem?_eq_getElem _hkeyC).symm.trans hmodelRoute)
      rw [hmodelP] at hstraightP
      have hbridgeP : execution.packedAcc.routes.getD edge.decl [] =
          execution.straightAcc.routes.getD edge.decl [] := by
        simp only [Array.getD_eq_getD_getElem?, _hpackedSC, Option.getD_some]
      rw [heP, hbridgeP] at hpackedRouteP
      rw [hpackedRouteP, execution.straight_canvasH, routePointTransport_eq, hnativeGetP] at hstraightP
      obtain ⟨native', start, finish, hnative', _, _, hstart, hfinish, hports⟩ :=
        componentRun_ordinary_edge_attachment (checkedParams_valid execution.checked)
          hnd hshape hrun hedge hne hsource htarget loops hloop execution.params.canvasMargin
          o.direction execution.packedAcc.canvasH q.2.x q.2.y
      have heqP : native' = native := Option.some.inj (hnative'.symm.trans hnative)
      subst native'
      let boundsP := placeBounds execution.params cg run execution.measured loops
      let transformP := routePointTransport execution.params.canvasMargin o.direction
        execution.packedAcc.canvasH q.2.x q.2.y boundsP.minX boundsP.minY
      let outP := Route.mk modelRoute.id modelRoute.fromId modelRoute.toId modelRoute.orthogonal
        (native.points.map transformP)
      refine ⟨modelRoute, outP, transformP start, transformP finish, hmodelRoute,
        hstraightP, rfl, rfl, ?_, ?_, ?_⟩
      · simp only [outP, List.head?_map, hstart, Option.map_some]
      · simp only [outP, List.getLast?_map, hfinish, Option.map_some]
      · exact hports
    · obtain ⟨_xC, _y0C, _y1C, _tailKeyC, _headKeyC, _tailRectC, _headRectC,
        _htailC, _hheadC, _hHtailC, _hHheadC, _hltC, _hptsC,
        _hx1C, _hx2C, _hx3C, _hx4C, _hy0C, _hy1C⟩ :=
        execution.installed_endpoints hinstC
      have _hstraightEq := execution.straight_points_of_scene hrouteC
      have hrev := execution.installed_edge_not_reversed hinstC hselected hedge rfl
        hrun hpart
      have hifT : (if edge.reversed then edge.head else edge.tail) = edge.tail := by
        simp [hrev]
      have hifH : (if edge.reversed then edge.tail else edge.head) = edge.head := by
        simp [hrev]
      obtain ⟨tK, hK, tR, hR, spanI, _hTailLt, _hHeadLt, hKeyLtB, hKeyHdB, htK, hhK,
        hlookT0, hlookH0, hth, hhh, _hTx, _hTw, _hHx, _hHw,
        hColT1, hColT2, hColH1, hColH2, hTop, hBot, hPtsEq⟩ :=
        execution.installed_part_edge_rects hinstC hselected hedge rfl hrun hpart
      have hspanPts : spanI.points = [⟨_xC, _y0C⟩, ⟨_xC, _y1C⟩] :=
        hPtsEq.symm.trans _hptsC
      have hheadI : spanI.points.head? = some ⟨spanI.column, spanI.top⟩ := rfl
      have hheadC : spanI.points.head? = some ⟨_xC, _y0C⟩ := by
        rw [hspanPts]
        rfl
      have hcolEq : spanI.column = _xC :=
        congrArg Point.x (Option.some.inj (hheadI.symm.trans hheadC))
      have htopEq : spanI.top = _y0C :=
        congrArg Point.y (Option.some.inj (hheadI.symm.trans hheadC))
      have hlastI : spanI.points.getLast? = some ⟨spanI.column, spanI.bottom⟩ := rfl
      have hlastC : spanI.points.getLast? = some ⟨_xC, _y1C⟩ := by
        rw [hspanPts]
        rfl
      have hbotEq : spanI.bottom = _y1C :=
        congrArg Point.y (Option.some.inj (hlastI.symm.trans hlastC))
      have hxT : tR.x ≤ _xC ∧ _xC ≤ tR.x + tR.w := by
        rw [← hcolEq]
        exact ⟨hColT1, hColT2⟩
      have hxH : hR.x ≤ _xC ∧ _xC ≤ hR.x + hR.w := by
        rw [← hcolEq]
        exact ⟨hColH1, hColH2⟩
      have hy0 : _y0C = tR.y + tR.h := by
        rw [← htopEq]
        exact hTop
      have hy1 : _y1C = hR.y := by
        rw [← hbotEq]
        exact hBot
      have hbAccR := corridor_onBoundary_acc hth hhh hxT hxH hy0 hy1
      have hbSceneR := corridor_onBoundary_scene (margin := execution.params.canvasMargin)
        (d := o.direction) (h := execution.packedAcc.canvasH) hbAccR
      let bounds := placeBounds execution.params cg run execution.measured loops
      have hentryT := chosen_part_frame_entry hpart htK
      have hentryH := chosen_part_frame_entry hpart hhK
      have hmidSize : execution.componentsAcc.rects.size = inp.boxes.length := by
        have h := components_fold_rects_size execution.params inp o execution.graph
          execution.measured _ _ _ execution.components_eq
        simpa only [Array.size_replicate] using h
      have hsizeT : tK < execution.componentsAcc.rects.size := by
        rw [hmidSize]
        exact hKeyLtB
      have hsizeH : hK < execution.componentsAcc.rects.size := by
        rw [hmidSize]
        exact hKeyHdB
      have hvalT := actual_components_packed_rect_value (by rfl) execution.components_eq
        execution.packed_eq packed hpacked hselected hentryT hsizeT default
      have hvalH := actual_components_packed_rect_value (by rfl) execution.components_eq
        execution.packed_eq packed hpacked hselected hentryH hsizeH default
      have htRmine : tR = shiftRect q.2.x q.2.y (shiftRect (0 - bounds.minX)
          (0 - bounds.minY) (frameRect execution.params cg run edge.tail)) := by
        have h1 := hvalT
        rw [Array.getD_eq_getD_getElem?, hlookT0, Option.getD_some] at h1
        exact h1
      have htRmineH : hR = shiftRect q.2.x q.2.y (shiftRect (0 - bounds.minX)
          (0 - bounds.minY) (frameRect execution.params cg run edge.head)) := by
        have h1 := hvalH
        rw [Array.getD_eq_getD_getElem?, hlookH0, Option.getD_some] at h1
        exact h1
      have htRgoal : tR = shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY)
          (frameRect execution.params cg run edge.tail) :=
        htRmine.trans (shiftRect_pack_normalize _ _ _ _ _)
      have htRgoalH : hR = shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY)
          (frameRect execution.params cg run edge.head) :=
        htRmineH.trans (shiftRect_pack_normalize _ _ _ _ _)
      have hfinT : Validator.onBoundary
          (shiftPoint execution.params.canvasMargin execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH ⟨_xC, _y0C⟩))
          (shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY)
                (frameRect execution.params cg run edge.tail)))) := by
        rw [← htRgoal]
        exact hbSceneR.1
      have hfinH : Validator.onBoundary
          (shiftPoint execution.params.canvasMargin execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH ⟨_xC, _y1C⟩))
          (shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY)
                (frameRect execution.params cg run edge.head)))) := by
        rw [← htRgoalH]
        exact hbSceneR.2
      refine ⟨modelRoute, Route.mk modelRoute.id modelRoute.fromId modelRoute.toId
        modelRoute.orthogonal (_pts.map fun p => shiftPoint execution.params.canvasMargin
          execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)),
        shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH ⟨_xC, _y0C⟩),
        shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH ⟨_xC, _y1C⟩),
        hmodelRoute, hrouteC, rfl, rfl, ?_, ?_, ?_⟩
      · have hpts : _pts = [⟨_xC, _y0C⟩, ⟨_xC, _y1C⟩] := _hstraightEq.symm.trans _hptsC
        subst hpts
        rfl
      · have hpts : _pts = [⟨_xC, _y0C⟩, ⟨_xC, _y1C⟩] := _hstraightEq.symm.trans _hptsC
        subst hpts
        rfl
      · rw [hifT, hifH]
        exact ⟨hfinT, hfinH⟩

theorem measuredGraph_node_role_not_top
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hrole : source.role = .node) :
    (graph.nodes.getD key default).border ≠ -2 := by
  cases hn : graph.nodes[key]? with
  | none =>
    simp only [List.getD_eq_getElem?_getD, hn, Option.getD_none]
    change (0 : Int) ≠ -2
    omega
  | some node =>
    simp only [List.getD_eq_getElem?_getD, hn, Option.getD_some]
    intro htop
    obtain ⟨hdecl, box, hprepared, hgroup, _⟩ := measuredGraph_group_origin hgraph hn htop
    have hroles := congrArg (Option.map ModelBox.role) hprepared
    cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) <;>
      simp [hdecl, List.getElem?_map, hsource, hf, hrole, hgroup] at hroles

theorem componentCandidate_node_role_not_top
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {component : List Nat} {candidate localIndex key : Nat}
    (hkey : component[localIndex]? = some key)
    {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hrole : source.role = .node) :
    ((componentCandidate graph component candidate).nodes.getD localIndex default).border ≠ -2 := by
  have hnode : (componentCandidate graph component candidate).nodes.getD localIndex default =
      graph.nodes.getD key default := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.getD_eq_getElem?_getD, List.getElem?_map, hkey,
      Option.map_some, Option.getD_some]
  rw [hnode]
  exact measuredGraph_node_role_not_top hgraph hsource hrole


theorem SceneExecution.effective_candidate_node_not_top
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {component : List Nat} {candidate v key : Nat} {source : ModelBox}
    (hkey : component[v]? = some key) (hsource : inp.boxes[key]? = some source)
    (hs : source.role = .node ∨
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true) :
    ((componentCandidate execution.graph component candidate).nodes.getD v default).border ≠ -2 := by
  rcases hs with hs | hs
  · exact componentCandidate_node_role_not_top execution.graph_eq hkey hsource hs
  · cases hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) with
    | none =>
      obtain ⟨entry, hentry, htest⟩ := List.any_eq_true.mp hs
      exact False.elim ((List.find?_eq_none.mp hfixed) entry hentry htest)
    | some entry =>
      have hv := (List.getElem?_eq_some_iff.mp hkey).1
      have hsource' : inp.boxes[component[v]]? = some source := by
        have heq : component[v] = key := (List.getElem?_eq_some_iff.mp hkey).2
        rw [heq]
        exact hsource
      obtain ⟨node, hnode, hborder⟩ :=
        execution.fixed_candidate_node_border_zero component candidate v hv hsource' hfixed
      simpa only [List.getD_eq_getElem?_getD, hnode, Option.getD_some, hborder] using
        (show (0 : Int) ≠ -2 by omega)

theorem SceneExecution.chosen_part_effective_c5_of_box_ids_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ (modelRoute : ModelRoute) (raw : Edge) (source target : ModelBox),
      inp.routes[edge.decl]? = some modelRoute ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = modelRoute.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = modelRoute.toId ∧
      (source.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true →
        target.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == target.id) = true →
        ∃ (out : Route) (start finish : Point) (fromBox toBox : Box),
          res.scene.routes[edge.decl]? = some out ∧
          out.points.head? = some start ∧ out.points.getLast? = some finish ∧
          res.scene.layoutDump.box? out.fromId = some fromBox ∧
          res.scene.layoutDump.box? out.toId = some toBox ∧
          Validator.onBoundary start fromBox.rect ∧
          Validator.onBoundary finish toBox.rect) := by
  let cg := componentCandidate execution.graph q.1.1 candidate
  obtain ⟨index, modelRoute, raw, source, target, hroute, hdecl,
    hsource, hsourceId, htarget, htargetId, hkeys⟩ :=
    componentCandidate_effective_node_model_keys execution.graph_eq hrun hedge
  have hrouteAt : inp.routes[edge.decl]? = some modelRoute := by
    rw [hdecl]
    exact hroute
  refine ⟨modelRoute, raw, source, target, hrouteAt,
    hsource, hsourceId, htarget, htargetId, ?_⟩
  intro hs ht
  obtain ⟨hfromKey, htoKey⟩ := hkeys hs ht
  have hfromNotTop := execution.effective_candidate_node_not_top
    (candidate := candidate) hfromKey hsource hs
  have htoNotTop := execution.effective_candidate_node_not_top
    (candidate := candidate) htoKey htarget ht
  have hordinary : (cg.nodes.getD edge.tail default).border ≠ -2 ∧
      (cg.nodes.getD edge.head default).border ≠ -2 := by
    cases hr : edge.reversed <;>
      simp only [hr, Bool.false_eq_true, ↓reduceIte] at hfromNotTop htoNotTop
    · exact ⟨hfromNotTop, htoNotTop⟩
    · exact ⟨htoNotTop, hfromNotTop⟩
  have hdecls : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
  have hloop := componentLoops_excludes_ordinary_decl hloops hdecls hedge hne
  obtain ⟨emittedRoute, out, start, finish, hemittedRoute, hout, hfromId, htoId,
    hstart, hfinish, hports⟩ :=
    execution.chosen_part_ordinary_ports packed hpacked hselected hrun hpart hedge hne
      hordinary.1 hordinary.2 hloop
  have hsame : emittedRoute = modelRoute :=
    Option.some.inj (hemittedRoute.symm.trans hrouteAt)
  subst emittedRoute
  have hfromEntry := chosen_part_frame_entry hpart hfromKey
  have htoEntry := chosen_part_frame_entry hpart htoKey
  have hfromLookup := execution.part_entry_box_lookup_of_box_ids_nodup hids packed hpacked hselected
    hfromEntry hsource
  have htoLookup := execution.part_entry_box_lookup_of_box_ids_nodup hids packed hpacked hselected
    htoEntry htarget
  dsimp only at hfromLookup htoLookup hports
  rw [shiftRect_pack_normalize] at hfromLookup htoLookup
  let bounds := placeBounds execution.params cg run execution.measured loops
  let transportRect := fun rect =>
    shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY) rect))
  let fromBox := Box.mk source.id source.role.id
    (transportRect (frameRect execution.params cg run
      (if edge.reversed then edge.head else edge.tail))) source.parent source.exclusive
  let toBox := Box.mk target.id target.role.id
    (transportRect (frameRect execution.params cg run
      (if edge.reversed then edge.tail else edge.head))) target.parent target.exclusive
  refine ⟨out, start, finish, fromBox, toBox, hout, hstart, hfinish, ?_, ?_, ?_, ?_⟩
  · rw [hfromId, ← hsourceId]
    exact hfromLookup
  · rw [htoId, ← htargetId]
    exact htoLookup
  · exact hports.1
  · exact hports.2

theorem SceneExecution.chosen_part_ordinary_c5_of_box_ids_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ (modelRoute : ModelRoute) (raw : Edge) (source target : ModelBox),
      inp.routes[edge.decl]? = some modelRoute ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = modelRoute.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = modelRoute.toId ∧
      (source.role = .node → target.role = .node →
        ∃ (out : Route) (start finish : Point) (fromBox toBox : Box),
          res.scene.routes[edge.decl]? = some out ∧
          out.points.head? = some start ∧ out.points.getLast? = some finish ∧
          res.scene.layoutDump.box? out.fromId = some fromBox ∧
          res.scene.layoutDump.box? out.toId = some toBox ∧
          Validator.onBoundary start fromBox.rect ∧
          Validator.onBoundary finish toBox.rect) := by
  obtain ⟨route, raw, source, target, hroute, hsource, hsId, htarget, htId, hports⟩ :=
    execution.chosen_part_effective_c5_of_box_ids_nodup
      hids packed hpacked hselected hrun hloops hpart hedge hne
  exact ⟨route, raw, source, target, hroute, hsource, hsId, htarget, htId,
    fun hs ht => hports (Or.inl hs) (Or.inl ht)⟩

theorem SceneExecution.chosen_part_ordinary_c5
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
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
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ (modelRoute : ModelRoute) (raw : Edge) (source target : ModelBox),
      inp.routes[edge.decl]? = some modelRoute ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = modelRoute.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = modelRoute.toId ∧
      (source.role = .node → target.role = .node →
        ∃ (out : Route) (start finish : Point) (fromBox toBox : Box),
          res.scene.routes[edge.decl]? = some out ∧
          out.points.head? = some start ∧ out.points.getLast? = some finish ∧
          res.scene.layoutDump.box? out.fromId = some fromBox ∧
          res.scene.layoutDump.box? out.toId = some toBox ∧
          Validator.onBoundary start fromBox.rect ∧
          Validator.onBoundary finish toBox.rect) :=
  execution.chosen_part_ordinary_c5_of_box_ids_nodup
    (Model.boxIds_nodup hwf) packed hpacked hselected hrun hloops hpart hedge hne

theorem measuredGraph_decl_range
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph) :
    graph.edges.map (·.decl) = List.range' 0 inp.routes.length := by
  unfold measuredGraph at hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  obtain ⟨edges, hedges, hgraph⟩ := bind_ok hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  have hg := Except.ok.inj hgraph
  subst graph
  rw [Compound.prepare_decls]
  exact graphEdgesFrom_decls inp inp.routes 0 edges hedges

theorem SceneExecution.route_component_source
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {key : Nat} (hkey : key < inp.routes.length) :
    ∃ (packed : Pack.State) (c : Nat) (q : (List Nat × Part) × Rect)
      (candidate : Nat) (run : Run) (loops : List (Nat × LoopPlacement)) (area : Int)
      (i : Nat) (edge : Edge),
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q ∧
      componentRun execution.params
        (componentCandidate execution.graph q.1.1 candidate) execution.measured
        (candidateOrder candidate) = .ok run ∧
      componentLoops execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops ∧
      q.1.2 = { placeComponent execution.params
        (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
        with area := area } ∧
      (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge ∧
      edge.decl = key := by
  have hdecl : key ∈ execution.graph.edges.map (·.decl) := by
    rw [measuredGraph_decl_range execution.graph_eq]
    exact List.mem_range'.mpr ⟨key, hkey, by omega⟩
  obtain ⟨globalEdge, hglobalEdge, hglobalDecl⟩ := List.mem_map.mp hdecl
  have hglobalBounds := sceneExecution_edges_bounded execution globalEdge
    (List.mem_append_left _ hglobalEdge)
  obtain ⟨component, hcomponent, htail⟩ :=
    components_cover hglobalBounds.1 (sceneExecution_edges_bounded execution)
  obtain ⟨hparts, hall⟩ := actual_components_parts_geometry (by rfl) execution.components_eq
  have hcomponentPart : component ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hparts]
    exact hcomponent
  obtain ⟨part, hpartMember, hpartComponent⟩ := List.mem_map.mp hcomponentPart
  obtain ⟨candidate, _, run, loops, area, _, _, _, hrun, hloops, hpart⟩ :=
    hall part hpartMember
  have htailPart : globalEdge.tail ∈ part.1 := by
    simpa only [hpartComponent] using htail
  have hrawDecl : globalEdge.decl ∈ (componentGraph execution.graph part.1).edges.map (·.decl) := by
    unfold componentGraph
    dsimp only
    apply List.mem_map.mpr
    refine ⟨Edge.mk (part.1.idxOf globalEdge.tail) (part.1.idxOf globalEdge.head)
      globalEdge.minLen globalEdge.decl globalEdge.reversed, ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨globalEdge, List.mem_filter.mpr
      ⟨hglobalEdge, List.contains_iff_mem.mpr htailPart⟩, rfl⟩
  rw [← componentCandidate_decls execution.graph part.1 candidate] at hrawDecl
  obtain ⟨edge, hedgeMember, hedgeDecl⟩ := List.mem_map.mp hrawDecl
  obtain ⟨i, hedge⟩ := List.mem_iff_getElem?.mp hedgeMember
  obtain ⟨packed, hpacked, _⟩ := packAcc_components_disjoint execution.packed_eq
  obtain ⟨c, hpartIndex⟩ := List.mem_iff_getElem?.mp hpartMember
  have hc := (List.getElem?_eq_some_iff.mp hpartIndex).1
  have hpackedCount : packed.boxes.length = execution.componentsAcc.parts.length := by
    simpa only [List.length_map] using Pack.pack_count hpacked
  have hpositionBound : c < packed.boxes.length := by omega
  let position := packed.boxes[c]'hpositionBound
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
      some (part, position) := List.getElem?_zip_eq_some.mpr
    ⟨hpartIndex, List.getElem?_eq_getElem hpositionBound⟩
  exact ⟨packed, c, (part, position), candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hedgeDecl.trans hglobalDecl⟩

private theorem input_node_role_of_id
    {inp : Input} (hids : (inp.boxes.map (·.id)).Nodup)
    {box : ModelBox} (hbox : box ∈ inp.boxes) {id : String} (hid : box.id = id)
    (hordinary : ∃ source ∈ inp.boxes, source.id = id ∧ source.role = .node) :
    box.role = .node := by
  obtain ⟨source, hsource, hsourceId, hrole⟩ := hordinary
  have hboxLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes
    hids box hbox
  have hsourceLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes
    hids source hsource
  have heqId : box.id = source.id := hid.trans hsourceId.symm
  rw [heqId] at hboxLookup
  have heq : box = source := Option.some.inj (hboxLookup.symm.trans hsourceLookup)
  rw [heq]
  exact hrole

private theorem input_effective_role_of_id
    {inp : Input} (hids : (inp.boxes.map (·.id)).Nodup)
    {box : ModelBox} (hbox : box ∈ inp.boxes) {id : String} (hid : box.id = id)
    (heffective : ∃ source ∈ inp.boxes, source.id = id ∧
      (source.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true)) :
    box.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true := by
  obtain ⟨source, hsource, hsourceId, hrole | hfixed⟩ := heffective
  · exact Or.inl (input_node_role_of_id hids hbox hid ⟨source, hsource, hsourceId, hrole⟩)
  · right
    simpa only [hid, hsourceId] using hfixed

theorem SceneExecution.effective_routes_c5_of_box_ids_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hne : out.fromId ≠ out.toId)
    (hfrom : ∃ source ∈ inp.boxes, source.id = out.fromId ∧
      (source.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true))
    (hto : ∃ target ∈ inp.boxes, target.id = out.toId ∧
      (target.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == target.id) = true)) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  obtain ⟨key, houtIndex⟩ := List.mem_iff_getElem?.mp hout
  have hlength : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    simp only [sceneOf, List.length_map, List.length_zipIdx]
  have hkey : key < inp.routes.length := by
    rw [← hlength]
    exact (List.getElem?_eq_some_iff.mp houtIndex).1
  let modelRoute := inp.routes[key]'hkey
  have hmodel : inp.routes[key]? = some modelRoute := List.getElem?_eq_getElem hkey
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.straightAcc execution.measured key hkey
  rw [← execution.scene_eq] at hscene
  have houtRecord := Option.some.inj (houtIndex.symm.trans hscene)
  have hfromId : out.fromId = modelRoute.fromId := congrArg Route.fromId houtRecord
  have htoId : out.toId = modelRoute.toId := congrArg Route.toId houtRecord
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_source hkey
  obtain ⟨index, route, raw, source, target, hroute, hdeclIndex,
    hsource, hsourceId, htarget, htargetId, hkeys⟩ :=
    componentCandidate_effective_node_model_keys execution.graph_eq hrun hedge
  have hindex : index = key := hdeclIndex.symm.trans hdecl
  rw [hindex] at hroute
  have hrouteEq : route = modelRoute := Option.some.inj (hroute.symm.trans hmodel)
  subst route
  have hs := input_effective_role_of_id hids (List.mem_of_getElem? hsource)
    (hsourceId.trans hfromId.symm) hfrom
  have ht := input_effective_role_of_id hids (List.mem_of_getElem? htarget)
    (htargetId.trans htoId.symm) hto
  have hedgeNonself : edge.tail ≠ edge.head := by
    intro hself
    obtain ⟨hfromKey, htoKey⟩ := hkeys hs ht
    simp only [hself, ite_self] at hfromKey htoKey
    have hraw : raw.tail = raw.head := Option.some.inj (hfromKey.symm.trans htoKey)
    have hsource' := hsource
    rw [hraw] at hsource'
    have heq : source = target := Option.some.inj (hsource'.symm.trans htarget)
    apply hne
    calc
      out.fromId = source.id := hfromId.trans hsourceId.symm
      _ = target.id := congrArg ModelBox.id heq
      _ = out.toId := htargetId.trans htoId.symm
  obtain ⟨route', raw', source', target', hroute', hsource', hsourceId',
    htarget', htargetId', hports⟩ :=
    execution.chosen_part_effective_c5_of_box_ids_nodup hids packed hpacked hselected hrun hloops hpart
      hedge hedgeNonself
  rw [hdecl] at hroute'
  have hrouteEq' : route' = modelRoute := Option.some.inj (hroute'.symm.trans hmodel)
  subst route'
  have hs' := input_effective_role_of_id hids (List.mem_of_getElem? hsource')
    (hsourceId'.trans hfromId.symm) hfrom
  have ht' := input_effective_role_of_id hids (List.mem_of_getElem? htarget')
    (htargetId'.trans htoId.symm) hto
  obtain ⟨emitted, start, finish, fromBox, toBox, hemitted,
    hstart, hfinish, hfromLookup, htoLookup, hfromBoundary, htoBoundary⟩ := hports hs' ht'
  rw [hdecl] at hemitted
  have heqOut : emitted = out := Option.some.inj (hemitted.symm.trans houtIndex)
  subst emitted
  exact ⟨start, finish, fromBox, toBox, hstart, hfinish,
    hfromLookup, htoLookup, hfromBoundary, htoBoundary⟩

theorem SceneExecution.ordinary_routes_c5_of_box_ids_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hne : out.fromId ≠ out.toId)
    (hfrom : ∃ source ∈ inp.boxes, source.id = out.fromId ∧ source.role = .node)
    (hto : ∃ target ∈ inp.boxes, target.id = out.toId ∧ target.role = .node) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  obtain ⟨source, hsource, hsId, hs⟩ := hfrom
  obtain ⟨target, htarget, htId, ht⟩ := hto
  exact execution.effective_routes_c5_of_box_ids_nodup hids hout hne
    ⟨source, hsource, hsId, Or.inl hs⟩ ⟨target, htarget, htId, Or.inl ht⟩

theorem SceneExecution.ordinary_routes_c5
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {out : Route} (hout : out ∈ res.scene.routes)
    (hne : out.fromId ≠ out.toId)
    (hfrom : ∃ source ∈ inp.boxes, source.id = out.fromId ∧ source.role = .node)
    (hto : ∃ target ∈ inp.boxes, target.id = out.toId ∧ target.role = .node) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect :=
  execution.ordinary_routes_c5_of_box_ids_nodup
    (Model.boxIds_nodup hwf) hout hne hfrom hto

theorem SceneExecution.ordinary_self_routes_c5_of_box_ids_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hselfId : out.fromId = out.toId)
    (hfrom : ∃ source ∈ inp.boxes, source.id = out.fromId ∧ source.role = .node) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  obtain ⟨key, houtIndex⟩ := List.mem_iff_getElem?.mp hout
  have hlength : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    simp only [sceneOf, List.length_map, List.length_zipIdx]
  have hkey : key < inp.routes.length := by
    rw [← hlength]
    exact (List.getElem?_eq_some_iff.mp houtIndex).1
  let modelRoute := inp.routes[key]'hkey
  have hmodel : inp.routes[key]? = some modelRoute := List.getElem?_eq_getElem hkey
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.straightAcc execution.measured key hkey
  rw [← execution.scene_eq] at hscene
  have houtRecord := Option.some.inj (houtIndex.symm.trans hscene)
  have hfromId : out.fromId = modelRoute.fromId := congrArg Route.fromId houtRecord
  have htoId : out.toId = modelRoute.toId := congrArg Route.toId houtRecord
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_source hkey
  obtain ⟨index, route, raw, source, target, hroute, hdeclIndex,
    hsource, hsourceId, htarget, htargetId, hkeys⟩ :=
    componentCandidate_ordinary_model_keys execution.graph_eq hrun hedge
  have hindex : index = key := hdeclIndex.symm.trans hdecl
  rw [hindex] at hroute
  have hrouteEq : route = modelRoute := Option.some.inj (hroute.symm.trans hmodel)
  subst route
  have hs : source.role = .node := input_node_role_of_id hids
    (List.mem_of_getElem? hsource) (hsourceId.trans hfromId.symm) hfrom
  have ht : target.role = .node := input_node_role_of_id hids
    (List.mem_of_getElem? htarget) (htargetId.trans htoId.symm)
    (by simpa only [← hselfId] using hfrom)
  by_cases hself : edge.tail = edge.head
  · let cg := componentCandidate execution.graph q.1.1 candidate
    obtain ⟨hfromKey, htoKey⟩ := hkeys hs ht
    simp only [← hself, ite_self] at hfromKey htoKey
    have hv : edge.tail < cg.nodes.length := by
      rw [componentCandidate_nodes]
      simpa only [componentGraph, List.length_map] using
        (List.getElem?_eq_some_iff.mp hfromKey).1
    obtain ⟨native, hnative, _, hnativeDecl, hemitted⟩ :=
      componentLoops_emitted_self_edge hloops hedge hv hself 0
    have hpartRoutes : q.1.2.routes =
        (placeComponent execution.params cg run 0 execution.measured loops).routes := by
      rw [hpart]
    rw [← hpartRoutes] at hemitted
    have hnd : (cg.edges.map (·.decl)).Nodup :=
      componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
    have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
      rw [hpartRoutes]
      exact placeComponent_routes_decls_nodup execution.params cg run 0 execution.measured loops hnd
    have hsize : execution.componentsAcc.routes.size = inp.routes.length := by
      have h := components_fold_routes_size execution.params inp o execution.graph
        execution.measured _ _ _ execution.components_eq
      simpa only [Array.size_replicate] using h
    have hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
      rw [hsize, hdecl]
      exact hkey
    have hpackedRoute := Elegant.Layered.actual_components_packAcc_routes_getD
      (by rfl) execution.components_eq (measuredGraph_decls_nodup execution.graph_eq)
      packed execution.packed_eq hpacked c q hselected i _ _ [] hemitted hpartNodup hrouteSize
    obtain ⟨hparts, _⟩ := actual_components_parts (by rfl) execution.components_eq
    have hcomponent : q.1.1 ∈ components execution.graph := by
      rw [← hparts]
      exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
    obtain ⟨v, hvComponent, placements, origin, horigin, horiginDecl,
      horiginTail, _, hattachment⟩ :=
      execution.componentLoops_ordinary_attachment q.1.1 hcomponent candidate hrun hloops hnative
        execution.params.canvasMargin o.direction execution.packedAcc.canvasH q.2.x q.2.y
    have horiginMem : origin ∈ cg.edges :=
      (List.mem_filter.mp (show origin ∈ loopEdges cg.edges v from
        (List.of_mem_zip horigin).1)).1
    have horiginEq : origin = edge := nodup_map_eq_of_mem hnd horiginMem
      (List.mem_of_getElem? hedge) (horiginDecl.symm.trans hnativeDecl)
    have hvEq : v = edge.tail := horiginTail.symm.trans (congrArg Edge.tail horiginEq)
    have hsourceAt : inp.boxes[q.1.1[v]]? = some source := by
      have hkeyAt : q.1.1[v]? = some raw.tail := by rw [hvEq]; exact hfromKey
      have heq : q.1.1[v] = raw.tail :=
        Option.some.inj ((List.getElem?_eq_getElem hvComponent).symm.trans hkeyAt)
      rw [heq]
      exact hsource
    obtain ⟨start, finish, hstart, hfinish, hboundary⟩ := hattachment source hsourceAt hs
    have hentry := chosen_part_frame_entry hpart
      (show q.1.1[v]? = some raw.tail by rw [hvEq]; exact hfromKey)
    have hlookup := execution.part_entry_box_lookup_of_box_ids_nodup hids
      packed hpacked hselected hentry hsource
    dsimp only at hlookup hboundary
    rw [shiftRect_pack_normalize] at hlookup
    let bounds := placeBounds execution.params cg run execution.measured loops
    let transport := routePointTransport execution.params.canvasMargin o.direction
      execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
    have houtPoints : out.points = native.2.points.map transport := by
      have hsizeS : edge.decl < execution.straightAcc.routes.size := by
        have hpb := execution.packedAcc_bounded execution.components_parts_bounded
        obtain ⟨_, _, _, _, _, hsz, _⟩ :=
          straightenAcc_bounded execution.straight_eq hpb.routes_bounded
        have hpsize : execution.packedAcc.routes.size = inp.routes.length := by
          rw [Elegant.Layered.packAcc_routes_size execution.packed_eq, hsize]
        rw [hdecl, hsz, hpsize]
        exact hkey
      have hgetS : execution.straightAcc.routes[edge.decl]? =
          some (execution.straightAcc.routes.getD edge.decl []) := by
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsizeS, Option.getD_some]
      rcases execution.route_cases hgetS with hpackedS | hinst
      · have hbridge : execution.packedAcc.routes.getD edge.decl [] =
            execution.straightAcc.routes.getD edge.decl [] := by
          simp only [Array.getD_eq_getD_getElem?, hpackedS, Option.getD_some]
        have hpoints := congrArg Route.points houtRecord
        dsimp only at hpoints
        rw [← hdecl, ← hbridge, hpackedRoute, execution.straight_canvasH,
          routePointTransport_eq] at hpoints
        exact hpoints
      · exfalso
        have hrouteKey : inp.routes[edge.decl]? = some modelRoute := by
          rw [hdecl]
          exact hmodel
        have hne := execution.installed_route_ends hinst hrouteKey
        have hneOut : out.fromId ≠ out.toId := by
          rw [hfromId, htoId]
          exact hne
        exact absurd hselfId hneOut
    let box := Box.mk source.id source.role.id
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY)
            (frameRect execution.params cg run v)))) source.parent source.exclusive
    refine ⟨transport start, transport finish, box, box, ?_, ?_, ?_, ?_,
      hboundary.1, hboundary.2⟩
    · rw [houtPoints, List.head?_map, hstart]
      rfl
    · rw [houtPoints, List.getLast?_map, hfinish]
      rfl
    · rw [hfromId, ← hsourceId]
      exact hlookup
    · rw [← hselfId, hfromId, ← hsourceId]
      exact hlookup
  · obtain ⟨route', raw', source', target', hroute', hsource', hsourceId',
      htarget', htargetId', hports⟩ :=
      execution.chosen_part_ordinary_c5_of_box_ids_nodup hids packed hpacked hselected
        hrun hloops hpart hedge hself
    rw [hdecl] at hroute'
    have heqRoute : route' = modelRoute := Option.some.inj (hroute'.symm.trans hmodel)
    subst route'
    have hs' := input_node_role_of_id hids (List.mem_of_getElem? hsource')
      (hsourceId'.trans hfromId.symm) hfrom
    have ht' := input_node_role_of_id hids (List.mem_of_getElem? htarget')
      (htargetId'.trans htoId.symm) (by simpa only [← hselfId] using hfrom)
    obtain ⟨emitted, start, finish, fromBox, toBox, hemitted, hstart, hfinish,
      hfromLookup, htoLookup, hfromBoundary, htoBoundary⟩ := hports hs' ht'
    rw [hdecl] at hemitted
    have heqOut : emitted = out := Option.some.inj (hemitted.symm.trans houtIndex)
    subst emitted
    exact ⟨start, finish, fromBox, toBox, hstart, hfinish,
      hfromLookup, htoLookup, hfromBoundary, htoBoundary⟩

theorem SceneExecution.self_routes_c5_of_box_ids_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hselfId : out.fromId = out.toId) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  obtain ⟨key, houtIndex⟩ := List.mem_iff_getElem?.mp hout
  have hlength : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    simp only [sceneOf, List.length_map, List.length_zipIdx]
  have hkey : key < inp.routes.length := by
    rw [← hlength]
    exact (List.getElem?_eq_some_iff.mp houtIndex).1
  let modelRoute := inp.routes[key]'hkey
  have hmodel : inp.routes[key]? = some modelRoute := List.getElem?_eq_getElem hkey
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.straightAcc execution.measured key hkey
  rw [← execution.scene_eq] at hscene
  have houtRecord := Option.some.inj (houtIndex.symm.trans hscene)
  have hfromId : out.fromId = modelRoute.fromId := congrArg Route.fromId houtRecord
  have htoId : out.toId = modelRoute.toId := congrArg Route.toId houtRecord
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_source hkey
  obtain ⟨index, route, raw, source, hroute, hdeclIndex,
    hsource, hsourceId, hkeys⟩ :=
    componentCandidate_self_model_key execution.graph_eq hrun hedge
  have hindex : index = key := hdeclIndex.symm.trans hdecl
  rw [hindex] at hroute
  have hrouteEq : route = modelRoute := Option.some.inj (hroute.symm.trans hmodel)
  subst route
  obtain ⟨hself, hfromKey⟩ := hkeys (hfromId.symm.trans (hselfId.trans htoId))
  cases hrole : source.role with
  | node =>
    exact execution.ordinary_self_routes_c5_of_box_ids_nodup hids hout hselfId
      ⟨source, List.mem_of_getElem? hsource, hsourceId.trans hfromId.symm, hrole⟩
  | group =>
    let cg := componentCandidate execution.graph q.1.1 candidate
    obtain ⟨hparts, _⟩ := actual_components_parts (by rfl) execution.components_eq
    have hcomponent : q.1.1 ∈ components execution.graph := by
      rw [← hparts]
      exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
    have hsourceAt : inp.boxes[q.1.1.getD edge.tail 0]? = some source := by
      simpa only [List.getD_eq_getElem?_getD, hfromKey, Option.getD_some] using hsource
    obtain ⟨native, _, _, _, hemitted, start, finish, hstart, hfinish, hsb, htb⟩ :=
      execution.componentLoops_group_emitted_attachment q.1.1 hcomponent candidate
        hrun hloops hedge hself hsourceAt hrole
    let bounds := placeBounds execution.params cg run execution.measured loops
    let points := native.2.points.map (shiftPoint (0 - bounds.minX) (0 - bounds.minY))
    let rect := shiftRect (0 - bounds.minX) (0 - bounds.minY)
      (frameRect execution.params cg run edge.tail)
    have hpartRoutes : q.1.2.routes =
        (placeComponent execution.params cg run 0 execution.measured loops).routes := by
      rw [hpart]
    rw [← hpartRoutes] at hemitted
    have hnd : (cg.edges.map (·.decl)).Nodup :=
      componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
    have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
      rw [hpartRoutes]
      exact placeComponent_routes_decls_nodup execution.params cg run 0 execution.measured loops hnd
    have hsize : execution.componentsAcc.routes.size = inp.routes.length := by
      have h := components_fold_routes_size execution.params inp o execution.graph
        execution.measured _ _ _ execution.components_eq
      simpa only [Array.size_replicate] using h
    have hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
      rw [hsize, hdecl]
      exact hkey
    have hpackedRoute := Elegant.Layered.actual_components_packAcc_routes_getD
      (by rfl) execution.components_eq (measuredGraph_decls_nodup execution.graph_eq)
      packed execution.packed_eq hpacked c q hselected i _ _ [] hemitted hpartNodup hrouteSize
    have hentry := chosen_part_frame_entry hpart hfromKey
    have hlookup := execution.part_entry_box_lookup_of_box_ids_nodup hids
      packed hpacked hselected hentry hsource
    let transport := fun p => shiftPoint execution.params.canvasMargin execution.params.canvasMargin
      (orientPoint o.direction execution.packedAcc.canvasH (shiftPoint q.2.x q.2.y p))
    have houtPoints : out.points = points.map transport := by
      have hsizeS : edge.decl < execution.straightAcc.routes.size := by
        have hpb := execution.packedAcc_bounded execution.components_parts_bounded
        obtain ⟨_, _, _, _, _, hsz, _⟩ :=
          straightenAcc_bounded execution.straight_eq hpb.routes_bounded
        have hpsize : execution.packedAcc.routes.size = inp.routes.length := by
          rw [Elegant.Layered.packAcc_routes_size execution.packed_eq, hsize]
        rw [hdecl, hsz, hpsize]
        exact hkey
      have hgetS : execution.straightAcc.routes[edge.decl]? =
          some (execution.straightAcc.routes.getD edge.decl []) := by
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsizeS, Option.getD_some]
      rcases execution.route_cases hgetS with hpackedS | hinst
      · have hbridge : execution.packedAcc.routes.getD edge.decl [] =
            execution.straightAcc.routes.getD edge.decl [] := by
          simp only [Array.getD_eq_getD_getElem?, hpackedS, Option.getD_some]
        have hpoints := congrArg Route.points houtRecord
        dsimp only at hpoints
        rw [← hdecl, ← hbridge, hpackedRoute, execution.straight_canvasH] at hpoints
        simpa only [List.map_map, Function.comp_def, points, bounds, cg, transport] using hpoints
      · exfalso
        have hrouteKey : inp.routes[edge.decl]? = some modelRoute := by
          rw [hdecl]
          exact hroute
        have hne := execution.installed_route_ends hinst hrouteKey
        have hneOut : out.fromId ≠ out.toId := by
          rw [hfromId, htoId]
          exact hne
        exact absurd hselfId hneOut
    let box := Box.mk source.id source.role.id
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH (shiftRect q.2.x q.2.y rect)))
      source.parent source.exclusive
    refine ⟨transport start, transport finish, box, box, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [houtPoints, List.head?_map, hstart]
      rfl
    · rw [houtPoints, List.getLast?_map, hfinish]
      rfl
    · rw [hfromId, ← hsourceId]
      exact hlookup
    · rw [← hselfId, hfromId, ← hsourceId]
      exact hlookup
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsb
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htb

theorem SceneExecution.effective_endpoint_c5
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hfrom : ∃ source ∈ inp.boxes, source.id = out.fromId ∧
      (source.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true))
    (hto : ∃ target ∈ inp.boxes, target.id = out.toId ∧
      (target.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == target.id) = true)) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  by_cases hself : out.fromId = out.toId
  · exact execution.self_routes_c5_of_box_ids_nodup hids hout hself
  · exact execution.effective_routes_c5_of_box_ids_nodup hids hout hself hfrom hto

theorem SceneExecution.ordinary_endpoint_c5
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hfrom : ∃ source ∈ inp.boxes, source.id = out.fromId ∧ source.role = .node)
    (hto : ∃ target ∈ inp.boxes, target.id = out.toId ∧ target.role = .node) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  by_cases hself : out.fromId = out.toId
  · exact execution.ordinary_self_routes_c5_of_box_ids_nodup hids hout hself hfrom
  · exact execution.ordinary_routes_c5_of_box_ids_nodup hids hout hself hfrom hto

theorem expandChild_assembly_sources
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group titleHeight parent child = .ok res) :
    ∃ (frame : Box) (metric : Measure.Metric) (titleLines : List Measure.Line)
      (lines : List (List Measure.Line)) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame ∧
      metricOf o.profile = .ok metric ∧
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines ∧
      boxLines metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        inp = .ok lines ∧
      let titleWidth := titleLines.foldl (fun width line => max width line.width) 0
      let inset := childInset group.direction P.clusterPad titleWidth titleHeight
      dx = frame.rect.x + inset.x - P.canvasMargin ∧
      dy = frame.rect.y + inset.y - P.canvasMargin ∧
      res.scene.boxes = inp.boxes.filterMap (fun model =>
        ((child.scene.boxes.map fun (box : Box) => { box with
          rect := shiftRect dx dy box.rect,
          parent := if box.parent == "" then group.id else box.parent }) ++
          parent.scene.boxes).find? (fun box => box.id == model.id)) ∧
      res.scene.routes = inp.routes.filterMap (fun model =>
        ((child.scene.routes.map fun (route : Route) =>
          { route with points := route.points.map (shiftPoint dx dy) }) ++
          parent.scene.routes).find? (fun route => route.id == model.id)) ∧
      res.scene.items = applyTitles
        ((group.id, childTitleRect group.direction P.clusterPad titleWidth titleHeight frame.rect) ::
          ((groupTitles child.scene.items).map (fun title => (title.1, shiftRect dx dy title.2)) ++
            groupTitles parent.scene.items))
        (sceneItems P inp res.scene.boxes res.scene.routes lines res.scene.labels) := by
  unfold expandChild at h
  cases hframe : parent.scene.boxes.find? (fun box => box.id == group.id) with
  | none =>
    simp only [hframe] at h
    contradiction
  | some frame =>
    simp only [hframe] at h
    obtain ⟨frame', hframe', h⟩ := bind_ok h
    have heframe : frame = frame' := Except.ok.inj hframe'
    subst frame'
    obtain ⟨metric, hmetric, h⟩ := bind_ok h
    obtain ⟨titleLines, htitle, h⟩ := bind_ok h
    obtain ⟨itemMetric, hitemMetric, h⟩ := bind_ok h
    have hemetric : itemMetric = metric := Except.ok.inj (hitemMetric.symm.trans hmetric)
    subst itemMetric
    obtain ⟨lines, hlines, h⟩ := bind_ok h
    have he := Except.ok.inj h
    subst res
    let inset := childInset group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
    exact ⟨frame, metric, titleLines, lines,
      frame.rect.x + inset.x - P.canvasMargin,
      frame.rect.y + inset.y - P.canvasMargin,
      rfl, hmetric, htitle, hlines, rfl, rfl, rfl, rfl, rfl⟩

theorem expandChild_port_assembly
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group titleHeight parent child = .ok res) :
    ∃ dx dy : Int,
      res.scene.boxes = inp.boxes.filterMap (fun model =>
        ((child.scene.boxes.map fun (box : Box) => { box with
          rect := shiftRect dx dy box.rect,
          parent := if box.parent == "" then group.id else box.parent }) ++
          parent.scene.boxes).find? (fun box => box.id == model.id)) ∧
      res.scene.routes = inp.routes.filterMap (fun model =>
        ((child.scene.routes.map fun (route : Route) =>
          { route with points := route.points.map (shiftPoint dx dy) }) ++
          parent.scene.routes).find? (fun route => route.id == model.id)) := by
  obtain ⟨_, _, _, _, dx, dy, _, _, _, _, _, _, hboxes, hroutes, _⟩ :=
    expandChild_assembly_sources h
  exact ⟨dx, dy, hboxes, hroutes⟩

private theorem input_routes_covered
    {inp : Input} {o : Options} (hwf : WellFormed (inputModel inp o)) :
    RoutesCovered inp := by
  unfold WellFormed modelWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hroutes⟩, _⟩, _⟩ := hwf
  intro route hroute
  have h := List.all_eq_true.mp hroutes route hroute
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.mem_map] at h
  exact h

theorem recursive_selected_box_ids_disjoint
    {fuel : Nat} {inp : Input} {o childOptions : Options} {group : ModelBox}
    {child parent : FamilyResult}
    {sizes : List (String × Size)} {children : List (String × Scene)}
    {areas : List (String × Int)}
    (hchild : layoutRecursive fuel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      childOptions = .ok child)
    (hparent : layoutRecursive fuel
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent) :
    ∀ id ∈ child.scene.boxes.map (·.id), id ∉ parent.scene.boxes.map (·.id) := by
  have hc := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    (selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
  have hparentCoverage : RoutesCovered
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
    selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hp := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hparentCoverage hparent
  have hcIds := hc.1
  have hpIds := hp.1
  change parent.scene.boxes.map (·.id) =
    (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).boxes.map
      (·.id) at hpIds
  rw [selectInput_box_ids] at hcIds hpIds
  intro id hidChild hidParent
  rw [hcIds] at hidChild
  rw [hpIds] at hidParent
  obtain ⟨childBox, hchildBox, hchildId⟩ := List.mem_map.mp hidChild
  obtain ⟨parentBox, hparentBox, hparentId⟩ := List.mem_map.mp hidParent
  have hinside := (List.mem_filter.mp hchildBox).2
  have houtside := (List.mem_filter.mp hparentBox).2
  have heqId : childBox.id = parentBox.id := hchildId.trans hparentId.symm
  rw [heqId] at hinside
  simp only [hinside, Bool.not_true, Bool.false_eq_true] at houtside

theorem layoutRecursive_embedding_assembly_sources
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hboxIds : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (P : Params) (metric : Measure.Metric) (child : FamilyResult)
      (titleLines : List Measure.Line) (parent : FamilyResult) (frame : Box)
      (lines : List (List Measure.Line)) (dx dy : Int),
      checkedParams o.profile inp.kind = .ok P ∧
      metricOf o.profile = .ok metric ∧
      layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child ∧
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines ∧
      let titleWidth := titleLines.foldl (fun width line => max width line.width) 0
      let titleHeight := (max 1 titleLines.length : Int) * P.lineH
      let size := childFrameSize group.direction P.clusterPad titleWidth titleHeight
        ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩
      let parentInput := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
      layoutRecursive fuel
        { parentInput with
          fixedSizes := parentInput.fixedSizes ++ [(group.id, size)]
          fixedChildren := parentInput.fixedChildren ++ [(group.id, child.scene)]
          fixedAreas := parentInput.fixedAreas ++ [(group.id, child.itemArea)] } o = .ok parent ∧
      expandChild P inp o group titleHeight parent child = .ok res ∧
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame ∧
      boxLines metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        inp = .ok lines ∧
      let inset := childInset group.direction P.clusterPad titleWidth titleHeight
      dx = frame.rect.x + inset.x - P.canvasMargin ∧
      dy = frame.rect.y + inset.y - P.canvasMargin ∧
      (∀ box : Box, child.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id =
          some { box with rect := shiftRect dx dy box.rect, parent := if box.parent == "" then group.id else box.parent }) ∧
      (∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id = some box) ∧
      res.scene.routes = inp.routes.filterMap (fun model =>
        ((child.scene.routes.map fun (route : Route) =>
          { route with points := route.points.map (shiftPoint dx dy) }) ++
          parent.scene.routes).find? (fun route => route.id == model.id)) ∧
      res.scene.items = applyTitles
        ((group.id, childTitleRect group.direction P.clusterPad titleWidth titleHeight frame.rect) ::
          ((groupTitles child.scene.items).map (fun title => (title.1, shiftRect dx dy title.2)) ++
            groupTitles parent.scene.items))
        (sceneItems P inp res.scene.boxes res.scene.routes lines res.scene.labels) := by
  rcases layoutRecursive_succ_sources hrecursive with ⟨hnone, _⟩ |
    ⟨found, P, metric, child, titleLines, parent, hfound, hP, hm,
      hchild, hwrap, hparent, hexpand⟩
  · rw [hgroup] at hnone
    contradiction
  · have hsame : found = group := Option.some.inj (hfound.symm.trans hgroup)
    subst found
    let titleWidth := titleLines.foldl (fun width line => max width line.width) 0
    let titleHeight := (max 1 titleLines.length : Int) * P.lineH
    let size := childFrameSize group.direction P.clusterPad titleWidth titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩
    let parentInput := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
    let sizes := parentInput.fixedSizes ++ [(group.id, size)]
    let children := parentInput.fixedChildren ++ [(group.id, child.scene)]
    let areas := parentInput.fixedAreas ++ [(group.id, child.itemArea)]
    have hc := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
      (selectInput_routesCovered inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
    have hparentCoverage : RoutesCovered
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
      selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
    have hp := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
      hparentCoverage hparent
    have hcIds := hc.1
    have hpIds := hp.1
    change parent.scene.boxes.map (·.id) =
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).boxes.map
        (·.id) at hpIds
    have hresultIds := (layoutRecursive_ids (fun _ _ _ hl => layout_ids hl)
      (fuel + 1) inp o res hcovered hrecursive).1
    have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
      rw [hresultIds]
      exact hboxIds
    have hdisjoint := recursive_selected_box_ids_disjoint hchild hparent
    obtain ⟨frame, expansionMetric, expansionLines, lines, dx, dy,
        hframe, hmetric, htitle, hlines, hdx, hdy, hboxes, hroutes, hitems⟩ :=
      expandChild_assembly_sources hexpand
    have hemetric : expansionMetric = metric := Except.ok.inj (hmetric.symm.trans hm)
    subst expansionMetric
    have hetitle : expansionLines = titleLines := Except.ok.inj (htitle.symm.trans hwrap)
    subst expansionLines
    let embed := fun box : Box => { box with rect := shiftRect dx dy box.rect, parent := if box.parent == "" then group.id else box.parent }
    change res.scene.boxes = inp.boxes.filterMap (fun model =>
      (child.scene.boxes.map embed ++ parent.scene.boxes).find?
        (fun box => box.id == model.id)) at hboxes
    refine ⟨P, metric, child, titleLines, parent, frame, lines, dx, dy,
      hP, hm, hchild, hwrap, hparent, hexpand, hframe, hlines, hdx, hdy,
      ?_, ?_, hroutes, hitems⟩
    · intro box hbox
      change child.scene.boxes.find? (fun candidate => candidate.id == box.id) = some box at hbox
      have hmember : box ∈ child.scene.boxes := List.mem_of_find?_eq_some hbox
      have hid : box.id ∈ child.scene.boxes.map (·.id) := List.mem_map_of_mem hmember
      rw [hcIds, selectInput_box_ids] at hid
      obtain ⟨model, hmodelFilter, hmodelId⟩ := List.mem_map.mp hid
      have hmodel := (List.mem_filter.mp hmodelFilter).1
      have hfind : (child.scene.boxes.map embed ++ parent.scene.boxes).find?
          (fun candidate => candidate.id == box.id) = some (embed box) := by
        simp [List.find?_append, embed, Function.comp_def, hbox]
      have hemitted : embed box ∈ res.scene.boxes := by
        rw [hboxes]
        apply List.mem_filterMap.mpr
        refine ⟨model, hmodel, ?_⟩
        rw [hmodelId]
        exact hfind
      change res.scene.boxes.find? (fun candidate => candidate.id == box.id) = some (embed box)
      exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hnodup (embed box) hemitted
    · intro box hbox
      change parent.scene.boxes.find? (fun candidate => candidate.id == box.id) = some box at hbox
      have hmember : box ∈ parent.scene.boxes := List.mem_of_find?_eq_some hbox
      have hid : box.id ∈ parent.scene.boxes.map (·.id) := List.mem_map_of_mem hmember
      rw [hpIds, selectInput_box_ids] at hid
      obtain ⟨model, hmodelFilter, hmodelId⟩ := List.mem_map.mp hid
      have hmodel := (List.mem_filter.mp hmodelFilter).1
      have hnone : (child.scene.boxes.map embed).find?
          (fun candidate => candidate.id == box.id) = none := by
        apply List.find?_eq_none.mpr
        intro candidate hcandidate
        obtain ⟨native, hnative, rfl⟩ := List.mem_map.mp hcandidate
        intro htest
        have heq : native.id = box.id := beq_iff_eq.mp htest
        have hchildId : native.id ∈ child.scene.boxes.map (·.id) := List.mem_map_of_mem hnative
        have hparentId : native.id ∈ parent.scene.boxes.map (·.id) := by
          rw [heq]
          exact List.mem_map_of_mem hmember
        exact hdisjoint native.id hchildId hparentId
      have hfind : (child.scene.boxes.map embed ++ parent.scene.boxes).find?
          (fun candidate => candidate.id == box.id) = some box := by
        simp [List.find?_append, hnone, hbox]
      have hemitted : box ∈ res.scene.boxes := by
        rw [hboxes]
        apply List.mem_filterMap.mpr
        refine ⟨model, hmodel, ?_⟩
        rw [hmodelId]
        exact hfind
      change res.scene.boxes.find? (fun candidate => candidate.id == box.id) = some box
      exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hnodup box hemitted

theorem layoutRecursive_embedding_box_lookup_sources
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hboxIds : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (P : Params) (metric : Measure.Metric) (child : FamilyResult)
      (titleLines : List Measure.Line) (parent : FamilyResult) (dx dy : Int),
      checkedParams o.profile inp.kind = .ok P ∧
      metricOf o.profile = .ok metric ∧
      layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child ∧
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines ∧
      let titleWidth := titleLines.foldl (fun width line => max width line.width) 0
      let titleHeight := (max 1 titleLines.length : Int) * P.lineH
      let size := childFrameSize group.direction P.clusterPad titleWidth titleHeight
        ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩
      let parentInput := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
      layoutRecursive fuel
        { parentInput with
          fixedSizes := parentInput.fixedSizes ++ [(group.id, size)]
          fixedChildren := parentInput.fixedChildren ++ [(group.id, child.scene)]
          fixedAreas := parentInput.fixedAreas ++ [(group.id, child.itemArea)] } o = .ok parent ∧
      expandChild P inp o group titleHeight parent child = .ok res ∧
      (∀ box : Box, child.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id =
          some { box with rect := shiftRect dx dy box.rect, parent := if box.parent == "" then group.id else box.parent }) ∧
      (∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id = some box) ∧
      res.scene.routes = inp.routes.filterMap (fun model =>
        ((child.scene.routes.map fun (route : Route) =>
          { route with points := route.points.map (shiftPoint dx dy) }) ++
          parent.scene.routes).find? (fun route => route.id == model.id)) := by
  obtain ⟨P, metric, child, titleLines, parent, frame, lines, dx, dy,
      hP, hm, hchild, hwrap, hparent, hexpand, _, _, _, _,
      hchildLookup, hparentLookup, hroutes, _⟩ :=
    layoutRecursive_embedding_assembly_sources hboxIds hcovered hgroup hrecursive
  exact ⟨P, metric, child, titleLines, parent, dx, dy, hP, hm, hchild, hwrap,
    hparent, hexpand, hchildLookup, hparentLookup, hroutes⟩

theorem layoutRecursive_embedding_box_lookup_with_fixed_sizes
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hboxIds : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (P : Params) (titleHeight : Int) (child parent : FamilyResult)
      (sizes : List (String × Size)) (children : List (String × Scene))
      (areas : List (String × Int)) (dx dy : Int),
      inp.fixedSizes ⊆ sizes ∧
      layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child ∧
      layoutRecursive fuel
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent ∧
      expandChild P inp o group titleHeight parent child = .ok res ∧
      (∀ box : Box, child.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id =
          some { box with rect := shiftRect dx dy box.rect, parent := if box.parent == "" then group.id else box.parent }) ∧
      (∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id = some box) ∧
      res.scene.routes = inp.routes.filterMap (fun model =>
        ((child.scene.routes.map fun (route : Route) =>
          { route with points := route.points.map (shiftPoint dx dy) }) ++
          parent.scene.routes).find? (fun route => route.id == model.id)) := by
  obtain ⟨P, metric, child, titleLines, parent, dx, dy, _, _, hchild, _, hparent,
      hexpand, hchildLookup, hparentLookup, hroutes⟩ :=
    layoutRecursive_embedding_box_lookup_sources hboxIds hcovered hgroup hrecursive
  refine ⟨P, _, child, parent, _, _, _, dx, dy, ?_, hchild, hparent,
    hexpand, hchildLookup, hparentLookup, hroutes⟩
  intro fixed hf
  exact List.mem_append_left _ hf

theorem layoutRecursive_embedding_box_lookup_of_endpoint_invariants
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hboxIds : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (P : Params) (titleHeight : Int) (child parent : FamilyResult)
      (sizes : List (String × Size)) (children : List (String × Scene))
      (areas : List (String × Int)) (dx dy : Int),
      layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child ∧
      layoutRecursive fuel
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent ∧
      expandChild P inp o group titleHeight parent child = .ok res ∧
      (∀ box : Box, child.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id =
          some { box with rect := shiftRect dx dy box.rect, parent := if box.parent == "" then group.id else box.parent }) ∧
      (∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id = some box) ∧
      res.scene.routes = inp.routes.filterMap (fun model =>
        ((child.scene.routes.map fun (route : Route) =>
          { route with points := route.points.map (shiftPoint dx dy) }) ++
          parent.scene.routes).find? (fun route => route.id == model.id)) := by
  obtain ⟨P, height, child, parent, sizes, children, areas, dx, dy,
    _, hchild, hparent, hexpand, hchildLookup, hparentLookup, hroutes⟩ :=
    layoutRecursive_embedding_box_lookup_with_fixed_sizes hboxIds hcovered hgroup hrecursive
  exact ⟨P, height, child, parent, sizes, children, areas, dx, dy,
    hchild, hparent, hexpand, hchildLookup, hparentLookup, hroutes⟩

theorem layoutRecursive_embedding_box_lookup
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (P : Params) (titleHeight : Int) (child parent : FamilyResult)
      (sizes : List (String × Size)) (children : List (String × Scene))
      (areas : List (String × Int)) (dx dy : Int),
      layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child ∧
      layoutRecursive fuel
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent ∧
      expandChild P inp o group titleHeight parent child = .ok res ∧
      (∀ box : Box, child.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id =
          some { box with rect := shiftRect dx dy box.rect, parent := if box.parent == "" then group.id else box.parent }) ∧
      (∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
        res.scene.layoutDump.box? box.id = some box) ∧
      res.scene.routes = inp.routes.filterMap (fun model =>
        ((child.scene.routes.map fun (route : Route) =>
          { route with points := route.points.map (shiftPoint dx dy) }) ++
          parent.scene.routes).find? (fun route => route.id == model.id)) :=
  layoutRecursive_embedding_box_lookup_of_endpoint_invariants
    (Model.boxIds_nodup hwf) (input_routes_covered hwf) hgroup hrecursive

theorem layoutRecursive_child_ports_transport_of_endpoint_invariants
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hboxIds : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (child parent : FamilyResult) (P : Params) (height dx dy : Int),
      layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child ∧
      expandChild P inp o group height parent child = .ok res ∧
      ∀ (native : Route) (start finish : Point) (fromBox toBox : Box),
        child.scene.routes.find? (fun route => route.id == native.id) = some native →
        native.points.head? = some start → native.points.getLast? = some finish →
        child.scene.layoutDump.box? native.fromId = some fromBox →
        child.scene.layoutDump.box? native.toId = some toBox →
        Validator.onBoundary start fromBox.rect →
        Validator.onBoundary finish toBox.rect →
        let emitted := { native with points := native.points.map (shiftPoint dx dy) }
        emitted ∈ res.scene.routes ∧
          ∃ (fromBox' toBox' : Box),
            emitted.points.head? = some (shiftPoint dx dy start) ∧
            emitted.points.getLast? = some (shiftPoint dx dy finish) ∧
            res.scene.layoutDump.box? emitted.fromId = some fromBox' ∧
            res.scene.layoutDump.box? emitted.toId = some toBox' ∧
            Validator.onBoundary (shiftPoint dx dy start) fromBox'.rect ∧
            Validator.onBoundary (shiftPoint dx dy finish) toBox'.rect := by
  obtain ⟨P, height, child, parent, _, _, _, dx, dy,
    hchild, _, hexpand, hchildLookup, _, hroutes⟩ :=
    layoutRecursive_embedding_box_lookup_of_endpoint_invariants hboxIds hcovered hgroup hrecursive
  refine ⟨child, parent, P, height, dx, dy, hchild, hexpand, ?_⟩
  intro native start finish fromBox toBox hnative hstart hfinish hfrom hto hfromBoundary htoBoundary
  let emitted := { native with points := native.points.map (shiftPoint dx dy) }
  have hmember : native ∈ child.scene.routes := List.mem_of_find?_eq_some hnative
  have hrouteId : native.id ∈ child.scene.routes.map (·.id) := List.mem_map_of_mem hmember
  have hc := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    (selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
  rw [hc.2] at hrouteId
  obtain ⟨model, hmodelSelected, hmodelId⟩ := List.mem_map.mp hrouteId
  have hmodel := ((selectInput_route_mem inp
    (fun box => Compound.inside inp.boxes group.id box.id) group.id model).mp hmodelSelected).1
  have hfind : ((child.scene.routes.map fun (route : Route) =>
        { route with points := route.points.map (shiftPoint dx dy) }) ++
      parent.scene.routes).find? (fun route => route.id == native.id) = some emitted := by
    simp [List.find?_append, Function.comp_def, emitted, hnative]
  have hemitted : emitted ∈ res.scene.routes := by
    rw [hroutes]
    apply List.mem_filterMap.mpr
    refine ⟨model, hmodel, ?_⟩
    rw [hmodelId]
    exact hfind
  change child.scene.boxes.find? (fun box => box.id == native.fromId) = some fromBox at hfrom
  change child.scene.boxes.find? (fun box => box.id == native.toId) = some toBox at hto
  have hfromTest : (fromBox.id == native.fromId) = true :=
    List.find?_some (p := fun (box : Box) => box.id == native.fromId) hfrom
  have htoTest : (toBox.id == native.toId) = true :=
    List.find?_some (p := fun (box : Box) => box.id == native.toId) hto
  have hfromId : fromBox.id = native.fromId := beq_iff_eq.mp hfromTest
  have htoId : toBox.id = native.toId := beq_iff_eq.mp htoTest
  have hfromSelf : child.scene.layoutDump.box? fromBox.id = some fromBox := by
    rw [hfromId]
    exact hfrom
  have htoSelf : child.scene.layoutDump.box? toBox.id = some toBox := by
    rw [htoId]
    exact hto
  let fromBox' := { fromBox with rect := shiftRect dx dy fromBox.rect, parent := if fromBox.parent == "" then group.id else fromBox.parent }
  let toBox' := { toBox with rect := shiftRect dx dy toBox.rect, parent := if toBox.parent == "" then group.id else toBox.parent }
  refine ⟨hemitted, fromBox', toBox', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.head?_map, hstart, Option.map_some]
  · simp only [List.getLast?_map, hfinish, Option.map_some]
  · change res.scene.layoutDump.box? native.fromId = some fromBox'
    rw [← hfromId]
    exact hchildLookup fromBox hfromSelf
  · change res.scene.layoutDump.box? native.toId = some toBox'
    rw [← htoId]
    exact hchildLookup toBox htoSelf
  · exact (onBoundary_shift dx dy start fromBox.rect).mpr hfromBoundary
  · exact (onBoundary_shift dx dy finish toBox.rect).mpr htoBoundary

theorem layoutRecursive_child_ports_transport
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (child parent : FamilyResult) (P : Params) (height dx dy : Int),
      layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child ∧
      expandChild P inp o group height parent child = .ok res ∧
      ∀ (native : Route) (start finish : Point) (fromBox toBox : Box),
        child.scene.routes.find? (fun route => route.id == native.id) = some native →
        native.points.head? = some start → native.points.getLast? = some finish →
        child.scene.layoutDump.box? native.fromId = some fromBox →
        child.scene.layoutDump.box? native.toId = some toBox →
        Validator.onBoundary start fromBox.rect →
        Validator.onBoundary finish toBox.rect →
        let emitted := { native with points := native.points.map (shiftPoint dx dy) }
        emitted ∈ res.scene.routes ∧
          ∃ (fromBox' toBox' : Box),
            emitted.points.head? = some (shiftPoint dx dy start) ∧
            emitted.points.getLast? = some (shiftPoint dx dy finish) ∧
            res.scene.layoutDump.box? emitted.fromId = some fromBox' ∧
            res.scene.layoutDump.box? emitted.toId = some toBox' ∧
            Validator.onBoundary (shiftPoint dx dy start) fromBox'.rect ∧
            Validator.onBoundary (shiftPoint dx dy finish) toBox'.rect :=
  layoutRecursive_child_ports_transport_of_endpoint_invariants
    (Model.boxIds_nodup hwf) (input_routes_covered hwf) hgroup hrecursive

theorem recursive_selected_route_ids_disjoint_of_route_ids_nodup
    {fuel : Nat} {inp : Input} {o childOptions : Options} {group : ModelBox}
    {child parent : FamilyResult}
    {sizes : List (String × Size)} {children : List (String × Scene)}
    {areas : List (String × Int)}
    (hrouteIds : (inp.routes.map (·.id)).Nodup)
    (hchild : layoutRecursive fuel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      childOptions = .ok child)
    (hparent : layoutRecursive fuel
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent) :
    ∀ id ∈ child.scene.routes.map (·.id), id ∉ parent.scene.routes.map (·.id) := by
  have hc := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    (selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
  have hparentCoverage : RoutesCovered
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
    selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hp := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hparentCoverage hparent
  have hpRoutes := hp.2
  change parent.scene.routes.map (·.id) =
    (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).routes.map
      (·.id) at hpRoutes
  intro id hchildId hparentId
  rw [hc.2] at hchildId
  rw [hpRoutes] at hparentId
  obtain ⟨childRoute, hchildRoute, hchildRouteId⟩ := List.mem_map.mp hchildId
  obtain ⟨parentRoute, hparentRoute, hparentRouteId⟩ := List.mem_map.mp hparentId
  have hcMem := (selectInput_route_mem inp
    (fun box => Compound.inside inp.boxes group.id box.id) group.id childRoute).mp hchildRoute
  have hpMem := (selectInput_route_mem inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "" parentRoute).mp hparentRoute
  have hnodup : (inp.routes.map (·.id)).Nodup := hrouteIds
  have hcLookup := Assembly.keyed_lookup_eq (·.id) inp.routes hnodup childRoute hcMem.1
  have hpLookup := Assembly.keyed_lookup_eq (·.id) inp.routes hnodup parentRoute hpMem.1
  rw [hchildRouteId] at hcLookup
  rw [hparentRouteId] at hpLookup
  have hsame : childRoute = parentRoute := Option.some.inj (hcLookup.symm.trans hpLookup)
  have hcCovered := selectInput_routesCovered inp
    (fun box => Compound.inside inp.boxes group.id box.id) group.id childRoute hchildRoute
  have hpCovered := selectInput_routesCovered inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "" parentRoute hparentRoute
  obtain ⟨childBox, hchildBox, hchildBoxId⟩ := hcCovered.1
  obtain ⟨parentBox, hparentBox, hparentBoxId⟩ := hpCovered.1
  have hcBoxId : childRoute.fromId ∈ child.scene.boxes.map (·.id) := by
    rw [hc.1]
    exact List.mem_map.mpr ⟨childBox, hchildBox, hchildBoxId⟩
  have hpBoxId : childRoute.fromId ∈ parent.scene.boxes.map (·.id) := by
    rw [hp.1]
    change childRoute.fromId ∈
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).boxes.map (·.id)
    rw [hsame]
    exact List.mem_map.mpr ⟨parentBox, hparentBox, hparentBoxId⟩
  exact recursive_selected_box_ids_disjoint hchild hparent childRoute.fromId hcBoxId hpBoxId

theorem recursive_selected_route_ids_disjoint
    {fuel : Nat} {inp : Input} {o childOptions : Options} {group : ModelBox}
    {child parent : FamilyResult}
    {sizes : List (String × Size)} {children : List (String × Scene)}
    {areas : List (String × Int)}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursive fuel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      childOptions = .ok child)
    (hparent : layoutRecursive fuel
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent) :
    ∀ id ∈ child.scene.routes.map (·.id), id ∉ parent.scene.routes.map (·.id) :=
  recursive_selected_route_ids_disjoint_of_route_ids_nodup (Model.routeIds_nodup hwf)
    hchild hparent

theorem layoutRecursive_parent_ports_transport_of_endpoint_invariants
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hboxIds : (inp.boxes.map (·.id)).Nodup)
    (hrouteIds : (inp.routes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (child parent : FamilyResult) (P : Params) (height : Int)
      (sizes : List (String × Size)) (children : List (String × Scene))
      (areas : List (String × Int)),
      layoutRecursive fuel
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent ∧
      expandChild P inp o group height parent child = .ok res ∧
      ∀ (native : Route) (start finish : Point) (fromBox toBox : Box),
        parent.scene.routes.find? (fun route => route.id == native.id) = some native →
        native.points.head? = some start → native.points.getLast? = some finish →
        parent.scene.layoutDump.box? native.fromId = some fromBox →
        parent.scene.layoutDump.box? native.toId = some toBox →
        Validator.onBoundary start fromBox.rect →
        Validator.onBoundary finish toBox.rect →
        native ∈ res.scene.routes ∧
          res.scene.layoutDump.box? native.fromId = some fromBox ∧
          res.scene.layoutDump.box? native.toId = some toBox ∧
          native.points.head? = some start ∧ native.points.getLast? = some finish ∧
          Validator.onBoundary start fromBox.rect ∧
          Validator.onBoundary finish toBox.rect := by
  obtain ⟨P, height, child, parent, sizes, children, areas, dx, dy,
    hchild, hparent, hexpand, _, hparentLookup, hroutes⟩ :=
    layoutRecursive_embedding_box_lookup_of_endpoint_invariants hboxIds hcovered hgroup hrecursive
  refine ⟨child, parent, P, height, sizes, children, areas, hparent, hexpand, ?_⟩
  intro native start finish fromBox toBox hnative hstart hfinish hfrom hto hfromBoundary htoBoundary
  have hmember : native ∈ parent.scene.routes := List.mem_of_find?_eq_some hnative
  have hnativeId : native.id ∈ parent.scene.routes.map (·.id) := List.mem_map_of_mem hmember
  have hdisjoint := recursive_selected_route_ids_disjoint_of_route_ids_nodup hrouteIds hchild hparent
  have hnone : (child.scene.routes.map fun (route : Route) =>
      { route with points := route.points.map (shiftPoint dx dy) }).find?
      (fun route => route.id == native.id) = none := by
    apply List.find?_eq_none.mpr
    intro candidate hcandidate htest
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hcandidate
    have heq : source.id = native.id := beq_iff_eq.mp htest
    have hsourceId : source.id ∈ child.scene.routes.map (·.id) := List.mem_map_of_mem hsource
    rw [heq] at hsourceId
    exact hdisjoint native.id hsourceId hnativeId
  have hfind : ((child.scene.routes.map fun (route : Route) =>
      { route with points := route.points.map (shiftPoint dx dy) }) ++
      parent.scene.routes).find? (fun route => route.id == native.id) = some native := by
    simp [List.find?_append, hnone, hnative]
  have hparentCoverage : RoutesCovered
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
    selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hp := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel _ _ _
    hparentCoverage hparent
  have hpRoutes := hp.2
  change parent.scene.routes.map (·.id) =
    (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).routes.map
      (·.id) at hpRoutes
  rw [hpRoutes] at hnativeId
  obtain ⟨model, hmodelSelected, hmodelId⟩ := List.mem_map.mp hnativeId
  have hmodel := ((selectInput_route_mem inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "" model).mp hmodelSelected).1
  have hemitted : native ∈ res.scene.routes := by
    rw [hroutes]
    apply List.mem_filterMap.mpr
    refine ⟨model, hmodel, ?_⟩
    rw [hmodelId]
    exact hfind
  change parent.scene.boxes.find? (fun box => box.id == native.fromId) = some fromBox at hfrom
  change parent.scene.boxes.find? (fun box => box.id == native.toId) = some toBox at hto
  have hfromTest : (fromBox.id == native.fromId) = true :=
    List.find?_some (p := fun (box : Box) => box.id == native.fromId) hfrom
  have htoTest : (toBox.id == native.toId) = true :=
    List.find?_some (p := fun (box : Box) => box.id == native.toId) hto
  have hfromId : fromBox.id = native.fromId := beq_iff_eq.mp hfromTest
  have htoId : toBox.id = native.toId := beq_iff_eq.mp htoTest
  have hfromSelf : parent.scene.layoutDump.box? fromBox.id = some fromBox := by
    rw [hfromId]
    exact hfrom
  have htoSelf : parent.scene.layoutDump.box? toBox.id = some toBox := by
    rw [htoId]
    exact hto
  refine ⟨hemitted, ?_, ?_, hstart, hfinish, hfromBoundary, htoBoundary⟩
  · rw [← hfromId]
    exact hparentLookup fromBox hfromSelf
  · rw [← htoId]
    exact hparentLookup toBox htoSelf

theorem layoutRecursive_parent_ports_transport
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hrecursive : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (child parent : FamilyResult) (P : Params) (height : Int)
      (sizes : List (String × Size)) (children : List (String × Scene))
      (areas : List (String × Int)),
      layoutRecursive fuel
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent ∧
      expandChild P inp o group height parent child = .ok res ∧
      ∀ (native : Route) (start finish : Point) (fromBox toBox : Box),
        parent.scene.routes.find? (fun route => route.id == native.id) = some native →
        native.points.head? = some start → native.points.getLast? = some finish →
        parent.scene.layoutDump.box? native.fromId = some fromBox →
        parent.scene.layoutDump.box? native.toId = some toBox →
        Validator.onBoundary start fromBox.rect →
        Validator.onBoundary finish toBox.rect →
        native ∈ res.scene.routes ∧
          res.scene.layoutDump.box? native.fromId = some fromBox ∧
          res.scene.layoutDump.box? native.toId = some toBox ∧
          native.points.head? = some start ∧ native.points.getLast? = some finish ∧
          Validator.onBoundary start fromBox.rect ∧
          Validator.onBoundary finish toBox.rect :=
  layoutRecursive_parent_ports_transport_of_endpoint_invariants
    (Model.boxIds_nodup hwf) (Model.routeIds_nodup hwf) (input_routes_covered hwf)
    hgroup hrecursive

theorem selectInput_box_source
    (inp : Input) (keep : ModelBox → Bool) (root : String) (selected : ModelBox)
    (hselected : selected ∈ (selectInput inp keep root).boxes) :
    ∃ source ∈ inp.boxes, keep source = true ∧
      selected = (if source.parent == root then { source with parent := "" } else source) := by
  have hboxes : (selectInput inp keep root).boxes =
      (inp.boxes.filter keep).map (fun source =>
        if source.parent == root then { source with parent := "" } else source) := by
    exact zipIdx_filter_map_fst keep
      (fun source => if source.parent == root then { source with parent := "" } else source)
      inp.boxes 0
  rw [hboxes] at hselected
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hselected
  obtain ⟨hsource, hkeep⟩ := List.mem_filter.mp hsource
  exact ⟨source, hsource, hkeep, heq.symm⟩

theorem selectInput_node_source
    (inp : Input) (keep : ModelBox → Bool) (root : String) (selected : ModelBox)
    (hselected : selected ∈ (selectInput inp keep root).boxes)
    (hrole : selected.role = .node) :
    ∃ source ∈ inp.boxes, keep source = true ∧ source.id = selected.id ∧
      source.role = .node := by
  obtain ⟨source, hsource, hkeep, heq⟩ := selectInput_box_source inp keep root selected hselected
  refine ⟨source, hsource, hkeep, ?_, ?_⟩
  · rw [heq]
    split <;> rfl
  · rw [heq] at hrole
    split at hrole <;> exact hrole

theorem selectInput_node_preserved
    (inp : Input) (keep : ModelBox → Bool) (root : String) (source : ModelBox)
    (hsource : source ∈ inp.boxes) (hkeep : keep source = true)
    (hrole : source.role = .node) :
    ∃ selected ∈ (selectInput inp keep root).boxes,
      selected.id = source.id ∧ selected.role = .node := by
  let selected := if source.parent == root then { source with parent := "" } else source
  have hboxes : (selectInput inp keep root).boxes =
      (inp.boxes.filter keep).map (fun source =>
        if source.parent == root then { source with parent := "" } else source) := by
    exact zipIdx_filter_map_fst keep
      (fun source => if source.parent == root then { source with parent := "" } else source)
      inp.boxes 0
  refine ⟨selected, ?_, ?_, ?_⟩
  · rw [hboxes]
    exact List.mem_map.mpr ⟨source, List.mem_filter.mpr ⟨hsource, hkeep⟩, rfl⟩
  · dsimp only [selected]
    split <;> rfl
  · dsimp only [selected]
    split <;> exact hrole

theorem selectInput_box_ids_nodup
    {inp : Input} (hids : (inp.boxes.map (·.id)).Nodup)
    (keep : ModelBox → Bool) (root : String) :
    ((selectInput inp keep root).boxes.map (·.id)).Nodup := by
  rw [selectInput_box_ids]
  exact List.Nodup.sublist
    (List.Sublist.map (fun box : ModelBox => box.id) List.filter_sublist) hids

theorem selectInput_route_ids_nodup
    {inp : Input} (hids : (inp.routes.map (·.id)).Nodup)
    (keep : ModelBox → Bool) (root : String) :
    ((selectInput inp keep root).routes.map (·.id)).Nodup := by
  let selected := selectInput inp keep root
  let retain := fun route : ModelRoute =>
    selected.boxes.any (fun box => box.id == route.fromId) &&
      selected.boxes.any (fun box => box.id == route.toId)
  have hroutes : selected.routes = inp.routes.filter retain := by
    simpa only [selected, retain, selectInput, List.map_id'] using
      (zipIdx_filter_map_fst retain (fun route => route) inp.routes 0)
  change (selected.routes.map (·.id)).Nodup
  rw [hroutes]
  exact List.Nodup.sublist
    (List.Sublist.map (fun route : ModelRoute => route.id) List.filter_sublist) hids

theorem selectInput_endpoint_invariants
    {inp : Input} {o : Options} (hwf : WellFormed (inputModel inp o))
    (keep : ModelBox → Bool) (root : String) :
    ((selectInput inp keep root).boxes.map (·.id)).Nodup ∧
      ((selectInput inp keep root).routes.map (·.id)).Nodup ∧
      RoutesCovered (selectInput inp keep root) :=
  ⟨selectInput_box_ids_nodup (Model.boxIds_nodup hwf) keep root,
    selectInput_route_ids_nodup (Model.routeIds_nodup hwf) keep root,
    selectInput_routesCovered inp keep root⟩

def EffectiveEndpointInvariant (inp : Input) (scene : Scene) : Prop :=
  ∀ out ∈ scene.routes,
    ∃ source ∈ inp.boxes, ∃ target ∈ inp.boxes,
      source.id = out.fromId ∧ target.id = out.toId ∧
      (source.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true →
        target.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == target.id) = true →
        ∃ (start finish : Point) (fromBox toBox : Box),
          out.points.head? = some start ∧ out.points.getLast? = some finish ∧
          scene.layoutDump.box? out.fromId = some fromBox ∧
          scene.layoutDump.box? out.toId = some toBox ∧
          Validator.onBoundary start fromBox.rect ∧
          Validator.onBoundary finish toBox.rect)

private theorem effective_role_transport
    {inp selected : Input} {source target : ModelBox}
    (hid : source.id = target.id) (hrole : source.role = target.role)
    (hfixed : inp.fixedSizes ⊆ selected.fixedSizes)
    (hs : source.role = .node ∨
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true) :
    target.role = .node ∨
      selected.fixedSizes.any (fun fixed => fixed.1 == target.id) = true := by
  rcases hs with hs | hs
  · exact Or.inl (hrole.symm.trans hs)
  · right
    obtain ⟨fixed, hmember, htest⟩ := List.any_eq_true.mp hs
    exact List.any_eq_true.mpr ⟨fixed, hfixed hmember, by simpa only [hid] using htest⟩

def OrdinaryEndpointInvariant (inp : Input) (scene : Scene) : Prop :=
  ∀ out ∈ scene.routes,
    ∃ source ∈ inp.boxes, ∃ target ∈ inp.boxes,
      source.id = out.fromId ∧ target.id = out.toId ∧
      (source.role = .node → target.role = .node →
        ∃ (start finish : Point) (fromBox toBox : Box),
          out.points.head? = some start ∧ out.points.getLast? = some finish ∧
          scene.layoutDump.box? out.fromId = some fromBox ∧
          scene.layoutDump.box? out.toId = some toBox ∧
          Validator.onBoundary start fromBox.rect ∧
          Validator.onBoundary finish toBox.rect)

theorem SceneExecution.effective_endpoint_source_invariant
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp) :
    EffectiveEndpointInvariant inp res.scene := by
  intro out hout
  obtain ⟨key, houtIndex⟩ := List.mem_iff_getElem?.mp hout
  have hlength : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    simp only [sceneOf, List.length_map, List.length_zipIdx]
  have hkey : key < inp.routes.length := by
    rw [← hlength]
    exact (List.getElem?_eq_some_iff.mp houtIndex).1
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.straightAcc execution.measured key hkey
  rw [← execution.scene_eq] at hscene
  have houtRecord := Option.some.inj (houtIndex.symm.trans hscene)
  have hfromId := congrArg Route.fromId houtRecord
  have htoId := congrArg Route.toId houtRecord
  obtain ⟨⟨source, hsource, hsourceId⟩, ⟨target, htarget, htargetId⟩⟩ :=
    hcovered inp.routes[key] (List.getElem_mem hkey)
  refine ⟨source, hsource, target, htarget, hsourceId.trans hfromId.symm,
    htargetId.trans htoId.symm, ?_⟩
  intro hs ht
  exact execution.effective_endpoint_c5 hids hout
    ⟨source, hsource, hsourceId.trans hfromId.symm, hs⟩
    ⟨target, htarget, htargetId.trans htoId.symm, ht⟩

theorem SceneExecution.ordinary_endpoint_source_invariant
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp) :
    OrdinaryEndpointInvariant inp res.scene := by
  intro out hout
  obtain ⟨source, hsource, target, htarget, hsId, htId, hports⟩ :=
    execution.effective_endpoint_source_invariant hids hcovered out hout
  exact ⟨source, hsource, target, htarget, hsId, htId,
    fun hs ht => hports (Or.inl hs) (Or.inl ht)⟩

theorem layoutRecursive_effective_endpoint_source_invariant
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hboxIds : (inp.boxes.map (·.id)).Nodup)
    (hrouteIds : (inp.routes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hrecursive : layoutRecursive fuel inp o = .ok res) :
    EffectiveEndpointInvariant inp res.scene := by
  have hbase : ∀ {input : Input} {options : Options} {result : FamilyResult},
      (input.boxes.map (·.id)).Nodup → RoutesCovered input →
      layout input options = .ok result → EffectiveEndpointInvariant input result.scene := by
    intro input options result hids hcoverage hrun
    obtain ⟨execution⟩ := layout_sceneExecution hrun
    exact execution.effective_endpoint_source_invariant hids hcoverage
  induction fuel generalizing inp o res with
  | zero => exact hbase hboxIds hcovered hrecursive
  | succ fuel ih =>
    rcases layoutRecursive_succ hrecursive with ⟨_, hflat⟩ |
      ⟨group, hgroup, _, _, _, _, _, _, _, _, _, _⟩
    · exact hbase hboxIds hcovered hflat
    · obtain ⟨P, height, child, parent, sizes, children, areas, dx, dy,
        hfixed, hchild, hparent, hexpand, hchildLookup, hparentLookup, hroutes⟩ :=
        layoutRecursive_embedding_box_lookup_with_fixed_sizes
          hboxIds hcovered hgroup hrecursive
      have hc := ih
        (selectInput_box_ids_nodup hboxIds
          (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        (selectInput_route_ids_nodup hrouteIds
          (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        (selectInput_routesCovered inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
      have hparentIds : (({ selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } : Input).boxes.map
          (·.id)).Nodup :=
        selectInput_box_ids_nodup hboxIds
          (fun box => !Compound.inside inp.boxes group.id box.id) ""
      have hparentRouteIds : (({ selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } : Input).routes.map
          (·.id)).Nodup :=
        selectInput_route_ids_nodup hrouteIds
          (fun box => !Compound.inside inp.boxes group.id box.id) ""
      have hparentCovered : RoutesCovered
          { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
        selectInput_routesCovered inp
          (fun box => !Compound.inside inp.boxes group.id box.id) ""
      have hp := ih hparentIds hparentRouteIds hparentCovered hparent
      have lift : ∀ (keep : ModelBox → Bool) (root : String) (selected : ModelBox),
          selected ∈ (selectInput inp keep root).boxes →
          ∃ source ∈ inp.boxes, source.id = selected.id ∧ source.role = selected.role := by
        intro keep root selected hselected
        obtain ⟨source, hsource, _, heq⟩ :=
          selectInput_box_source inp keep root selected hselected
        refine ⟨source, hsource, ?_, ?_⟩
        · rw [heq]
          split <;> rfl
        · rw [heq]
          split <;> rfl
      intro out hout
      rw [hroutes] at hout
      obtain ⟨model, _, hfind⟩ := List.mem_filterMap.mp hout
      have houtMember := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp houtMember with hshifted | hunchanged
      · obtain ⟨native, hnative, houtEq⟩ := List.mem_map.mp hshifted
        subst out
        obtain ⟨selectedSource, hselectedSource, selectedTarget, hselectedTarget,
          hfromId, htoId, hports⟩ := hc native hnative
        obtain ⟨source, hsource, hsId, hsRole⟩ := lift _ _ _ hselectedSource
        obtain ⟨target, htarget, htId, htRole⟩ := lift _ _ _ hselectedTarget
        refine ⟨source, hsource, target, htarget, hsId.trans hfromId,
          htId.trans htoId, ?_⟩
        intro hs ht
        obtain ⟨start, finish, fromBox, toBox, hstart, hfinish,
          hfrom, hto, hfromBoundary, htoBoundary⟩ :=
          hports (effective_role_transport hsId hsRole (fun _ hf => hf) hs)
            (effective_role_transport htId htRole (fun _ hf => hf) ht)
        have hfromBoxId : fromBox.id = native.fromId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == native.fromId) hfrom)
        have htoBoxId : toBox.id = native.toId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == native.toId) hto)
        have hfromSelf : child.scene.layoutDump.box? fromBox.id = some fromBox := by
          rw [hfromBoxId]
          exact hfrom
        have htoSelf : child.scene.layoutDump.box? toBox.id = some toBox := by
          rw [htoBoxId]
          exact hto
        refine ⟨shiftPoint dx dy start, shiftPoint dx dy finish,
          { fromBox with rect := shiftRect dx dy fromBox.rect, parent := if fromBox.parent == "" then group.id else fromBox.parent },
          { toBox with rect := shiftRect dx dy toBox.rect, parent := if toBox.parent == "" then group.id else toBox.parent },
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.head?_map, hstart, Option.map_some]
        · simp only [List.getLast?_map, hfinish, Option.map_some]
        · change res.scene.layoutDump.box? native.fromId = _
          rw [← hfromBoxId]
          exact hchildLookup fromBox hfromSelf
        · change res.scene.layoutDump.box? native.toId = _
          rw [← htoBoxId]
          exact hchildLookup toBox htoSelf
        · exact (onBoundary_shift dx dy start fromBox.rect).mpr hfromBoundary
        · exact (onBoundary_shift dx dy finish toBox.rect).mpr htoBoundary
      · obtain ⟨selectedSource, hselectedSource, selectedTarget, hselectedTarget,
          hfromId, htoId, hports⟩ := hp out hunchanged
        obtain ⟨source, hsource, hsId, hsRole⟩ :=
          lift (fun box => !Compound.inside inp.boxes group.id box.id) "" _ hselectedSource
        obtain ⟨target, htarget, htId, htRole⟩ :=
          lift (fun box => !Compound.inside inp.boxes group.id box.id) "" _ hselectedTarget
        refine ⟨source, hsource, target, htarget, hsId.trans hfromId,
          htId.trans htoId, ?_⟩
        intro hs ht
        obtain ⟨start, finish, fromBox, toBox, hstart, hfinish,
          hfrom, hto, hfromBoundary, htoBoundary⟩ :=
          hports (effective_role_transport hsId hsRole hfixed hs)
            (effective_role_transport htId htRole hfixed ht)
        have hfromBoxId : fromBox.id = out.fromId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == out.fromId) hfrom)
        have htoBoxId : toBox.id = out.toId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == out.toId) hto)
        refine ⟨start, finish, fromBox, toBox, hstart, hfinish,
          ?_, ?_, hfromBoundary, htoBoundary⟩
        · have hself : parent.scene.layoutDump.box? fromBox.id = some fromBox := by
            rw [hfromBoxId]
            exact hfrom
          rw [← hfromBoxId]
          exact hparentLookup fromBox hself
        · have hself : parent.scene.layoutDump.box? toBox.id = some toBox := by
            rw [htoBoxId]
            exact hto
          rw [← htoBoxId]
          exact hparentLookup toBox hself

theorem layoutRecursive_ordinary_endpoint_source_invariant
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hboxIds : (inp.boxes.map (·.id)).Nodup)
    (hrouteIds : (inp.routes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hrecursive : layoutRecursive fuel inp o = .ok res) :
    OrdinaryEndpointInvariant inp res.scene := by
  intro out hout
  obtain ⟨source, hsource, target, htarget, hsId, htId, hports⟩ :=
    layoutRecursive_effective_endpoint_source_invariant fuel hboxIds hrouteIds hcovered
      hrecursive out hout
  exact ⟨source, hsource, target, htarget, hsId, htId,
    fun hs ht => hports (Or.inl hs) (Or.inl ht)⟩

theorem layoutRecursive_effective_endpoint_c5
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hrecursive : layoutRecursive fuel inp o = .ok res)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hfrom : ∃ source ∈ inp.boxes, source.id = out.fromId ∧
      (source.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true))
    (hto : ∃ target ∈ inp.boxes, target.id = out.toId ∧
      (target.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == target.id) = true)) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  have hids := Model.boxIds_nodup hwf
  obtain ⟨source, hsource, target, htarget, hsId, htId, hports⟩ :=
    layoutRecursive_effective_endpoint_source_invariant fuel hids
      (Model.routeIds_nodup hwf) (input_routes_covered hwf) hrecursive out hout
  exact hports (input_effective_role_of_id hids hsource hsId hfrom)
    (input_effective_role_of_id hids htarget htId hto)

theorem layoutRecursive_ordinary_endpoint_c5
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hrecursive : layoutRecursive fuel inp o = .ok res)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hfrom : ∃ source ∈ inp.boxes, source.id = out.fromId ∧ source.role = .node)
    (hto : ∃ target ∈ inp.boxes, target.id = out.toId ∧ target.role = .node) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  have hids := Model.boxIds_nodup hwf
  obtain ⟨source, hsource, target, htarget, hsId, htId, hports⟩ :=
    layoutRecursive_ordinary_endpoint_source_invariant fuel hids
      (Model.routeIds_nodup hwf) (input_routes_covered hwf) hrecursive out hout
  exact hports (input_node_role_of_id hids hsource hsId hfrom)
    (input_node_role_of_id hids htarget htId hto)

theorem layoutRecursive_self_endpoint_c5
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hboxIds : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hrecursive : layoutRecursive fuel inp o = .ok res)
    {out : Route} (hout : out ∈ res.scene.routes) (hselfId : out.fromId = out.toId) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  have hbase : ∀ {input : Input} {options : Options} {result : FamilyResult},
      (input.boxes.map (·.id)).Nodup → layout input options = .ok result →
      ∀ {route : Route}, route ∈ result.scene.routes → route.fromId = route.toId →
      ∃ (start finish : Point) (fromBox toBox : Box),
        route.points.head? = some start ∧ route.points.getLast? = some finish ∧
        result.scene.layoutDump.box? route.fromId = some fromBox ∧
        result.scene.layoutDump.box? route.toId = some toBox ∧
        Validator.onBoundary start fromBox.rect ∧
        Validator.onBoundary finish toBox.rect := by
    intro input options result hids hrun route hroute hself
    obtain ⟨execution⟩ := layout_sceneExecution hrun
    exact execution.self_routes_c5_of_box_ids_nodup hids hroute hself
  induction fuel generalizing inp o res out with
  | zero => exact hbase hboxIds hrecursive hout hselfId
  | succ fuel ih =>
    rcases layoutRecursive_succ hrecursive with ⟨_, hflat⟩ |
      ⟨group, hgroup, _, _, _, _, _, _, _, _, _, _⟩
    · exact hbase hboxIds hflat hout hselfId
    · obtain ⟨P, height, child, parent, sizes, children, areas, dx, dy,
        hchild, hparent, hexpand, hchildLookup, hparentLookup, hroutes⟩ :=
        layoutRecursive_embedding_box_lookup_of_endpoint_invariants
          hboxIds hcovered hgroup hrecursive
      rw [hroutes] at hout
      obtain ⟨model, _, hfind⟩ := List.mem_filterMap.mp hout
      have houtMember := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp houtMember with hshifted | hunchanged
      · obtain ⟨native, hnative, houtEq⟩ := List.mem_map.mp hshifted
        subst out
        have hnativeSelf : native.fromId = native.toId := hselfId
        obtain ⟨start, finish, fromBox, toBox, hstart, hfinish,
          hfrom, hto, hfromBoundary, htoBoundary⟩ :=
          ih (selectInput_box_ids_nodup hboxIds
              (fun box => Compound.inside inp.boxes group.id box.id) group.id)
            (selectInput_routesCovered inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id)
            hchild hnative hnativeSelf
        have hfromBoxId : fromBox.id = native.fromId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == native.fromId) hfrom)
        have htoBoxId : toBox.id = native.toId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == native.toId) hto)
        have hfromSelf : child.scene.layoutDump.box? fromBox.id = some fromBox := by
          rw [hfromBoxId]
          exact hfrom
        have htoSelf : child.scene.layoutDump.box? toBox.id = some toBox := by
          rw [htoBoxId]
          exact hto
        refine ⟨shiftPoint dx dy start, shiftPoint dx dy finish,
          { fromBox with rect := shiftRect dx dy fromBox.rect, parent := if fromBox.parent == "" then group.id else fromBox.parent },
          { toBox with rect := shiftRect dx dy toBox.rect, parent := if toBox.parent == "" then group.id else toBox.parent },
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.head?_map, hstart, Option.map_some]
        · simp only [List.getLast?_map, hfinish, Option.map_some]
        · change res.scene.layoutDump.box? native.fromId = _
          rw [← hfromBoxId]
          exact hchildLookup fromBox hfromSelf
        · change res.scene.layoutDump.box? native.toId = _
          rw [← htoBoxId]
          exact hchildLookup toBox htoSelf
        · exact (onBoundary_shift dx dy start fromBox.rect).mpr hfromBoundary
        · exact (onBoundary_shift dx dy finish toBox.rect).mpr htoBoundary
      · have hparentIds : (({ selectInput inp
            (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } : Input).boxes.map
            (·.id)).Nodup :=
          selectInput_box_ids_nodup hboxIds
            (fun box => !Compound.inside inp.boxes group.id box.id) ""
        have hparentCovered : RoutesCovered
            { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
              fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
          selectInput_routesCovered inp
            (fun box => !Compound.inside inp.boxes group.id box.id) ""
        obtain ⟨start, finish, fromBox, toBox, hstart, hfinish,
          hfrom, hto, hfromBoundary, htoBoundary⟩ :=
          ih hparentIds hparentCovered hparent hunchanged hselfId
        have hfromBoxId : fromBox.id = out.fromId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == out.fromId) hfrom)
        have htoBoxId : toBox.id = out.toId :=
          beq_iff_eq.mp (List.find?_some
            (p := fun (box : Box) => box.id == out.toId) hto)
        refine ⟨start, finish, fromBox, toBox, hstart, hfinish,
          ?_, ?_, hfromBoundary, htoBoundary⟩
        · have hself : parent.scene.layoutDump.box? fromBox.id = some fromBox := by
            rw [hfromBoxId]
            exact hfrom
          rw [← hfromBoxId]
          exact hparentLookup fromBox hself
        · have hself : parent.scene.layoutDump.box? toBox.id = some toBox := by
            rw [htoBoxId]
            exact hto
          rw [← htoBoxId]
          exact hparentLookup toBox hself

theorem SceneExecution.graph_direct_group_path {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {parentKey childKey : Nat} {parentNode childNode : Node}
    (hparentNode : execution.graph.nodes[parentKey]? = some parentNode)
    (hchildNode : execution.graph.nodes[childKey]? = some childNode)
    (hparentGroup : parentNode.border = -2) (hchildGroup : childNode.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hchildBox : inp.boxes[childKey]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    childNode.clusterPath.dropLast = parentNode.clusterPath := by
  obtain ⟨parentOriginal, hparentOriginal, hparentDecl, hparentPath⟩ :=
    execution.group_node_path_source hparentNode hparentGroup
  obtain ⟨childOriginal, hchildOriginal, hchildDecl, hchildPath⟩ :=
    execution.group_node_path_source hchildNode hchildGroup
  have hparentEq : parentOriginal = parentBox :=
    Option.some.inj (hparentOriginal.symm.trans hparentBox)
  have hchildEq : childOriginal = childBox :=
    Option.some.inj (hchildOriginal.symm.trans hchildBox)
  rw [hparentEq] at hparentPath
  rw [hchildEq] at hchildPath
  have himmediate := Compound.path_of_parent (inputModel inp o) hwf
    hparentBox hchildBox hparentRef hne
  calc
    childNode.clusterPath.dropLast = Compound.path inp.boxes childBox := by
      rw [hchildPath, List.dropLast_concat]
    _ = Compound.path inp.boxes parentBox ++ [parentKey] := himmediate
    _ = parentNode.clusterPath := hparentPath.symm

theorem SceneExecution.group_bottom_lookup {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph.nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ bottom : Node × Nat,
      (execution.graph.nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == node.decl) = some bottom := by
  obtain ⟨_, effective, heffective, hrole, _⟩ :=
    measuredGraph_group_origin execution.graph_eq hnode hgroup
  obtain ⟨nodes, edges, titles, hprepared, _, _⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hmem := Compound.prepare_bottom_exists _ execution.params.clusterPad titles
    { nodes := nodes, edges := edges, slot := execution.params.slot } heffective hrole
  rw [← hprepared] at hmem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  have hzip : ((_ : Node), j) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hj
  have hsome : (execution.graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == node.decl).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨_, hzip, by simp⟩
  exact Option.isSome_iff_exists.mp hsome


theorem SceneExecution.group_parent_constraint_edge {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {parentKey childKey : Nat} {parentNode childNode : Node}
    (hparentNode : execution.graph.nodes[parentKey]? = some parentNode)
    (hchildNode : execution.graph.nodes[childKey]? = some childNode)
    (hparentGroup : parentNode.border = -2) (hchildGroup : childNode.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hchildBox : inp.boxes[childKey]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (⟨parentKey, childKey, 1, 0, false⟩ : Edge) ∈ Compound.constraints execution.graph := by
  obtain ⟨parentBottom, hparentBottom⟩ := execution.group_bottom_lookup hparentNode hparentGroup
  obtain ⟨childBottom, hchildBottom⟩ := execution.group_bottom_lookup hchildNode hchildGroup
  have hpath := execution.graph_direct_group_path hwf hparentNode hchildNode hparentGroup
    hchildGroup hparentBox hchildBox hparentRef hne
  exact (compound_child_constraint_edges (parent := (parentNode, parentKey))
    (child := (childNode, childKey)) (List.mem_zipIdx_iff_getElem?.mpr hparentNode)
    hparentGroup hparentBottom (List.mem_zipIdx_iff_getElem?.mpr hchildNode) hchildGroup
    hpath hchildBottom).1

theorem SceneExecution.group_parent_same_part {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {parentKey childKey : Nat} {parentNode childNode : Node}
    (hparentNode : execution.graph.nodes[parentKey]? = some parentNode)
    (hchildNode : execution.graph.nodes[childKey]? = some childNode)
    (hparentGroup : parentNode.border = -2) (hchildGroup : childNode.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hchildBox : inp.boxes[childKey]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    ∃ part ∈ execution.componentsAcc.parts, parentKey ∈ part.1 ∧ childKey ∈ part.1 := by
  have hedge := execution.group_parent_constraint_edge hwf hparentNode hchildNode
    hparentGroup hchildGroup hparentBox hchildBox hparentRef hne
  obtain ⟨comp, hcomp, hparentIn, hchildIn⟩ := components_edge_endpoints
    (sceneExecution_edges_bounded execution) (List.mem_append_right _ hedge)
  obtain ⟨hparts, _⟩ := actual_components_parts_geometry (by rfl) execution.components_eq
  have hmem : comp ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hparts]
    exact hcomp
  obtain ⟨part, hpart, hpartComp⟩ := List.mem_map.mp hmem
  refine ⟨part, hpart, ?_, ?_⟩
  · rw [hpartComp]
    exact hparentIn
  · rw [hpartComp]
    exact hchildIn

theorem SceneExecution.part_frame_rects {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ (index : Nat) (run : Run) (dx dy : Int),
      part.1 ∈ components execution.graph ∧
      componentRun execution.params (componentCandidate execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      ∀ {position : Nat},
        position < (componentCandidate execution.graph part.1 index).nodes.length →
        part.2.rects[position]? = some (shiftRect dx dy
          (frameRect execution.params (componentCandidate execution.graph part.1 index)
            run position)) := by
  obtain ⟨hcomponents, _⟩ :=
    actual_components_parts_geometry (by rfl) execution.components_eq
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hcomponents]
    exact List.mem_map.mpr ⟨part, hpart, rfl⟩
  obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hpart
  let cg := componentCandidate execution.graph part.1 index
  let bounds := placeBounds execution.params cg run execution.measured loops
  refine ⟨index, run, 0 - bounds.minX, 0 - bounds.minY, hcomp, hrun, ?_⟩
  intro position hposition
  rw [hplace]
  change (((List.range cg.nodes.length).map (frameRect execution.params cg run)).map
    (shiftRect (0 - bounds.minX) (0 - bounds.minY)))[position]? =
      some (shiftRect (0 - bounds.minX) (0 - bounds.minY)
        (frameRect execution.params cg run position))
  have hposition' : position < cg.nodes.length := hposition
  simp only [List.getElem?_map, List.getElem?_range hposition', Option.map_some]

theorem candidate_node_of_part_key {graph : Graph} {part : List Nat}
    {index position key : Nat} {node : Node}
    (hkey : part[position]? = some key) (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph part index).nodes[position]? = some node := by
  rw [componentCandidate_nodes]
  change (part.map (fun key => graph.nodes.getD key default))[position]? = some node
  simp only [List.getElem?_map, hkey, Option.map_some,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

theorem SceneExecution.part_nested_frames_contained {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {parentIndex childIndex parentKey childKey : Nat}
    (hparentKey : part.1[parentIndex]? = some parentKey)
    (hchildKey : part.1[childIndex]? = some childKey)
    {parentNode childNode : Node}
    (hparentNode : execution.graph.nodes[parentKey]? = some parentNode)
    (hchildNode : execution.graph.nodes[childKey]? = some childNode)
    (hparentGroup : parentNode.border = -2) (hchildGroup : childNode.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hchildBox : inp.boxes[childKey]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    ∃ parentFrame childFrame : Rect,
      part.2.rects[parentIndex]? = some parentFrame ∧
      part.2.rects[childIndex]? = some childFrame ∧
      parentFrame.Contained childFrame := by
  obtain ⟨index, run, dx, dy, hcomp, hrun, hframes⟩ := execution.part_frame_rects hpart
  have hlocalParent := candidate_node_of_part_key (index := index) hparentKey hparentNode
  have hlocalChild := candidate_node_of_part_key (index := index) hchildKey hchildNode
  obtain ⟨_, _, hparentDecl, _⟩ := execution.group_node_path_source hparentNode hparentGroup
  obtain ⟨_, _, hchildDecl, _⟩ := execution.group_node_path_source hchildNode hchildGroup
  have hcontained := execution.component_child_frame_contained hwf hcomp hrun hlocalParent
    hparentGroup hlocalChild hchildGroup (by rw [hparentDecl]; exact hparentBox)
    (by rw [hchildDecl]; exact hchildBox) hparentRef hne
  refine ⟨_, _, hframes (List.getElem?_eq_some_iff.mp hlocalParent).1,
    hframes (List.getElem?_eq_some_iff.mp hlocalChild).1, ?_⟩
  unfold Rect.Contained at hcontained ⊢
  unfold shiftRect
  dsimp only
  omega

theorem SceneExecution.packed_part_rect_shift {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ dx dy : Int, ∀ {position key : Nat} {frame : Rect},
      part.1[position]? = some key → part.2.rects[position]? = some frame →
      key < execution.componentsAcc.rects.size →
      execution.packedAcc.rects.getD key default = shiftRect dx dy frame := by
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, hpacked, _⟩ := bind_ok hpack
  obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpart
  have hclt : c < packed.boxes.length := by
    rw [Pack.pack_count hpacked]
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hc).1
  let box := packed.boxes[c]'hclt
  have hbox : packed.boxes[c]? = some box := List.getElem?_eq_getElem hclt
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
      some (part, box) := List.getElem?_zip_eq_some.mpr ⟨hc, hbox⟩
  refine ⟨box.x, box.y, ?_⟩
  intro position key frame hkey hframe hsize
  have hentry : (part.1.zip part.2.rects)[position]? = some (key, frame) :=
    List.getElem?_zip_eq_some.mpr ⟨hkey, hframe⟩
  exact actual_components_packed_rect_value (by rfl) execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hsize default

theorem SceneExecution.scene_boxes_contained_of_part_frames {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {outerIndex innerIndex outerKey innerKey : Nat}
    (houterKey : part.1[outerIndex]? = some outerKey)
    (hinnerKey : part.1[innerIndex]? = some innerKey)
    {outerSource innerSource : ModelBox}
    (houterSource : inp.boxes[outerKey]? = some outerSource)
    (hinnerSource : inp.boxes[innerKey]? = some innerSource)
    {outerFrame innerFrame : Rect}
    (houterFrame : part.2.rects[outerIndex]? = some outerFrame)
    (hinnerFrame : part.2.rects[innerIndex]? = some innerFrame)
    (hcontained : outerFrame.Contained innerFrame) :
    ∃ outerBox innerBox : Box,
      res.scene.layoutDump.box? outerSource.id = some outerBox ∧
      res.scene.layoutDump.box? innerSource.id = some innerBox ∧
      outerBox.rect.Contained innerBox.rect := by
  obtain ⟨dx, dy, hshift⟩ := execution.packed_part_rect_shift hpart
  have hsize : ∀ {key : Nat} {source : ModelBox}, inp.boxes[key]? = some source →
      key < execution.componentsAcc.rects.size := by
    intro key source hsource
    rw [execution.components_rects_size]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have houterPacked := hshift houterKey houterFrame (hsize houterSource)
  have hinnerPacked := hshift hinnerKey hinnerFrame (hsize hinnerSource)
  have hids := Model.boxIds_nodup hwf
  have houterBox := execution.source_box_lookup_of_box_ids_nodup hids houterSource
  have hinnerBox := execution.source_box_lookup_of_box_ids_nodup hids hinnerSource
  rw [houterPacked] at houterBox
  rw [hinnerPacked] at hinnerBox
  refine ⟨_, _, houterBox, hinnerBox, ?_⟩
  change (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH (shiftRect dx dy outerFrame))).Contained
    (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH (shiftRect dx dy innerFrame)))
  unfold Rect.Contained at hcontained ⊢
  unfold shiftRect orientRect
  cases o.direction <;> dsimp only <;> omega

theorem SceneExecution.nested_group_box_contained {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {parentKey childKey : Nat} {parentSource childSource : ModelBox}
    (hparentSource : inp.boxes[parentKey]? = some parentSource)
    (hchildSource : inp.boxes[childKey]? = some childSource)
    {parentNode childNode : Node}
    (hparentNode : execution.graph.nodes[parentKey]? = some parentNode)
    (hchildNode : execution.graph.nodes[childKey]? = some childNode)
    (hparentGroup : parentNode.border = -2) (hchildGroup : childNode.border = -2)
    (hparentRef : childSource.parent = parentSource.id) (hne : childSource.parent ≠ "") :
    ∃ parentBox childBox : Box,
      res.scene.layoutDump.box? parentSource.id = some parentBox ∧
      res.scene.layoutDump.box? childSource.id = some childBox ∧
      parentBox.rect.Contained childBox.rect := by
  obtain ⟨part, hpart, hparentIn, hchildIn⟩ := execution.group_parent_same_part hwf
    hparentNode hchildNode hparentGroup hchildGroup hparentSource hchildSource hparentRef hne
  obtain ⟨parentIndex, hparentKey⟩ := List.mem_iff_getElem?.mp hparentIn
  obtain ⟨childIndex, hchildKey⟩ := List.mem_iff_getElem?.mp hchildIn
  obtain ⟨parentFrame, childFrame, hparentFrame, hchildFrame, hcontained⟩ :=
    execution.part_nested_frames_contained hwf hpart hparentKey hchildKey hparentNode
      hchildNode hparentGroup hchildGroup hparentSource hchildSource hparentRef hne
  exact execution.scene_boxes_contained_of_part_frames hwf hpart hparentKey hchildKey
    hparentSource hchildSource hparentFrame hchildFrame hcontained

theorem SceneExecution.group_member_constraint_edge {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {groupKey memberKey : Nat} {groupNode memberNode : Node}
    (hgroupNode : execution.graph.nodes[groupKey]? = some groupNode)
    (hmemberNode : execution.graph.nodes[memberKey]? = some memberNode)
    (hgroup : groupNode.border = -2) (hplain : memberNode.border = 0)
    (hinside : memberNode.clusterPath.contains groupNode.decl = true) :
    (⟨groupKey, memberKey, 1, 0, false⟩ : Edge) ∈ Compound.constraints execution.graph := by
  obtain ⟨bottom, hbottom⟩ := execution.group_bottom_lookup hgroupNode hgroup
  exact (compound_member_constraint_edges (top := (groupNode, groupKey))
    (member := (memberNode, memberKey)) (List.mem_zipIdx_iff_getElem?.mpr hgroupNode)
    hgroup hbottom (List.mem_zipIdx_iff_getElem?.mpr hmemberNode) hplain hinside).1

theorem SceneExecution.member_box_contained {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {groupKey memberKey : Nat} {groupSource memberSource : ModelBox}
    (hgroupSource : inp.boxes[groupKey]? = some groupSource)
    (hmemberSource : inp.boxes[memberKey]? = some memberSource)
    {groupNode memberNode : Node}
    (hgroupNode : execution.graph.nodes[groupKey]? = some groupNode)
    (hmemberNode : execution.graph.nodes[memberKey]? = some memberNode)
    (hgroup : groupNode.border = -2) (hplain : memberNode.border = 0)
    (hinside : memberNode.clusterPath.contains groupNode.decl = true) :
    ∃ groupBox memberBox : Box,
      res.scene.layoutDump.box? groupSource.id = some groupBox ∧
      res.scene.layoutDump.box? memberSource.id = some memberBox ∧
      groupBox.rect.Contained memberBox.rect := by
  have hedge := execution.group_member_constraint_edge hgroupNode hmemberNode hgroup hplain
    hinside
  obtain ⟨comp, hcomp, hgroupIn, hmemberIn⟩ := components_edge_endpoints
    (sceneExecution_edges_bounded execution) (List.mem_append_right _ hedge)
  obtain ⟨hparts, _⟩ := actual_components_parts_geometry (by rfl) execution.components_eq
  have hmem : comp ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hparts]
    exact hcomp
  obtain ⟨part, hpart, hpartComp⟩ := List.mem_map.mp hmem
  have hgroupPart : groupKey ∈ part.1 := by
    rw [hpartComp]
    exact hgroupIn
  have hmemberPart : memberKey ∈ part.1 := by
    rw [hpartComp]
    exact hmemberIn
  obtain ⟨groupIndex, hgroupIndex⟩ := List.mem_iff_getElem?.mp hgroupPart
  obtain ⟨memberIndex, hmemberIndex⟩ := List.mem_iff_getElem?.mp hmemberPart
  obtain ⟨index, run, dx, dy, hcomponent, hrun, hframes⟩ := execution.part_frame_rects hpart
  have hlocalGroup := candidate_node_of_part_key (index := index) hgroupIndex hgroupNode
  have hlocalMember := candidate_node_of_part_key (index := index) hmemberIndex hmemberNode
  have hcontained := execution.component_member_contained hwf hcomponent hrun hlocalGroup
    hgroup hlocalMember hplain hinside
  refine execution.scene_boxes_contained_of_part_frames hwf hpart hgroupIndex hmemberIndex
    hgroupSource hmemberSource
    (hframes (List.getElem?_eq_some_iff.mp hlocalGroup).1)
    (hframes (List.getElem?_eq_some_iff.mp hlocalMember).1) ?_
  unfold Rect.Contained at hcontained ⊢
  unfold shiftRect
  dsimp only
  omega

theorem SceneExecution.graph_key_bound {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    {nodes : List Node} (hlength : nodes.length = execution.lines.length) :
    key < nodes.length := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    calc execution.lines.length = (inp.boxes.zipIdx).length := (mapM_getElem? _ _ _ h).1
         _ = inp.boxes.length := List.length_zipIdx
  rw [hlength, hlines]
  exact (List.getElem?_eq_some_iff.mp hsource).1

theorem SceneExecution.nonfixed_group_graph_node {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hgroup : source.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) :
    ∃ node : Node, execution.graph.nodes[key]? = some node ∧ node.border = -2 ∧
      node.decl = key := by
  obtain ⟨nodes, edges, titles, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hi : key < nodes.length := execution.graph_key_bound hsource hlength
  have hpreparedSource :
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[key]? = some source := by
    simp [List.getElem?_map, hsource, hfixed]
  have hrecord := Compound.prepare_group_title_record
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)
    execution.params.clusterPad titles
    { nodes := nodes, edges := edges, slot := execution.params.slot }
    hi hpreparedSource hgroup
  rw [← hprepared] at hrecord
  exact ⟨_, hrecord, rfl, (hmetadata key _ (List.getElem?_eq_getElem hi)).1⟩

theorem SceneExecution.plain_graph_node {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hplain : ¬(source.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false)) :
    ∃ node : Node, execution.graph.nodes[key]? = some node ∧ node.border = 0 ∧
      node.clusterPath = Compound.path inp.boxes source ∧ node.decl = key := by
  obtain ⟨nodes, edges, titles, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hi : key < nodes.length := execution.graph_key_bound hsource hlength
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hsource
  have hnotGroup : (if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true then
      { id := source.id, parent := source.parent, exclusive := source.exclusive,
        direction := source.direction, shape := source.shape, icon := source.icon,
        text := source.text } else source : ModelBox).role ≠ .group := by
    by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true
    · simp only [hf, ↓reduceIte]
      decide
    · have hf' : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false :=
        Bool.eq_false_iff.mpr hf
      simp only [hf]
      intro hrole
      exact hplain ⟨hrole, hf'⟩
  have hrecord := Compound.prepare_plain_node_record
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { id := box.id, parent := box.parent, exclusive := box.exclusive,
          direction := box.direction, shape := box.shape, icon := box.icon,
          text := box.text } else box)
    execution.params.clusterPad titles
    { nodes := nodes, edges := edges, slot := execution.params.slot }
    hi hchangedBox hnotGroup
  rw [← hprepared] at hrecord
  obtain ⟨hdecl, hborder⟩ := hmetadata key _ (List.getElem?_eq_getElem hi)
  exact ⟨_, hrecord, hborder, hpathMap, hdecl⟩


theorem SceneExecution.flat_parent_containment {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hparents : ∀ b ∈ inp.boxes, b.parent ≠ "" →
      ∃ p ∈ inp.boxes, p.id = b.parent ∧ p.role = .group ∧
        inp.fixedSizes.any (fun fixed => fixed.1 == p.id) = false) :
    Validator.C3 res.scene.layoutDump := by
  intro b hb hne p hp
  have hbMem : b ∈ res.scene.boxes := hb
  rw [execution.boxes_eq_map] at hbMem
  obtain ⟨⟨source, key⟩, hq, rfl⟩ := List.mem_map.mp hbMem
  have hsource : inp.boxes[key]? = some source := List.mem_zipIdx_iff_getElem?.mp hq
  have hparentNe : source.parent ≠ "" := hne
  obtain ⟨parentSource, hparentIn, hparentId, hparentRole, hparentFixed⟩ :=
    hparents source (List.mem_of_getElem? hsource) hparentNe
  obtain ⟨parentKey, hparentKey⟩ := List.mem_iff_getElem?.mp hparentIn
  have hids := Model.boxIds_nodup hwf
  have hparentLookup := execution.source_box_lookup_of_box_ids_nodup hids hparentKey
  have hchildLookup := execution.source_box_lookup_of_box_ids_nodup hids hsource
  change res.scene.layoutDump.box? source.parent = some p at hp
  rw [← hparentId, hparentLookup] at hp
  have hpEq := Option.some.inj hp
  subst hpEq
  obtain ⟨parentNode, hparentNode, hparentBorder, hparentDecl⟩ :=
    execution.nonfixed_group_graph_node hparentKey hparentRole hparentFixed
  by_cases hchildGroup : source.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false
  · obtain ⟨childNode, hchildNode, hchildBorder, _⟩ :=
      execution.nonfixed_group_graph_node hsource hchildGroup.1 hchildGroup.2
    obtain ⟨parentBox, childBox, hparentBox, hchildBox, hcontained⟩ :=
      execution.nested_group_box_contained hwf hparentKey hsource hparentNode hchildNode
        hparentBorder hchildBorder hparentId.symm hparentNe
    rw [hparentLookup] at hparentBox
    rw [hchildLookup] at hchildBox
    rw [← Option.some.inj hparentBox, ← Option.some.inj hchildBox] at hcontained
    exact hcontained
  · obtain ⟨childNode, hchildNode, hchildBorder, hchildPath, _⟩ :=
      execution.plain_graph_node hsource hchildGroup
    have hpath : Compound.path inp.boxes source =
        Compound.path inp.boxes parentSource ++ [parentKey] :=
      Compound.path_of_parent (inputModel inp o) hwf hparentKey hsource
        hparentId.symm hparentNe
    have hinside : childNode.clusterPath.contains parentNode.decl = true := by
      rw [List.contains_iff_mem, hchildPath, hparentDecl]
      change parentKey ∈ Compound.path inp.boxes source
      rw [hpath]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    obtain ⟨parentBox, memberBox, hparentBox, hmemberBox, hcontained⟩ :=
      execution.member_box_contained hwf hparentKey hsource hparentNode hchildNode
        hparentBorder hchildBorder hinside
    rw [hparentLookup] at hparentBox
    rw [hchildLookup] at hmemberBox
    rw [← Option.some.inj hparentBox, ← Option.some.inj hmemberBox] at hcontained
    exact hcontained

end Elegant.Layered.PipelineImpl

namespace Elegant.Layered

theorem layoutFamily_effective_endpoint_c5
    {inp : Input} {o : Options} {res : FamilyResult}
    (hfamily : layoutFamily inp o = .ok res)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hfrom : ∃ source ∈ (inputModel inp o).boxes, source.id = out.fromId ∧
      (source.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true))
    (hto : ∃ target ∈ (inputModel inp o).boxes, target.id = out.toId ∧
      (target.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == target.id) = true)) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  obtain ⟨hwf, hrecursive⟩ := layoutFamily_success hfamily
  exact PipelineImpl.layoutRecursive_effective_endpoint_c5 hwf hrecursive hout hfrom hto

theorem layoutFamily_ordinary_endpoint_c5
    {inp : Input} {o : Options} {res : FamilyResult}
    (hfamily : layoutFamily inp o = .ok res)
    {out : Route} (hout : out ∈ res.scene.routes)
    (hfrom : ∃ source ∈ (inputModel inp o).boxes,
      source.id = out.fromId ∧ source.role = .node)
    (hto : ∃ target ∈ (inputModel inp o).boxes,
      target.id = out.toId ∧ target.role = .node) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  obtain ⟨hwf, hrecursive⟩ := layoutFamily_success hfamily
  exact PipelineImpl.layoutRecursive_ordinary_endpoint_c5 hwf hrecursive hout hfrom hto

theorem layoutFamily_self_endpoint_c5
    {inp : Input} {o : Options} {res : FamilyResult}
    (hfamily : layoutFamily inp o = .ok res)
    {out : Route} (hout : out ∈ res.scene.routes) (hselfId : out.fromId = out.toId) :
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  obtain ⟨hwf, hrecursive⟩ := layoutFamily_success hfamily
  exact PipelineImpl.layoutRecursive_self_endpoint_c5 _ (Model.boxIds_nodup hwf)
    (PipelineImpl.input_routes_covered hwf) hrecursive hout hselfId

end Elegant.Layered

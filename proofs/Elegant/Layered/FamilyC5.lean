import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.StraightenFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The flat group-endpoint attachment fact, stated exactly as
`componentRun_group_route_attachment` will conclude it: the same statement as
`componentRun_ordinary_route_attachment` without the `hsource`/`htarget`
plainness premises.  An endpoint whose graph node carries `border = -2`
attaches to the *frame* `frameRect P cg run v`; a plain endpoint's `frameRect`
collapses to `boxRect`, so one statement covers both.  This is a hypothesis
until the sibling `componentRun_group_route_attachment` lands; every consumer
below takes it as an explicit premise. -/
def GroupAttach : Prop :=
  ∀ {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < cg.edges.length) {first last : Nat}
    (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last)
    (cursor : Int) (loops : List (Nat × LoopPlacement))
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (margin : Int) (direction : Direction) (canvasH boxX boxY : Int),
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
      Validator.onBoundary (transport finish) (transportRect (if reversed then source else target))

/-- Universal anchor identification: in every successful flat execution, for
every component part and every proper (non-self) candidate edge, the
candidate-local endpoint indices resolve to the model endpoint boxes of the
declared route.  Semantic-edge normalization may rewrite a group anchor to a
containing member, so this identification is not available unconditionally;
it is the second standing hypothesis of the group-endpoint C5 lift, next to
`GroupAttach`. -/
def GroupAnchors : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult},
    ∀ (execution : SceneExecution inp o res) (packed : Pack.State),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    ∀ {c : Nat} {q : (List Nat × Part) × Rect},
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    ∀ {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int},
    componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        = .ok loops →
    q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area } →
    ∀ {i : Nat} {edge : Edge},
    (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge →
    edge.tail ≠ edge.head →
    ∃ (idxF idxT : Nat) (sF sT : ModelBox) (r : ModelRoute),
      q.1.1[(if edge.reversed then edge.head else edge.tail)]? = some idxF ∧
      inp.boxes[idxF]? = some sF ∧
      q.1.1[(if edge.reversed then edge.tail else edge.head)]? = some idxT ∧
      inp.boxes[idxT]? = some sT ∧
      inp.routes[edge.decl]? = some r ∧
      sF.id = r.fromId ∧ sT.id = r.toId

/-- Every scene route attaches both endpoints to the boundary of its `from`/`to`
dump boxes, provided the flat group-attachment fact holds.  This is the
remaining C5 case: node and fixed-size endpoints are already covered by
`layoutRecursive_effective_endpoint_c5`, self loops by
`layoutRecursive_self_endpoint_c5`; this invariant covers a non-fixed group
endpoint by descending through `expandChild` exactly as the node-endpoint
invariant does. -/
def GroupEndpointInvariant (inp : Input) (scene : Scene) : Prop :=
  ∀ out ∈ scene.routes,
    ∃ source ∈ inp.boxes, ∃ target ∈ inp.boxes,
      source.id = out.fromId ∧ target.id = out.toId ∧
      ∃ (start finish : Point) (fromBox toBox : Box),
        out.points.head? = some start ∧ out.points.getLast? = some finish ∧
        scene.layoutDump.box? out.fromId = some fromBox ∧
        scene.layoutDump.box? out.toId = some toBox ∧
        Validator.onBoundary start fromBox.rect ∧
        Validator.onBoundary finish toBox.rect

/-- An endpoint computed below `boxes.length` must come from its own input
index; mirrors the private `compound_endpoint_preimage` of
ExecutedLoopPortsFacts, which is not exported. -/
private theorem selfPreimage {boxes : List ModelBox} (source : Bool)
    (index other v : Nat) (hv : v < boxes.length)
    (h : Compound.endpoint boxes source index other = v) : index = v := by
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

/-- `bottomIndex` is strictly increasing past a group box. -/
private theorem selfBottomIndex_lt {boxes : List ModelBox} {i j : Nat} (hij : i < j)
    (_hi : i < boxes.length) {bi : ModelBox} (hbi : boxes[i]? = some bi)
    (hg : bi.role == .group) :
    Compound.bottomIndex boxes i < Compound.bottomIndex boxes j := by
  unfold Compound.bottomIndex
  have h1 : (boxes.take j).take i ++ (boxes.take j).drop i = boxes.take j :=
    List.take_append_drop i (boxes.take j)
  have h2 : (boxes.take j).take i = boxes.take i := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  have h3 := congrArg (List.filter (fun box : ModelBox => box.role == .group)) h1
  rw [List.filter_append, h2] at h3
  have hmem : bi ∈ (boxes.take j).drop i := by
    have h0 : ((boxes.take j).drop i)[0]? = some bi := by
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_take, ite_eq_left hij, hbi]
    exact List.mem_of_getElem? h0
  have hfilter : 0 < (((boxes.take j).drop i).filter
      (fun box : ModelBox => box.role == .group)).length := by
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hmem, hg⟩
  rw [h3.symm, List.length_append]
  omega

set_option maxHeartbeats 1000000 in
/-- Two distinct indices cannot map to the same relabeled endpoint: when the
shared value stays below the box list it is both inputs (`selfPreimage`);
beyond the box list it is `bottomIndex`, which is strictly increasing past a
group box. -/
private theorem selfBottom_ne {boxes : List ModelBox} {a b k : Nat}
    (ha : a < boxes.length) (hb : b < boxes.length) (hab : a ≠ b)
    (ea : Compound.endpoint boxes true a b = k)
    (eb : Compound.endpoint boxes false b a = k)
    (hk : ¬ k < boxes.length) : False := by
  cases hma : boxes[a]? with
  | none =>
    simp only [Compound.endpoint, hma] at ea
    exact hk (by rw [← ea]; exact ha)
  | some ba =>
    cases hmb : boxes[b]? with
    | none =>
      simp only [Compound.endpoint, hma, hmb] at ea eb
      exact hk (by rw [← eb]; exact hb)
    | some bb =>
      simp only [Compound.endpoint, hma, hmb] at ea eb
      split at ea
      · exact hk (by rw [← ea]; exact ha)
      · split at ea
        · exact hk (by rw [← ea]; exact ha)
        · rename_i hc1 hc2
          split at eb
          · exact hk (by rw [← eb]; exact hb)
          · split at eb
            · exact hk (by rw [← eb]; exact hb)
            · rename_i hc3 _
              have hgrpA : (ba.role == .group) = true := by
                have hf := Bool.eq_false_iff.mpr hc1
                have hp := (Bool.or_eq_false_iff.mp hf).1
                simpa using hp.symm
              have hgrpB : (bb.role == .group) = true := by
                have hf := Bool.eq_false_iff.mpr hc3
                have hp := (Bool.or_eq_false_iff.mp hf).1
                simpa using hp.symm
              rcases Nat.lt_or_ge a b with hcmp | hcmp
              · have hbound := selfBottomIndex_lt hcmp ha hma hgrpA
                rw [ea, eb] at hbound
                exact absurd hbound (Nat.lt_irrefl k)
              · have hblt : b < a := by omega
                have hbound := selfBottomIndex_lt hblt hb hmb hgrpB
                rw [eb, ea] at hbound
                exact absurd hbound (Nat.lt_irrefl k)

set_option maxHeartbeats 900000 in
/-- Converse of `componentCandidate_self_model_key`: a component-local self
loop comes from a semantic self edge, so the model route joins one box with
itself. -/
private theorem component_self_route_ids
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph} (hgraph : measuredGraph P inp o lines = .ok graph)
    {component : List Nat} {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    (hrun : componentRun P (componentCandidate graph component candidate) labels
      (candidateOrder candidate) = .ok run)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate graph component candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head) :
    ∃ (index : Nat) (route : ModelRoute) (raw : Edge) (source : ModelBox),
      inp.routes[index]? = some route ∧ edge.decl = index ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      route.fromId = route.toId := by
  obtain ⟨index, route, raw, source, target, hroute, hraw, hdecl, hsource, hsourceId,
    htarget, htargetId, hsemantic⟩ :=
    componentCandidate_model_endpoint_source hgraph (List.mem_of_getElem? hedge)
  refine ⟨index, route, raw, source, hroute, hdecl, hsource, hsourceId, ?_⟩
  obtain ⟨ranks, normalized, hn, _, _⟩ := componentRun_normalized_source hrun
  have hwf := (normalize_node_rank_alignment hn).2
  have hbounds := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
  have hlen : (componentCandidate graph component candidate).nodes.length =
      component.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have horigEq : edge.original.tail = edge.original.head := by
    unfold Edge.original
    split <;> simp only [hself]
  have ht := congrArg Edge.tail hsemantic
  have hh := congrArg Edge.head hsemantic
  dsimp only at ht hh
  let prepared : List ModelBox := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
    else box
  let alias := Compound.aliasEdge prepared raw
  have haliasEq : alias = Compound.aliasEdge prepared raw := rfl
  have hht : edge.original.tail = component.idxOf alias.tail := by
    simpa only [alias, prepared] using ht
  have hhh : edge.original.head = component.idxOf alias.head := by
    simpa only [alias, prepared] using hh
  rw [horigEq] at hht
  have hidx : component.idxOf alias.tail = component.idxOf alias.head :=
    hht.symm.trans hhh
  have hv : component.idxOf alias.tail < component.length := by
    cases hr : edge.reversed with
    | false =>
      have h1 : component.idxOf alias.tail = edge.head := by
        rw [← hht]
        simp [Edge.original, hr]
      have hb := hbounds.2.1
      have hb' : edge.head < (componentCandidate graph component candidate).nodes.length := by
        have hsucc : edge.head.succ.le (componentCandidate graph component candidate).nodes.length := hb
        omega
      rw [hlen] at hb'
      exact h1 ▸ hb'
    | true =>
      have h1 : component.idxOf alias.tail = edge.tail := by
        rw [← hht]
        simp [Edge.original, hr]
      have hb := hbounds.1
      have hb' : edge.tail < (componentCandidate graph component candidate).nodes.length := by
        have hsucc : edge.tail.succ.le (componentCandidate graph component candidate).nodes.length := hb
        omega
      rw [hlen] at hb'
      exact h1 ▸ hb'
  have hv2 : component.idxOf alias.head < component.length := hidx ▸ hv
  have haliasEq' : alias.tail = alias.head := by
    have h1 : component[component.idxOf alias.tail]? = some alias.tail := by
      rw [List.getElem?_eq_getElem]
      · exact congrArg some (List.getElem_idxOf hv)
      · exact hv
    have h2 : component[component.idxOf alias.head]? = some alias.head := by
      rw [List.getElem?_eq_getElem]
      · exact congrArg some (List.getElem_idxOf hv2)
      · exact hv2
    rw [hidx] at h1
    have : alias.tail = alias.head := Option.some.inj (h1.symm.trans h2)
    exact this
  have hlenPrep : prepared.length = inp.boxes.length := List.length_map _
  by_cases hk : alias.tail < inp.boxes.length
  · have htailE : Compound.endpoint prepared true raw.tail raw.head = alias.tail := by
      have h1 : (Compound.aliasEdge prepared raw).tail =
          Compound.endpoint prepared true raw.tail raw.head := rfl
      have h2 : alias.tail = (Compound.aliasEdge prepared raw).tail :=
        congrArg Edge.tail haliasEq
      rw [h1] at h2
      exact h2.symm
    have hheadE : Compound.endpoint prepared false raw.head raw.tail = alias.tail := by
      have h1 : (Compound.aliasEdge prepared raw).head =
          Compound.endpoint prepared false raw.head raw.tail := rfl
      have h2 : alias.head = (Compound.aliasEdge prepared raw).head :=
        congrArg Edge.head haliasEq
      rw [h1] at h2
      exact h2.symm.trans haliasEq'.symm
    have e1 : raw.tail = alias.tail :=
      selfPreimage true raw.tail raw.head alias.tail
        (by rw [hlenPrep]; exact hk) htailE
    have e2 : raw.head = alias.tail :=
      selfPreimage false raw.head raw.tail alias.tail
        (by rw [hlenPrep]; exact hk) hheadE
    have hsource' : inp.boxes[raw.head]? = some source := by
      rw [e2]
      have hcopy := hsource
      rw [e1] at hcopy
      exact hcopy
    have heq : target = source := Option.some.inj (htarget.symm.trans hsource')
    exact hsourceId.symm.trans ((congrArg ModelBox.id heq.symm).trans htargetId)
  · have hrt : raw.tail < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
    have hhd : raw.head < inp.boxes.length := (List.getElem?_eq_some_iff.mp htarget).1
    by_cases hneRaw : raw.tail = raw.head
    · have hsource' : inp.boxes[raw.head]? = some source := by
        rw [← hneRaw]; exact hsource
      have heq : target = source := Option.some.inj (htarget.symm.trans hsource')
      exact hsourceId.symm.trans ((congrArg ModelBox.id heq.symm).trans htargetId)
    · have hk' : ¬ alias.tail < prepared.length := by rw [hlenPrep]; exact hk
      have ea : Compound.endpoint prepared true raw.tail raw.head = alias.tail := by
        have h1 : (Compound.aliasEdge prepared raw).tail =
            Compound.endpoint prepared true raw.tail raw.head := rfl
        have h2 : alias.tail = (Compound.aliasEdge prepared raw).tail :=
          congrArg Edge.tail haliasEq
        rw [h1] at h2
        exact h2.symm
      have eb : Compound.endpoint prepared false raw.head raw.tail = alias.tail := by
        have h1 : (Compound.aliasEdge prepared raw).head =
            Compound.endpoint prepared false raw.head raw.tail := rfl
        have h2 : alias.head = (Compound.aliasEdge prepared raw).head :=
          congrArg Edge.head haliasEq
        rw [h1] at h2
        exact h2.symm.trans haliasEq'.symm
      exact False.elim (selfBottom_ne (boxes := prepared)
        (by rw [hlenPrep]; exact hrt) (by rw [hlenPrep]; exact hhd) hneRaw ea eb hk')

/-- Group-endpoint attachment at the scene level: the chosen component's route
entry supplies the emitted scene route and the transported endpoint points,
`GroupAttach` supplies the two `onBoundary` facts (frames for `border = -2`
nodes, plain boxes otherwise), and the packed frame entries identify the dump
boxes.  This is the group analog of `chosen_part_effective_c5_of_box_ids_nodup`;
it needs no role premises, so it covers exactly the remaining case where one
endpoint is a non-fixed group. -/
theorem SceneExecution.chosen_part_group_c5_of_box_ids_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (hattach : GroupAttach)
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
    (hne : edge.tail ≠ edge.head)
    {idxF idxT : Nat} {sF sT : ModelBox} {rF rT : ModelRoute}
    (hfromKey : q.1.1[(if edge.reversed then edge.head else edge.tail)]? = some idxF)
    (hsourceM : inp.boxes[idxF]? = some sF)
    (hrouteF : inp.routes[edge.decl]? = some rF)
    (hsourceId : sF.id = rF.fromId)
    (htoKey : q.1.1[(if edge.reversed then edge.tail else edge.head)]? = some idxT)
    (htargetM : inp.boxes[idxT]? = some sT)
    (hrouteT : inp.routes[edge.decl]? = some rT)
    (htargetId : sT.id = rT.toId) :
    ∃ (out : Route) (start finish : Point) (fromBox toBox : Box),
      res.scene.routes[edge.decl]? = some out ∧
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  let cg := componentCandidate execution.graph q.1.1 candidate
  have hmem : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
  have hP := checkedParams_valid execution.checked
  have hshape : CgShape cg := componentCandidate_shape
    (components_nodup execution.graph q.1.1
      ((actual_components_parts (by rfl) execution.components_eq).1 ▸
        List.mem_map_of_mem hmem)) (measuredGraph_shape execution.graph_eq) candidate
  obtain ⟨first, last, hfirst, hlast, htail, hhead⟩ :=
    componentRun_chain_endpoints hP hnd hshape hrun hedge hne
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have hdeclEq : (cg.edges[i]'hi).decl = edge.decl := by
    have h1 : cg.edges[i]? = some (cg.edges[i]'hi) := List.getElem?_eq_getElem hi
    have h2 : cg.edges[i]? = some edge := hedge
    rw [h1] at h2
    exact congrArg Edge.decl (Option.some.inj h2)
  have hlo : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]'hi).decl := by
    intro l hl
    rw [hdeclEq]
    exact componentLoops_excludes_ordinary_decl hloops hnd hedge hne l hl
  obtain ⟨rt, start, finish, hget, hor, hplaced, hstart, hfinish, hports⟩ :=
    hattach hrun hi hfirst hlast 0 loops (fun l hl => hlo l hl)
      execution.params.canvasMargin o.direction execution.packedAcc.canvasH q.2.x q.2.y
  obtain ⟨modelRoute, native, hmodelRoute, hnative, horiginal, hscene⟩ :=
    execution.chosen_part_route_entry packed hpacked hselected hrun hpart hedge
      (fun l hl => by
        rw [← hdeclEq]
        exact hlo l hl)
  have hsuff : res.scene.routes[edge.decl]? =
      some (Route.mk modelRoute.id modelRoute.fromId modelRoute.toId modelRoute.orthogonal
        (native.points.map (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBounds execution.params cg run execution.measured loops).minX
          (placeBounds execution.params cg run execution.measured loops).minY))) →
      ∃ (out : Route) (start finish : Point) (fromBox toBox : Box),
        res.scene.routes[edge.decl]? = some out ∧
        out.points.head? = some start ∧ out.points.getLast? = some finish ∧
        res.scene.layoutDump.box? out.fromId = some fromBox ∧
        res.scene.layoutDump.box? out.toId = some toBox ∧
        Validator.onBoundary start fromBox.rect ∧
        Validator.onBoundary finish toBox.rect := by
    intro hscene0
    {
  have hsame : rt = native := Option.some.inj (hget.symm.trans hnative)
  subst rt
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hedge,
    Option.map_some, Option.getD_some, htail, hhead] at hports
  have hrF : rF = modelRoute := Option.some.inj (hrouteF.symm.trans hmodelRoute)
  have hrT : rT = modelRoute := Option.some.inj (hrouteT.symm.trans hmodelRoute)
  rw [hrF] at hsourceId
  rw [hrT] at htargetId
  have hfromEntry := chosen_part_frame_entry hpart hfromKey
  have htoEntry := chosen_part_frame_entry hpart htoKey
  have hfromLookup := execution.part_entry_box_lookup_of_box_ids_nodup hids packed
    hpacked hselected hfromEntry hsourceM
  have htoLookup := execution.part_entry_box_lookup_of_box_ids_nodup hids packed
    hpacked hselected htoEntry htargetM
  rw [shiftRect_pack_normalize] at hfromLookup htoLookup
  let bounds := placeBounds execution.params cg run execution.measured loops
  let transport := routePointTransport execution.params.canvasMargin o.direction
    execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
  let transportRect := fun rect =>
    shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect (q.2.x - bounds.minX) (q.2.y - bounds.minY) rect))
  cases hr : edge.reversed
  · simp only [hr] at hports hfromLookup htoLookup
    refine ⟨Route.mk modelRoute.id modelRoute.fromId modelRoute.toId modelRoute.orthogonal
        (native.points.map transport), transport start, transport finish,
      Box.mk sF.id sF.role.id (transportRect (frameRect execution.params cg run edge.tail))
        sF.parent sF.exclusive,
      Box.mk sT.id sT.role.id (transportRect (frameRect execution.params cg run edge.head))
        sT.parent sT.exclusive,
      hscene0, ?_, ?_, ?_, ?_, hports.1, hports.2⟩
    · simp only [List.head?_map, hstart, Option.map_some]
    · simp only [List.getLast?_map, hfinish, Option.map_some]
    · rw [← hsourceId]
      exact hfromLookup
    · rw [← htargetId]
      exact htoLookup
  · simp only [hr] at hports hfromLookup htoLookup
    refine ⟨Route.mk modelRoute.id modelRoute.fromId modelRoute.toId modelRoute.orthogonal
        (native.points.map transport), transport start, transport finish,
      Box.mk sF.id sF.role.id (transportRect (frameRect execution.params cg run edge.head))
        sF.parent sF.exclusive,
      Box.mk sT.id sT.role.id (transportRect (frameRect execution.params cg run edge.tail))
        sT.parent sT.exclusive,
      hscene0, ?_, ?_, ?_, ?_, hports.1, hports.2⟩
    · simp only [List.head?_map, hstart, Option.map_some]
    · simp only [List.getLast?_map, hfinish, Option.map_some]
    · rw [← hsourceId]
      exact hfromLookup
    · rw [← htargetId]
      exact htoLookup
    }
  rcases hscene with hscene | _hcorr
  · exact hsuff hscene
  -- Corridor case is second: resplit the corridor route via route_cases.
  case inr =>
    obtain ⟨_pts, _hcor, _hrouteC⟩ := _hcorr
    obtain ⟨_x, _y₀, _y₁, _hlt, _hptsEq⟩ := _hcor
    have _hi : i < (componentCandidate execution.graph q.1.1 candidate).edges.length :=
      (List.getElem?_eq_some_iff.mp hedge).1
    have _hk' : edge.decl < inp.routes.length := by
      have _heP := (List.getElem?_eq_some_iff.mp hedge).2
      rw [← _heP]
      exact componentCandidate_edge_index_decl_lt execution.graph_eq q.1.1 candidate _hi
    have _hstraight := sceneOf_routes_getElem? execution.params inp o execution.lines
      execution.straightAcc execution.measured edge.decl _hk'
    rw [← execution.scene_eq] at _hstraight
    rw [execution.straight_canvasH] at _hstraight
    have _hgetD : execution.straightAcc.routes.getD edge.decl [] = _pts :=
      execution.straight_points_of_scene _hrouteC
    have hpts : execution.straightAcc.routes[edge.decl]? = some _pts := by
      have _hne : _pts ≠ [] := by
        rw [_hptsEq]
        intro _hcon
        simp at _hcon
      have _hgd : (execution.straightAcc.routes[edge.decl]?.getD []) = _pts := by
        have _h := _hgetD
        rw [Array.getD_eq_getD_getElem?] at _h
        exact _h
      cases _ho : execution.straightAcc.routes[edge.decl]? with
      | none =>
        simp only [_ho, Option.getD_none] at _hgd
        exact absurd _hgd.symm _hne
      | some _v =>
        simp only [_ho, Option.getD_some] at _hgd
        exact congrArg Option.some _hgd
    rcases SceneExecution.route_cases execution hpts with _hpackedPts | hinst
    · -- (P) packed corridor: the packed route equals the corridor points, so the
      -- placed-points bridge turns _hrouteC into the first-disjunct form reused via hsuff.
      have _heP := (List.getElem?_eq_some_iff.mp hedge).2
      have _hgetP := placeComponent_route_entry_of_producer hrun 0 loops i hi hlo
      have _hpartRoutes : q.1.2.routes =
          (placeComponent execution.params cg run 0 execution.measured loops).routes := by
        rw [hpart]
      rw [← _hpartRoutes] at _hgetP
      have _hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
        rw [_hpartRoutes]
        exact placeComponent_routes_decls_nodup execution.params cg run 0
          execution.measured loops hnd
      have _hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
        rw [← Elegant.Layered.packAcc_routes_size execution.packed_eq]
        exact (Array.getElem?_eq_some_iff.mp _hpackedPts).1
      have _hpackedRoute := Elegant.Layered.actual_components_packAcc_routes_getD
        (by rfl) execution.components_eq (measuredGraph_decls_nodup execution.graph_eq)
        packed execution.packed_eq hpacked c q hselected i _ _ [] _hgetP _hpartNodup (by rw [_heP]; exact _hrouteSize)
      have _hnativeGet := (List.getElem?_eq_some_iff.mp hnative).2
      have _hmodelEq : inp.routes[edge.decl]'_hk' = modelRoute :=
        Option.some.inj ((List.getElem?_eq_getElem _hk').symm.trans hmodelRoute)
      have _hbridge : execution.packedAcc.routes.getD edge.decl [] =
          execution.straightAcc.routes.getD edge.decl [] := by
        rw [_hgetD, Array.getD_eq_getD_getElem?, _hpackedPts, Option.getD_some]
      rw [_heP, _hbridge] at _hpackedRoute
      rw [_hmodelEq] at _hstraight
      rw [_hpackedRoute, routePointTransport_eq, _hnativeGet] at _hstraight
      exact hsuff _hstraight
    · -- (I) installed corridor: the installer's part-vertex keys name the packed
      -- rectangles carrying the corridor endpoints; the endpoint model boxes and
      -- the scene transport then give the witness.
      obtain ⟨tailKey, headKey, tailRect, headRect, span,
          _hTailLt, _hHeadLt, hT, hH, hKeyT, hKeyH,
          htailRect, hheadRect, h0tail, h0head,
          _htx, _htw, _hhx, _hhw,
          hxT1, hxT2, hxH1, hxH2, hy0eq, hy1eq, hptsEq⟩ :=
        execution.installed_part_edge_rects hinst hselected hedge rfl hrun hpart
      obtain ⟨hfromId, htoId⟩ :=
        execution.installed_part_edge_key_ids hinst hselected hedge rfl hrun hpart
          hmodelRoute hT hH hKeyT hKeyH
      have hptsEq2 : _pts = [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] :=
        hptsEq
      have hsourceTail : inp.boxes[tailKey]? = some (inp.boxes[tailKey]'hT) :=
        List.getElem?_eq_getElem hT
      have hsourceHead : inp.boxes[headKey]? = some (inp.boxes[headKey]'hH) :=
        List.getElem?_eq_getElem hH
      have htailGetD : execution.packedAcc.rects.getD tailKey default = tailRect := by
        simp only [Array.getD_eq_getD_getElem?, htailRect, Option.getD_some]
      have hheadGetD : execution.packedAcc.rects.getD headKey default = headRect := by
        simp only [Array.getD_eq_getD_getElem?, hheadRect, Option.getD_some]
      have hlookupTail := execution.source_box_lookup_of_box_ids_nodup hids hsourceTail
      have hlookupHead := execution.source_box_lookup_of_box_ids_nodup hids hsourceHead
      rw [htailGetD] at hlookupTail
      rw [hheadGetD] at hlookupHead
      have hb := corridor_onBoundary_acc h0tail h0head ⟨hxT1, hxT2⟩ ⟨hxH1, hxH2⟩ hy0eq hy1eq
      have hbScene := corridor_onBoundary_scene (margin := execution.params.canvasMargin)
        (d := o.direction) (h := execution.packedAcc.canvasH) hb
      have hptsMap : (_pts.map fun p => shiftPoint execution.params.canvasMargin
          execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)) =
          [(shiftPoint execution.params.canvasMargin execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH ⟨span.column, span.top⟩)),
           (shiftPoint execution.params.canvasMargin execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH ⟨span.column, span.bottom⟩))] := by
        simp only [hptsEq2, List.map_cons, List.map_nil]
      refine ⟨Route.mk modelRoute.id modelRoute.fromId modelRoute.toId modelRoute.orthogonal
          (_pts.map fun p => shiftPoint execution.params.canvasMargin
            execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH p)),
          (shiftPoint execution.params.canvasMargin execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH ⟨span.column, span.top⟩)),
          (shiftPoint execution.params.canvasMargin execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH ⟨span.column, span.bottom⟩)),
          { id := (inp.boxes[tailKey]'hT).id, role := (inp.boxes[tailKey]'hT).role.id,
            rect := shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH tailRect),
            parent := (inp.boxes[tailKey]'hT).parent, exclusive := (inp.boxes[tailKey]'hT).exclusive },
          { id := (inp.boxes[headKey]'hH).id, role := (inp.boxes[headKey]'hH).role.id,
            rect := shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH headRect),
            parent := (inp.boxes[headKey]'hH).parent, exclusive := (inp.boxes[headKey]'hH).exclusive },
          _hrouteC, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hptsMap]; rfl
      · rw [hptsMap]; rfl
      · rw [← hfromId]; exact hlookupTail
      · rw [← htoId]; exact hlookupHead
      · exact hbScene.1
      · exact hbScene.2

/-- The flat scene invariant, under the group-attachment hypothesis: a plain
`layout` covers every route endpoint, because the ordinary case is
`chosen_part_effective_c5_of_box_ids_nodup` (node/fixed endpoints), the
self-loop case is `self_routes_c5_of_box_ids_nodup`, and the group case is the
`chosen_part_group_c5_of_box_ids_nodup` analog above. -/
theorem SceneExecution.group_endpoint_source_invariant
    {inp : Input} {o : Options} {res : FamilyResult}
    (hattach : GroupAttach) (hanchors : GroupAnchors)
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup) (_hcovered : RoutesCovered inp) :
    GroupEndpointInvariant inp res.scene := by
  intro out hout
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
  by_cases hself : edge.tail = edge.head
  · -- Self loop: the semantic route joins one box with itself, so both ends
    -- land on the same dump box, whatever the roles are.
    obtain ⟨index, route, _raw, source, hroute, hdeclIndex, hsourceBox, hsourceId,
      hrouteSelf⟩ :=
      component_self_route_ids execution.graph_eq hrun hedge hself
    have hindex : index = key := hdeclIndex.symm.trans hdecl
    rw [hindex] at hroute
    have hrouteEq : route = modelRoute := Option.some.inj (hroute.symm.trans hmodel)
    subst route
    refine ⟨source, List.mem_of_getElem? hsourceBox, source,
      List.mem_of_getElem? hsourceBox, hsourceId.trans hfromId.symm,
      hsourceId.trans (hrouteSelf.trans htoId.symm), ?_⟩
    exact execution.self_routes_c5_of_box_ids_nodup hids hout
      (hfromId.trans (hrouteSelf.trans htoId.symm))
  · -- Proper edge: the group analog covers every endpoint role.
    obtain ⟨_idxF, _idxT, sF, sT, rDecl, hfromKey, hsourceM, htoKey, htargetM,
      hrouteD, hsourceIdD, htargetIdD⟩ :=
      hanchors execution packed hpacked hselected hrun hloops hpart hedge hself
    obtain ⟨out', start, finish, fromBox, toBox, hemitted, hstart, hfinish,
      hfromLookup, htoLookup, hfromBoundary, htoBoundary⟩ :=
      execution.chosen_part_group_c5_of_box_ids_nodup hattach hids packed hpacked
        hselected hrun hloops hpart hedge hself
        hfromKey hsourceM hrouteD hsourceIdD htoKey htargetM hrouteD htargetIdD
    rw [hdecl] at hemitted hrouteD
    have hrouteEq : rDecl = modelRoute :=
      Option.some.inj (hrouteD.symm.trans hmodel)
    subst rDecl
    have hsame' : out' = out := Option.some.inj (hemitted.symm.trans houtIndex)
    subst out'
    exact ⟨sF, List.mem_of_getElem? hsourceM, sT, List.mem_of_getElem? htargetM,
      hsourceIdD.trans hfromId.symm, htargetIdD.trans htoId.symm,
      start, finish, fromBox, toBox, hstart, hfinish, hfromLookup, htoLookup,
      hfromBoundary, htoBoundary⟩

/-- Recursive group-endpoint invariant: mirrors
`layoutRecursive_effective_endpoint_source_invariant`.  The flat base case is
`SceneExecution.group_endpoint_source_invariant`; the embedding case follows
`expandChild`'s route assembly, shifting child endpoints and keeping parent
endpoints, both of which keep the invariant. -/
theorem layoutRecursive_group_endpoint_source_invariant
    (hattach : GroupAttach) (hanchors : GroupAnchors)
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hboxIds : (inp.boxes.map (·.id)).Nodup)
    (hrouteIds : (inp.routes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hrecursive : layoutRecursive fuel inp o = .ok res) :
    GroupEndpointInvariant inp res.scene := by
  have hbase : ∀ {input : Input} {options : Options} {result : FamilyResult},
      (input.boxes.map (·.id)).Nodup → RoutesCovered input →
      layout input options = .ok result →
      GroupEndpointInvariant input result.scene := by
    intro input options result hids hcoverage hrun
    obtain ⟨execution⟩ := layout_sceneExecution hrun
    exact execution.group_endpoint_source_invariant hattach hanchors hids hcoverage
  induction fuel generalizing inp o res with
  | zero => exact hbase hboxIds hcovered hrecursive
  | succ fuel ih =>
    rcases layoutRecursive_succ hrecursive with ⟨_, hflat⟩ |
      ⟨group, hgroup, _, _, _, _, _, _, _, _, _, _⟩
    · exact hbase hboxIds hcovered hflat
    · obtain ⟨P, height, child, parent, sizes, children, areas, dx, dy,
        hchild, hparent, hexpand, hchildLookup, hparentLookup, hroutes⟩ :=
        layoutRecursive_embedding_box_lookup_of_endpoint_invariants
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
        obtain ⟨start, finish, fromBox, toBox, hstart, hfinish,
          hfrom, hto, hfromBoundary, htoBoundary⟩ := hports
        refine ⟨shiftPoint dx dy start, shiftPoint dx dy finish,
          { fromBox with rect := shiftRect dx dy fromBox.rect, parent := if fromBox.parent == "" then group.id else fromBox.parent },
          { toBox with rect := shiftRect dx dy toBox.rect, parent := if toBox.parent == "" then group.id else toBox.parent },
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.head?_map, hstart, Option.map_some]
        · simp only [List.getLast?_map, hfinish, Option.map_some]
        · have hfromBoxId : fromBox.id = native.fromId :=
            beq_iff_eq.mp (List.find?_some
              (p := fun (box : Box) => box.id == native.fromId) hfrom)
          rw [← hfromBoxId]
          exact hchildLookup fromBox
            (by rw [hfromBoxId]; exact hfrom)
        · have htoBoxId : toBox.id = native.toId :=
            beq_iff_eq.mp (List.find?_some
              (p := fun (box : Box) => box.id == native.toId) hto)
          rw [← htoBoxId]
          exact hchildLookup toBox
            (by rw [htoBoxId]; exact hto)
        · exact (onBoundary_shift dx dy start fromBox.rect).mpr hfromBoundary
        · exact (onBoundary_shift dx dy finish toBox.rect).mpr htoBoundary
      · obtain ⟨selectedSource, hselectedSource, selectedTarget, hselectedTarget,
          hfromId, htoId, hports⟩ := hp out hunchanged
        obtain ⟨source, hsource, hsId, _⟩ :=
          lift (fun box => !Compound.inside inp.boxes group.id box.id) "" _
            hselectedSource
        obtain ⟨target, htarget, htId, _⟩ :=
          lift (fun box => !Compound.inside inp.boxes group.id box.id) "" _
            hselectedTarget
        refine ⟨source, hsource, target, htarget, hsId.trans hfromId,
          htId.trans htoId, ?_⟩
        obtain ⟨start, finish, fromBox, toBox, hstart, hfinish,
          hfrom, hto, hfromBoundary, htoBoundary⟩ := hports
        refine ⟨start, finish, fromBox, toBox, hstart, hfinish, ?_, ?_,
          hfromBoundary, htoBoundary⟩
        · have hfromBoxId : fromBox.id = out.fromId :=
            beq_iff_eq.mp (List.find?_some
              (p := fun (box : Box) => box.id == out.fromId) hfrom)
          have hself : parent.scene.layoutDump.box? fromBox.id = some fromBox := by
            rw [hfromBoxId]
            exact hfrom
          rw [← hfromBoxId]
          exact hparentLookup fromBox hself
        · have htoBoxId : toBox.id = out.toId :=
            beq_iff_eq.mp (List.find?_some
              (p := fun (box : Box) => box.id == out.toId) hto)
          have hself : parent.scene.layoutDump.box? toBox.id = some toBox := by
            rw [htoBoxId]
            exact hto
          rw [← htoBoxId]
          exact hparentLookup toBox hself

end Elegant.Layered.PipelineImpl

namespace Elegant.Layered

/-- Clause C5 for a successful `layoutFamily`, contingent on the flat
group-endpoint attachment fact `GroupAttach`.  Every route's first point lies
on the boundary of its `from` box and its last point on the boundary of its
`to` box in the layout dump, whatever the endpoint roles are: node and
fixed-size endpoints come from `layoutFamily_effective_endpoint_c5`, self
loops from `layoutFamily_self_endpoint_c5`, and non-fixed group endpoints from
the recursive group invariant above. -/
theorem layoutFamily_c5 (hattach : PipelineImpl.GroupAttach)
    (hanchors : PipelineImpl.GroupAnchors)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hfamily : layoutFamily inp o = .ok res) :
    Validator.C5 res.scene.layoutDump := by
  obtain ⟨hwf, hrecursive⟩ := layoutFamily_success hfamily
  have hids := Model.boxIds_nodup hwf
  have hrouteIds := Model.routeIds_nodup hwf
  -- RoutesCovered (inlined from the private helper in ExecutedPortsFacts).
  have hcovered : PipelineImpl.RoutesCovered inp := by
    unfold WellFormed modelWellFormed at hwf
    simp only [Bool.and_eq_true] at hwf
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hroutes⟩, _⟩, _⟩ := hwf
    intro rt hrt
    have h := List.all_eq_true.mp hroutes rt hrt
    simp only [Bool.and_eq_true, List.contains_iff_mem, List.mem_map] at h
    exact h
  intro route hroute
  obtain ⟨source, hsource, target, htarget, hsId, htId, hports⟩ :=
    PipelineImpl.layoutRecursive_group_endpoint_source_invariant hattach hanchors
      (inp.boxes.length + 1) hids hrouteIds hcovered hrecursive route hroute
  exact hports

end Elegant.Layered

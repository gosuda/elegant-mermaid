import Elegant.Layered.FamilyC5
import Elegant.Layered.GroupRouteAttachment
import Elegant.Layered.GroupAnchors
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.RecursiveC6

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Every scene route attaches both endpoints to the boundary of its `from`/`to`
dump boxes, under the measured group-attachment fact.  Identical in shape to
`GroupEndpointInvariant`; the `_measured` suffix keeps the two files' names
distinct while the underlying statement is the same C5 invariant. -/
def GroupEndpointInvariantMeasured (inp : Input) (scene : Scene) : Prop :=
  ∀ out ∈ scene.routes,
    ∃ source ∈ inp.boxes, ∃ target ∈ inp.boxes,
      source.id = out.fromId ∧ target.id = out.toId ∧
      ∃ (start finish : Point) (fromBox toBox : Box),
        out.points.head? = some start ∧ out.points.getLast? = some finish ∧
        scene.layoutDump.box? out.fromId = some fromBox ∧
        scene.layoutDump.box? out.toId = some toBox ∧
        Validator.onBoundary start fromBox.rect ∧
        Validator.onBoundary finish toBox.rect

/-- The remaining bottom-proxy frame fact, over the executed pipeline: for a
`measuredGraph` success with `lines.length = inp.boxes.length`, a well-formed
framed-parents input, a reported component `comp`, and a successful
`componentRun` on `componentCandidate graph comp candidate`, a route port of a
`border = 2` bottom marker lies on the frame of its paired `border = -2` top
marker.  The executed premises rule out hand-built graphs (e.g. an extra
`border = 1` node with cluster path `[decl]` below `v`, which would extend the
frame of `t` past the port point): such a node cannot appear in a measured
component.  The vertical half is the mirror of the top-proxy member routing
bound (`rk top + 1 ≤ rk bottom` from `componentRun_group_top_lt_bottom`,
transferred through `rankAxis_node_in_band` and `top_mono`), with the bottom
proxy itself supplying the frame's bottom edge because `frameRect`'s rectangle
list contains every node whose cluster path contains the declaration, the proxy
included. -/
def GroupBottomBoundaryFacts : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v t : Nat} {px : Int},
    ((componentCandidate graph comp candidate).nodes.getD v default).border = 2 →
    ((componentCandidate graph comp candidate).nodes.getD t default).border = -2 →
    ((componentCandidate graph comp candidate).nodes.getD v default).decl =
      ((componentCandidate graph comp candidate).nodes.getD t default).decl →
    (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w →
    Validator.onBoundary ⟨px, run.ys.getD v 0⟩
      (frameRect P (componentCandidate graph comp candidate) run t)

/-! ### Carried-over private helpers (renamed `_measured`) -/

private theorem selfPreimage_measured {boxes : List ModelBox} (source : Bool)
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
private theorem selfBottomIndex_lt_measured {boxes : List ModelBox} {i j : Nat} (hij : i < j)
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
shared value stays below the box list it is both inputs (`selfPreimage_measured`);
beyond the box list it is `bottomIndex`, which is strictly increasing past a
group box. -/
private theorem selfBottom_ne_measured {boxes : List ModelBox} {a b k : Nat}
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
              · have hbound := selfBottomIndex_lt_measured hcmp ha hma hgrpA
                rw [ea, eb] at hbound
                exact absurd hbound (Nat.lt_irrefl k)
              · have hblt : b < a := by omega
                have hbound := selfBottomIndex_lt_measured hblt hb hmb hgrpB
                rw [eb, ea] at hbound
                exact absurd hbound (Nat.lt_irrefl k)

set_option maxHeartbeats 900000 in
/-- Converse of `componentCandidate_self_model_key`: a component-local self
loop comes from a semantic self edge, so the model route joins one box with
itself. -/
private theorem component_self_route_ids_measured
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
      selfPreimage_measured true raw.tail raw.head alias.tail
        (by rw [hlenPrep]; exact hk) htailE
    have e2 : raw.head = alias.tail :=
      selfPreimage_measured false raw.head raw.tail alias.tail
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
      exact False.elim (selfBottom_ne_measured (boxes := prepared)
        (by rw [hlenPrep]; exact hrt) (by rw [hlenPrep]; exact hhd) hneRaw ea eb hk')

/-- Group-endpoint attachment at the scene level, from the *measured* flat
attachment fact: every `layoutFamily`/`layoutRecursive` consumer applies
`GroupAttach` only at `componentCandidate execution.graph comp candidate`,
whose premises `GroupAttachMeasured` consumes directly (`graph_eq`, the
`lines`-length from `lines_eq`, `WellFormed`, `framedParents`, and component
membership from the selected part).  Everything else is the node-analog
structure of `chosen_part_group_c5_of_box_ids_nodup`. -/
theorem SceneExecution.chosen_part_group_c5_of_box_ids_nodup_measured
    {inp : Input} {o : Options} {res : FamilyResult}
    (hattach : GroupAttachMeasured)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
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
  have hpartsMap : execution.componentsAcc.parts.map
      (fun part : List Nat × Part => part.1) = components execution.graph :=
    (actual_components_parts (by rfl) execution.components_eq).1
  have hcomp : q.1.1 ∈ components execution.graph := by
    have hmap : q.1.1 ∈
        execution.componentsAcc.parts.map (fun part : List Nat × Part => part.1) :=
      List.mem_map_of_mem hmem
    rw [hpartsMap] at hmap
    exact hmap
  have hlines : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have hlen := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using hlen
  have hattach : GroupAttachAt execution.params
      (componentCandidate execution.graph q.1.1 candidate) :=
    hattach execution.graph_eq hlines hwf hfp hcomp candidate
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
  have hP := checkedParams_valid execution.checked
  have hshape : CgShape cg := componentCandidate_shape
    (components_nodup execution.graph q.1.1
      (hpartsMap ▸ List.mem_map_of_mem hmem)) (measuredGraph_shape execution.graph_eq) candidate
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
      hscene, ?_, ?_, ?_, ?_, hports.1, hports.2⟩
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
      hscene, ?_, ?_, ?_, ?_, hports.1, hports.2⟩
    · simp only [List.head?_map, hstart, Option.map_some]
    · simp only [List.getLast?_map, hfinish, Option.map_some]
    · rw [← hsourceId]
      exact hfromLookup
    · rw [← htargetId]
      exact htoLookup

/-- The flat scene invariant, under the *measured* group-attachment fact and a
group-endpoint identification: a plain `layout` covers every route endpoint,
because the ordinary case is `chosen_part_effective_c5_of_box_ids_nodup`, the
self-loop case is `self_routes_c5_of_box_ids_nodup`, and the group case is
`chosen_part_group_c5_of_box_ids_nodup_measured` above.  The identification
premise is the `GroupAnchors` shape; the alias form `GroupAnchorsAlias` (proved
as `groupAnchorsAlias_holds` in `GroupAnchors.lean`) supplies the plain-endpoint
instances of it. -/
theorem SceneExecution.group_endpoint_source_invariant_measured
    {inp : Input} {o : Options} {res : FamilyResult}
    (hattach : GroupAttachMeasured) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hanchors : GroupAnchors)
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup) :
    GroupEndpointInvariantMeasured inp res.scene := by
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
    execution.packedAcc execution.measured key hkey
  rw [← execution.scene_eq] at hscene
  have houtRecord := Option.some.inj (houtIndex.symm.trans hscene)
  have hfromId : out.fromId = modelRoute.fromId := congrArg Route.fromId houtRecord
  have htoId : out.toId = modelRoute.toId := congrArg Route.toId houtRecord
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_source hkey
  by_cases hself : edge.tail = edge.head
  · obtain ⟨index, route, _raw, source, hroute, hdeclIndex, hsourceBox, hsourceId,
      hrouteSelf⟩ :=
      component_self_route_ids_measured execution.graph_eq hrun hedge hself
    have hindex : index = key := hdeclIndex.symm.trans hdecl
    rw [hindex] at hroute
    have hrouteEq : route = modelRoute := Option.some.inj (hroute.symm.trans hmodel)
    subst hrouteEq
    refine ⟨source, List.mem_of_getElem? hsourceBox, source,
      List.mem_of_getElem? hsourceBox, hsourceId.trans hfromId.symm,
      hsourceId.trans (hrouteSelf.trans htoId.symm), ?_⟩
    exact execution.self_routes_c5_of_box_ids_nodup hids hout
      (hfromId.trans (hrouteSelf.trans htoId.symm))
  · obtain ⟨_idxF, _idxT, sF, sT, rDecl, hfromKey, hsourceM, htoKey, htargetM,
      hrouteD, hsourceIdD, htargetIdD⟩ :=
      hanchors execution packed hpacked hselected hrun hloops hpart hedge hself
    obtain ⟨out', start, finish, fromBox, toBox, hemitted, hstart, hfinish,
      hfromLookup, htoLookup, hfromBoundary, htoBoundary⟩ :=
      execution.chosen_part_group_c5_of_box_ids_nodup_measured hattach hwf hfp hids packed
        hpacked hselected hrun hloops hpart hedge hself
        hfromKey hsourceM hrouteD hsourceIdD htoKey htargetM hrouteD htargetIdD
    rw [hdecl] at hemitted hrouteD
    have hrouteEq : rDecl = modelRoute :=
      Option.some.inj (hrouteD.symm.trans hmodel)
    subst hrouteEq
    have hsame' : out' = out := Option.some.inj (hemitted.symm.trans houtIndex)
    subst hsame'
    exact ⟨sF, List.mem_of_getElem? hsourceM, sT, List.mem_of_getElem? htargetM,
      hsourceIdD.trans hfromId.symm, htargetIdD.trans htoId.symm,
      start, finish, fromBox, toBox, hstart, hfinish, hfromLookup, htoLookup,
      hfromBoundary, htoBoundary⟩

/-- Open seam, the flat endpoint invariant: every route of a successful flat
`layout` of a well-formed input with framed parents attaches both endpoints
to the boundary of its endpoint dump boxes.  It is the flat form of clause C5.
`SceneExecution.group_endpoint_source_invariant_measured` proves it from
`GroupAttachMeasured` and `GroupAnchors`, but `GroupAnchors` is refuted
(`GroupAnchors.lean`): the proof of this seam has to consume the true
identification `GroupAnchorsAlias` (`groupAnchorsAlias_holds`) and the
bottom-proxy boundary fact `GroupBottomBoundaryFacts` instead. -/
def FlatGroupEndpoints : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult},
    WellFormed (inputModel inp o) → framedParents inp = true →
    SceneExecution inp o res → GroupEndpointInvariantMeasured inp res.scene

/-- Recursive group-endpoint invariant from the flat endpoint invariant: the
flat base case is `FlatGroupEndpoints`; the embedding case follows
`expandChild`'s route assembly, shifting child endpoints and keeping parent
endpoints, both of which keep the invariant.  Well-formedness and framed
parents are carried through the recursion by `SubInputWellFormed` (the seam
the flat-clause lifts consume) so the flat seam applies at every `layout`
leaf. -/
theorem layoutRecursive_group_endpoint_source_invariant_measured
    (hflatEndpoints : FlatGroupEndpoints)
    (hsub : SubInputWellFormed)
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hrecursive : layoutRecursive fuel inp o = .ok res) :
    GroupEndpointInvariantMeasured inp res.scene := by
  induction fuel generalizing inp o res with
  | zero =>
      obtain ⟨execution⟩ := layout_sceneExecution hrecursive
      exact hflatEndpoints hwf hfp execution
  | succ fuel ih =>
      have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      have hcovered : RoutesCovered inp := inputRoutesCovered hwf
      rcases layoutRecursive_succ hrecursive with ⟨_, hflat⟩ |
        ⟨group, hg, _, _, _, _, _, _, _, _, _, _⟩
      · obtain ⟨execution⟩ := layout_sceneExecution hflat
        exact hflatEndpoints hwf hfp execution
      · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, dx, dy,
          hP, hm, hchild, hwrap, hparentAt, _hexpand, _, _, _, _,
          hchildLookup, hparentLookup, hroutes, _⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg hrecursive
        obtain ⟨hwfChild, hfpChild, hwfParent, hfpParent⟩ :=
          hsub fuel inp o group P metric titleLines child parent hwf hfp hP hm hwrap
            hchild hparentAt
        have hc := ih hwfChild hfpChild hchild
        have hp := ih hwfParent hfpParent hparentAt
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
          obtain ⟨source, hsource, hsId, _⟩ := lift _ _ _ hselectedSource
          obtain ⟨target, htarget, htId, _⟩ := lift _ _ _ hselectedTarget
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

/-- Clause C5 for a successful `layoutFamily` from the flat endpoint invariant:
the recursive invariant gives, for every scene route, endpoint boxes whose
boundaries carry the first and last route points. -/
theorem layoutFamily_c5_measured (hflatEndpoints : PipelineImpl.FlatGroupEndpoints)
    (hsub : PipelineImpl.SubInputWellFormed)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hfamily : layoutFamily inp o = .ok res) :
    Validator.C5 res.scene.layoutDump := by
  obtain ⟨hwf, hrecursive⟩ := layoutFamily_success hfamily
  have hfp := layoutFamily_framed_parents hfamily
  intro route hroute
  obtain ⟨source, hsource, target, htarget, hsId, htId, hports⟩ :=
    PipelineImpl.layoutRecursive_group_endpoint_source_invariant_measured hflatEndpoints
      hsub (inp.boxes.length + 1) hwf hfp hrecursive route hroute
  exact hports

end Elegant.Layered

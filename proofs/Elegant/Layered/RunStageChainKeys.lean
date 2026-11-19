import Elegant.Layered.FlatC6ScopeBridgeProof
import Elegant.Layered.FlatC6ScopeResidualsProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SizingFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.CgShape
import Elegant.Layered.CoordGraph
import Elegant.Layered.ComponentCoverage
set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl


/-- Members of a reported component are valid graph indices. -/
theorem comp_mem_lt {g : Graph} {comp : List Nat}
    (hcomp : comp ∈ components g) {v : Nat} (hv : v ∈ comp) :
    v < g.nodes.length := by
  unfold components at hcomp
  dsimp only at hcomp
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hcomp
  have hmem : v ∈ (List.range g.nodes.length).filter
      (fun v => (labelsFix (g.edges ++ Compound.constraints g)
        (g.nodes.length + 1) (Array.range g.nodes.length))[v]! == r) := hv
  have hrange : v ∈ List.range g.nodes.length :=
    (List.mem_filter.mp hmem).1
  exact List.mem_range.mp hrange

/-- Every edge appended by `chainEdges` carries its own index. -/
theorem chainEdges_original {e : Edge} {idx n0 s : Nat} {pe : ProperEdge}
    (hmem : pe ∈ NormalizeImpl.chainEdges e idx n0 s) : pe.original = idx := by
  unfold NormalizeImpl.chainEdges at hmem
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
  rfl

/-- A self-loop `normalizeEdge` keeps the edge list. -/
theorem normalizeEdge_self_edges {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (hself : e.tail = e.head)
    (h : NormalizeImpl.normalizeEdge slot p e idx = .ok p') :
    p'.edges = p.edges := by
  unfold NormalizeImpl.normalizeEdge at h
  simp only [hself, ↓reduceIte, Except.ok.injEq] at h
  subst h
  rfl

/-- A non-self `normalizeEdge` appends only its own index. -/
theorem normalizeEdge_append_original {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (hne : e.tail ≠ e.head)
    (h : NormalizeImpl.normalizeEdge slot p e idx = .ok p') {pe : ProperEdge}
    (hmem : pe ∈ p'.edges) (hnot : pe ∉ p.edges) : pe.original = idx := by
  unfold NormalizeImpl.normalizeEdge at h
  simp only [hne, ↓reduceIte] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · have heq := Except.ok.inj h
      subst p'
      have hmem2 : pe ∈ p.edges ++ NormalizeImpl.chainEdges e idx p.nodes.length _ :=
        hmem
      rcases List.mem_append.mp hmem2 with hm | hm
      · exact absurd hm hnot
      · exact chainEdges_original hm

/-- No output edge carries a self-loop index. -/
theorem normalizeLoop_preserves_no_original {es : List Edge} {slot : Int} {i : Nat}
    {l : List (Edge × Nat)} {p p' : Proper}
    (hmem : ∀ x ∈ l, es[x.2]? = some x.1)
    (hself : ∃ e, es[i]? = some e ∧ e.tail = e.head)
    (hno : ∀ pe ∈ p.edges, pe.original ≠ i)
    (h : NormalizeImpl.normalizeLoop slot l p = .ok p') :
    ∀ pe ∈ p'.edges, pe.original ≠ i := by
  induction l generalizing p with
  | nil =>
    simp only [NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    exact hno
  | cons q rest ih =>
    obtain ⟨e, idx⟩ := q
    simp only [NormalizeImpl.normalizeLoop] at h
    split at h
    · simp at h
    · next p1 h1 =>
      have hmemHead : es[idx]? = some e := hmem (e, idx) (by simp)
      have hmemRest : ∀ x ∈ rest, es[x.2]? = some x.1 := fun x hx =>
        hmem x (List.mem_cons_of_mem _ hx)
      have hno1 : ∀ pe ∈ p1.edges, pe.original ≠ i := by
        intro pe hpe hcon
        by_cases hidx : idx = i
        · subst hidx
          have heq : e = hself.choose :=
            Option.some.inj (hmemHead.symm.trans hself.choose_spec.1)
          have hselfE : e.tail = e.head := by
            rw [heq]
            exact hself.choose_spec.2
          have hedge : p1.edges = p.edges :=
            normalizeEdge_self_edges hselfE h1
          rw [hedge] at hpe
          exact hno pe hpe hcon
        · by_cases hselfE : e.tail = e.head
          · have hedge : p1.edges = p.edges :=
              normalizeEdge_self_edges hselfE h1
            rw [hedge] at hpe
            exact hno pe hpe hcon
          · have horig := normalizeEdge_append_original hselfE h1 hpe
            by_cases hmemOld : pe ∈ p.edges
            · exact hno pe hmemOld hcon
            · have heq := horig hmemOld
              omega
      exact ih hmemRest hno1 h

/-- The zip-index list carries its own identity. -/
theorem zipIdx_mem_identity {es : List Edge} {x : Edge × Nat}
    (hx : x ∈ es.zipIdx) : es[x.2]? = some x.1 :=
  List.mem_zipIdx_iff_getElem?.mp hx

/-- A self-loop index contributes no normalized edge. -/
theorem normalized_no_original_of_self {cg : Graph} {ranks : List Int} {p0 : Proper}
    (hn : normalize cg ranks = .ok p0)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hself : edge.tail = edge.head) :
    ∀ pe ∈ p0.edges, pe.original ≠ i := by
  have hmem : ∀ x ∈ cg.edges.zipIdx, cg.edges[x.2]? = some x.1 :=
    fun x hx => zipIdx_mem_identity hx
  have hselfEx : ∃ e, cg.edges[i]? = some e ∧ e.tail = e.head :=
    ⟨edge, hedge, hself⟩
  have hno : ∀ (pe : ProperEdge), pe ∈
      (Proper.mk (cg.nodes.map (fun nd => ProperNode.mk nd false none false))
        [] ranks []).edges →
      pe.original ≠ i := by
    intro pe hpe
    simp at hpe
  unfold normalize at hn
  cases hslot : NormalizeImpl.slotOf cg with
  | none =>
    simp [hslot] at hn
  | some slot =>
    simp [hslot] at hn
    by_cases hcond : (cg.wellformed = true ∧ ranks.length = cg.nodes.length ∧ 0 ≤ slot)
    · simp [hcond] at hn
      have hn' : NormalizeImpl.normalizeLoop slot cg.edges.zipIdx
          (Proper.mk (cg.nodes.map (fun nd => ProperNode.mk nd false none false))
            [] ranks []) = .ok p0 := hn
      exact normalizeLoop_preserves_no_original hmem hselfEx hno hn'
    · simp [hcond] at hn

/-- Residual about `Compound.aliasEdge`: an aliased endpoint's graph node
carries a model endpoint declaration. Pinned by `measuredGraph` (`graph_eq`)
and the `edgeOf` equation; true on executed layouts. -/
def AliasDeclTransport (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) {index : Nat} {route : ModelRoute} {raw : Edge},
    inp.routes[index]? = some route →
    edgeOf inp route index = .ok raw →
    ∀ {a : Nat} {node : Node},
      (a = (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) raw).tail ∨
       a = (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box) raw).head) →
      execution.graph.nodes[a]? = some node →
      node.decl = raw.tail ∨ node.decl = raw.head

/-- Endpoint projections of the pristine form of an edge. -/
private theorem edge_original_tail' (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  unfold Edge.original
  split <;> simp_all

/-- Endpoint projections of the pristine form of an edge. -/
private theorem edge_original_head' (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  unfold Edge.original
  split <;> simp_all

/-- `nodeMinW` is positive in both profiles. -/
theorem nodeMinW_pos {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 0 < P.nodeMinW := by
  obtain ⟨B, hb, rfl⟩ := checkedParams_some h
  have hP : (B.forKind profile kind).nodeMinW = B.nodeMinW := rfl
  have hB : B.nodeMinW = LayoutConst.node_min_w.get profile := by
    unfold baseParams at hb
    have heq := Option.some.inj hb
    have hcon := congrArg Params.nodeMinW heq
    simpa using hcon.symm
  rw [hP, hB]
  cases profile <;> decide

/-- `nodeMinH` is positive in both profiles. -/
theorem nodeMinH_pos {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 0 < P.nodeMinH := by
  obtain ⟨B, hb, rfl⟩ := checkedParams_some h
  have hP : (B.forKind profile kind).nodeMinH = B.nodeMinH := rfl
  have hB : B.nodeMinH = LayoutConst.node_min_h.get profile := by
    unfold baseParams at hb
    have heq := Option.some.inj hb
    have hcon := congrArg Params.nodeMinH heq
    simpa using hcon.symm
  rw [hP, hB]
  cases profile <;> decide

/-- Residual about `Pipeline.frameRect`: a placed part's plain/group rects
are positive. Pinned by the `placeComponent` rect equations; true on
executed layouts (`nodeMinW/H`, `clusterBorderW` positive in both profiles). -/
def FrameRectPositive (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res)
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (_hrun : componentRun execution.params cg labels orderOptions = .ok run)
    {v : Nat} {node : Node} (_hn : cg.nodes[v]? = some node),
    (node.border = 0 → 0 < (frameRect execution.params cg run v).w ∧
      0 < (frameRect execution.params cg run v).h) ∧
    (node.border = -2 → 0 < (frameRect execution.params cg run v).w)

/-- Component lookup at the position of a member (copy of the
`FlatGroupEndpointsProof` helper; `List.idxOf` inverts membership). -/
private theorem comp_idxOf_lookup {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))

/-- Rect lookup in a placed component (copy of the `ForeignFrameClearance`
pattern; uses only `Pipeline`). -/
private theorem placeComponent_rects_get_aux (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponent P cg run 0 labels loops).rects[i]? =
      some (shiftRect (0 - (placeBounds P cg run labels loops).minX)
        (0 - (placeBounds P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponent placeBounds
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- `PartPositiveContent` from `FrameRectPositive`: a routed part has a plain
candidate node whose shifted frame rect is positive in both axes. The
`hplain` premise (every routed part has a `border = 0` candidate node) is the
only additional assumption; the route y-span alternative is not needed since
the plain rect already supplies both axes. -/
theorem partPositiveContent {inp : Input} {o : Options} {res : FamilyResult}
    (hframe : FrameRectPositive inp o res)
    (hplain : ∀ (execution : SceneExecution inp o res) (comp : List Nat)
      (candidate : Nat) (run : Run),
      comp ∈ components execution.graph →
      componentRun execution.params (componentCandidate execution.graph comp candidate)
        execution.measured (candidateOrder candidate) = .ok run →
      ∀ {part : List Nat × Part}, part ∈ execution.componentsAcc.parts →
      part.1 = comp → part.2.routes ≠ [] →
      ∃ (v : Nat) (node : Node),
        (componentCandidate execution.graph comp candidate).nodes[v]? = some node ∧
        node.border = 0) :
    PartPositiveContent inp o res := by
  intro execution part hpart hroutes
  obtain ⟨index, run, loops, area, hcomp, hrun, heq⟩ :=
    execution_part_run execution hpart
  obtain ⟨v, node, hnode, hborder⟩ :=
    hplain execution part.1 index run hcomp hrun hpart rfl hroutes
  have hpos := (hframe execution hrun hnode).1 hborder
  obtain ⟨hposW, hposH⟩ := hpos
  have hrectsEq : part.2.rects =
      (placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0
        execution.measured loops).rects := by rw [heq]
  have hi : v < (componentCandidate execution.graph part.1 index).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hget := placeComponent_rects_get_aux execution.params
    (componentCandidate execution.graph part.1 index) run execution.measured loops hi
  have hmem : shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run v) ∈
      part.2.rects := by
    rw [hrectsEq]
    exact List.mem_of_getElem? hget
  have hw : 0 < (shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run v)).w := hposW
  have hh : 0 < (shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run v)).h := hposH
  exact ⟨⟨_, hmem, hw⟩, Or.inl ⟨_, hmem, hh⟩⟩
/-- A self-loop edge contributes no proper chain segment. `normalize` emits no
edge with a self-loop index (`normalized_no_original_of_self`), and the later
run stages preserve the edge set outright (`componentRun_normalized_source`:
`run.proper.edges = normalized.edges`, itself via `addLabelNodes_metadata`,
`normalize_clean`, `dropSynthetic_addClusterBorders_edges`, `proxyWidths_rel`,
and `coordinateGraph_chains`). No new stage lemma was needed; the missing link
was only this composition. -/
theorem selfLoop_edgesOf_empty {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {i : Nat} {edge : Edge}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hedge : cg.edges[i]? = some edge) (hself : edge.tail = edge.head) :
    (RouteImpl.edgesOf run.proper i) = [] := by
  obtain ⟨ranks, normalized, hn, he, _⟩ := componentRun_normalized_source hrun
  have hno : ∀ pe ∈ normalized.edges, pe.original ≠ i :=
    normalized_no_original_of_self hn hedge hself
  have hno' : ∀ pe ∈ run.proper.edges, pe.original ≠ i := by
    rw [he]
    exact hno
  exact List.eq_nil_iff_forall_not_mem.mpr fun j hj =>
    absurd (mem_edgesOf.mp hj).2 (hno' _ (edgeAt_mem (mem_edgesOf.mp hj).1))

/-- `ProperChainEndpointKeys` from `AliasDeclTransport`: the first/last proper
segment endpoints of a run route resolve through `chain_endpoints` to the
candidate edge ends, through `model_endpoint_source` to the model route/raw,
and through `idxOf`/`getElem_idxOf` plus `AliasDeclTransport` to global keys
carrying `raw.tail/head` decls. The self-loop case is by
`selfLoop_edgesOf_empty` (no proper segment carries a self-loop index). -/
theorem properChainEndpointKeys {inp : Input} {o : Options} {res : FamilyResult}
    (halias : AliasDeclTransport inp o res) :
    ProperChainEndpointKeys inp o res := by
  intro execution comp candidate run hcomp hrun i edge native hnative horig hedge
    i₀ i₁ hfirst hlast
  have hP : execution.params.Valid := checkedParams_valid execution.checked
  have hdecls : ((componentCandidate execution.graph comp candidate).edges.map
      (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
  have hshapeG : CgShape execution.graph :=
    measuredGraph_shape execution.graph_eq
  have hnd : comp.Nodup := components_nodup execution.graph comp hcomp
  have hS : CgShape (componentCandidate execution.graph comp candidate) :=
    componentCandidate_shape hnd hshapeG candidate
  by_cases hne : edge.tail = edge.head
  · have hempty' := selfLoop_edgesOf_empty hrun hedge hne
    rw [horig] at hfirst
    rw [hempty'] at hfirst
    simp at hfirst
  · have hne' : edge.tail ≠ edge.head := hne
    obtain ⟨first, last, hfirst', hlast', htail, hhead⟩ :=
      componentRun_chain_endpoints hP hdecls hS hrun hedge hne'
    rw [horig] at hfirst hlast
    have hfi : i₀ = first := Option.some.inj (hfirst.symm.trans hfirst')
    have hla : i₁ = last := Option.some.inj (hlast.symm.trans hlast')
    subst hfi
    subst hla
    obtain ⟨index, route, raw, source, target, hroute, hraw, hdecl',
      hsource, hsourceId, htarget, htargetId, _⟩ :=
      componentCandidate_model_endpoint_source execution.graph_eq
        (List.mem_of_getElem? hedge)
    obtain ⟨gEdge, hgMem, hgTail0, hsemG⟩ :=
      componentCandidate_semantic_source (List.mem_of_getElem? hedge)
    obtain ⟨index₂, route₂, raw₂, hroute₂, hraw₂, halias₂⟩ :=
      measuredGraph_edge_source execution.graph_eq hgMem
    obtain ⟨hdecl₂, hrev₂, _, _, _, _, _, _⟩ :=
      edgeOf_semantic_endpoints hraw₂
    have hgeRev : gEdge.reversed = false := by rw [halias₂]; exact hrev₂
    have hdecl₂' : edge.decl = index₂ := by
      have h1 : edge.decl = gEdge.decl := by
        have h := congrArg Edge.decl hsemG
        simpa only [Edge.original_decl] using h
      have h2 : gEdge.decl = raw₂.decl := by
        rw [halias₂]
        exact Compound.aliasEdge_decl _ _
      rw [h1, h2]
      exact hdecl₂
    have hidx₂ : index₂ = index := hdecl₂'.symm.trans hdecl'
    rw [hidx₂] at hroute₂
    have hrouteEq : route₂ = route := Option.some.inj (hroute₂.symm.trans hroute)
    rw [hidx₂, hrouteEq] at hraw₂
    have hrawEq : raw₂ = raw := Except.ok.inj (hraw₂.symm.trans hraw)
    have hlinesLen : execution.lines.length = inp.boxes.length := by
      have hle := execution.lines_eq
      unfold boxLines at hle
      have hlen := (mapM_getElem? _ _ _ hle).1
      simpa [List.length_zipIdx] using hlen
    have hbd : ∀ e ∈ execution.graph.edges ++
        Compound.constraints execution.graph,
        e.tail < execution.graph.nodes.length ∧
        e.head < execution.graph.nodes.length := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact measuredGraph_edges_bounded execution.graph_eq hlinesLen e he
      · exact constraints_bounded _ e he
    obtain ⟨comp', hcomp'In, hgTailC, hgHeadC⟩ :=
      components_edge_endpoints hbd (List.mem_append.mpr (Or.inl hgMem))
    have hcompEq : comp' = comp :=
      components_shared_member_eq hcomp'In hcomp hgTailC hgTail0
    have hgHead : gEdge.head ∈ comp := by rw [← hcompEq]; exact hgHeadC
    have hgeAlias : gEdge = Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node }
        else box) raw := by rw [halias₂, hrawEq]
    have hmemT : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node }
        else box) raw).tail ∈ comp := by
      have h := hgTail0
      rw [hgeAlias] at h
      exact h
    have hmemH : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node }
        else box) raw).head ∈ comp := by
      have h := hgHead
      rw [hgeAlias] at h
      exact h
    have hsemTail : edge.original.tail = comp.idxOf
        (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node }
          else box) raw).tail := by
      have h := congrArg Edge.tail hsemG
      have hgeOrig : gEdge.original = gEdge := by
        cases gEdge with
        | mk tail head minLen decl reversed => cases hgeRev; rfl
      rw [hgeOrig, hgeAlias] at h
      exact h
    have hsemHead : edge.original.head = comp.idxOf
        (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node }
          else box) raw).head := by
      have h := congrArg Edge.head hsemG
      have hgeOrig : gEdge.original = gEdge := by
        cases gEdge with
        | mk tail head minLen decl reversed => cases hgeRev; rfl
      rw [hgeOrig, hgeAlias] at h
      exact h
    rw [edge_original_tail'] at hsemTail
    rw [edge_original_head'] at hsemHead
    cases hr : edge.reversed with
    | true =>
      simp only [hr, ↓reduceIte] at hsemTail hsemHead
      have hT : comp[edge.tail]? =
          some (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).head := by
        rw [hsemHead]
        exact comp_idxOf_lookup hmemH
      have hH : comp[edge.head]? =
          some (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).tail := by
        rw [hsemTail]
        exact comp_idxOf_lookup hmemT
      have hcompT : comp[(RouteImpl.edgeAt run.proper i₀).tail]? =
          some (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).head := by
        rw [htail]
        exact hT
      have hcompH : comp[(RouteImpl.edgeAt run.proper i₁).head]? =
          some (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).tail := by
        rw [hhead]
        exact hH
      have hltT : (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node }
          else box) raw).head < execution.graph.nodes.length :=
        comp_mem_lt hcomp hmemH
      have hltH : (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node }
          else box) raw).tail < execution.graph.nodes.length :=
        comp_mem_lt hcomp hmemT
      obtain ⟨nT, hnT⟩ : ∃ nT, execution.graph.nodes[
          (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).head]? = some nT :=
        ⟨_, List.getElem?_eq_getElem hltT⟩
      obtain ⟨nH, hnH⟩ : ∃ nH, execution.graph.nodes[
          (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).tail]? = some nH :=
        ⟨_, List.getElem?_eq_getElem hltH⟩
      have hdeclT := halias execution hroute hraw (Or.inr rfl) hnT
      have hdeclH := halias execution hroute hraw (Or.inl rfl) hnH
      exact ⟨_, _, _, _, _, nT, nH, hcompT, hcompH, hnT, hnH,
        hdeclT, hdeclH, hroute, hraw, hdecl'⟩
    | false =>
      simp [hr] at hsemTail hsemHead
      have hT : comp[edge.tail]? =
          some (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).tail := by
        rw [hsemTail]
        exact comp_idxOf_lookup hmemT
      have hH : comp[edge.head]? =
          some (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).head := by
        rw [hsemHead]
        exact comp_idxOf_lookup hmemH
      have hcompT : comp[(RouteImpl.edgeAt run.proper i₀).tail]? =
          some (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).tail := by
        rw [htail]
        exact hT
      have hcompH : comp[(RouteImpl.edgeAt run.proper i₁).head]? =
          some (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).head := by
        rw [hhead]
        exact hH
      have hltT : (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node }
          else box) raw).tail < execution.graph.nodes.length :=
        comp_mem_lt hcomp hmemT
      have hltH : (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node }
          else box) raw).head < execution.graph.nodes.length :=
        comp_mem_lt hcomp hmemH
      obtain ⟨nT, hnT⟩ : ∃ nT, execution.graph.nodes[
          (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).tail]? = some nT :=
        ⟨_, List.getElem?_eq_getElem hltT⟩
      obtain ⟨nH, hnH⟩ : ∃ nH, execution.graph.nodes[
          (Compound.aliasEdge (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
              { box with role := .node }
            else box) raw).head]? = some nH :=
        ⟨_, List.getElem?_eq_getElem hltH⟩
      have hdeclT := halias execution hroute hraw (Or.inl rfl) hnT
      have hdeclH := halias execution hroute hraw (Or.inr rfl) hnH
      exact ⟨_, _, _, _, _, nT, nH, hcompT, hcompH, hnT, hnH,
        hdeclT, hdeclH, hroute, hraw, hdecl'⟩

/-- Closed corollary: run route endpoints land inside the scene route scope. -/
theorem runRouteEndpointIdsScoped' {inp : Input} {o : Options} {res : FamilyResult}
    (hpreserved : ProperDeclPreserved inp o res)
    (hkeys : ProperChainEndpointKeys inp o res) :
    RunRouteEndpointIdsScoped inp o res :=
  runRouteEndpointIdsScoped_of_keys hpreserved hkeys

/-- Closed corollary: the shelf of a part with an edge is positive in both axes. -/
theorem routePartShelfPositive' {inp : Input} {o : Options} {res : FamilyResult}
    (hcontent : PartPositiveContent inp o res) :
    RoutePartShelfPositive inp o res :=
  routePartShelfPositive_of_content hcontent
end PipelineImpl
end Layered
end Elegant

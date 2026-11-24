import Elegant.Layered.RegionC5ExactLoopTransport
import Elegant.Layered.RegionPipeline
import Lean

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

def R5_OwningFallbackR {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (out : Route) : Prop :=
  ∃ (key : Nat) (part : List Nat × Part),
    res.scene.routes[key]? = some out ∧ part ∈ execution.componentsAcc.parts ∧
    key ∈ (componentGraph execution.graph part.1).edges.map (·.decl) ∧
    newComponentRegions (selectedC5TerminalSpec idSets execution.params o execution.lines)
      execution.params inp (componentGraph execution.graph part.1) = .ok none

/-- The packed owner and chosen portfolio run of the very edge that emits `out`. -/
def R5_SelectedLoopR {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (out : Route) (isExact : Bool) : Prop :=
  ∃ (packed : Pack.State) (c : Nat) (q : (List Nat × Part) × Rect)
      (candidate : Nat) (run : Run) (loops : List (Nat × LoopPlacement))
      (area : Int) (used : Option RegionSpec) (cg : Graph) (i : Nat) (edge : Edge),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) =
        .ok packed ∧
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q ∧
    (∃ chosen, Portfolio.portfolio o.thoroughness
      (componentTrialR execution.params exactIds
        (selectedC5TerminalSpec idSets execution.params o execution.lines) inp o
        execution.graph q.1.1 execution.measured) = .ok chosen ∧ chosen.value = (cg, run)) ∧
    (∃ rs, newComponentRegions (selectedC5TerminalSpec idSets execution.params o execution.lines)
      execution.params inp (componentGraph execution.graph q.1.1) = .ok rs ∧
      used = if rs.isSome then selectedC5TerminalSpec idSets execution.params o execution.lines
        else none) ∧
    componentRunR execution.params (exactDecls exactIds inp) used inp
      (componentCandidateR used execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok (cg, run) ∧
    componentLoops execution.params cg run execution.measured = .ok loops ∧
    q.1.2 = { placeComponentExact execution.params cg run 0 execution.measured loops with
      area := area } ∧
    cg.edges[i]? = some edge ∧ edge.tail = edge.head ∧ run.exact.contains edge.tail = isExact ∧
    res.scene.routes[edge.decl]? = some out

private theorem c5EmittedSelfLoop_edge_self {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {used : Option RegionSpec} {comp : List Nat} {index : Nat} {cg : Graph} {run : Run}
    (hc : comp ∈ components execution.graph)
    (hrun : componentRunR execution.params (exactDecls exactIds inp) used inp
      (componentCandidateR used execution.graph comp index) execution.measured
      (candidateOrder index) = .ok (cg, run))
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    {out : Route} (hout : res.scene.routes[edge.decl]? = some out)
    (hself : out.fromId = out.toId) : edge.tail = edge.head := by
  obtain ⟨native, raw, hnative, hraw, ht, hh, _, _⟩ :=
    c5NativeRouteOrigin execution hc hrun hedge
  obtain ⟨hk, hmodel⟩ := List.getElem?_eq_some_iff.mp hnative
  have hemit := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured edge.decl hk
  rw [← execution.scene_eq, hmodel] at hemit
  have heq := Option.some.inj (hout.symm.trans hemit)
  have hnativeSelf : native.fromId = native.toId :=
    (congrArg Route.fromId heq).symm.trans (hself.trans (congrArg Route.toId heq))
  have hrawSelf : raw.tail = raw.head := by
    unfold edgeOf at hraw
    rw [hnativeSelf] at hraw
    cases hf : inp.boxes.findIdx? (fun b => b.id == native.toId) with
    | none => simp [hf] at hraw
    | some k =>
      simp only [hf, Except.ok.injEq] at hraw
      rw [← hraw]
  have halias : (aliasEdgeOf inp raw).tail = (aliasEdgeOf inp raw).head := by
    change Compound.endpoint (preparedBoxes inp) true raw.tail raw.head =
      Compound.endpoint (preparedBoxes inp) false raw.head raw.tail
    rw [hrawSelf]
    unfold Compound.endpoint
    cases (preparedBoxes inp)[raw.head]? <;> simp
  have hlookup : comp[edge.original.tail]? = comp[edge.original.head]? :=
    ht.trans ((congrArg some halias).trans hh.symm)
  have horiginal : edge.original.tail = edge.original.head :=
    ((components_nodup execution.graph comp hc).getElem?_inj
      (List.getElem?_eq_some_iff.mp ht).1).mp hlookup
  cases hr : edge.reversed with
  | false => simpa [Edge.original, hr] using horiginal
  | true =>
    have h : edge.head = edge.tail := by simpa [Edge.original, hr] using horiginal
    exact h.symm

/-- Every emitted self-loop has a selected run witness, before testing `run.exact`. -/
theorem regionC5EmittedSelfLoop_selected {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {out : Route} (hout : out ∈ res.scene.routes) (hself : out.fromId = out.toId) :
    ∃ isExact : Bool, R5_SelectedLoopR execution out isExact := by
  obtain ⟨key, hout⟩ := List.mem_iff_getElem?.mp hout
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length execution.params inp o execution.lines
      execution.packedAcc execution.measured
  have hkey : key < inp.routes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hout).1
  obtain ⟨packed, c, q, sourceCandidate, _, _, _, sourceSpec, _, _, _, hpack,
    hselected, hsourceRun, _, _, hsourceEdge, hsourceDecl⟩ := rgeRouteSourceR execution hkey
  have howned : key ∈ (componentGraph execution.graph q.1.1).edges.map (·.decl) := by
    rw [← c5TransportCandidateDecls sourceSpec execution.graph q.1.1 sourceCandidate,
      ← componentRunR_edges_declsR hsourceRun, ← hsourceDecl]
    exact List.mem_map_of_mem (List.mem_of_getElem? hsourceEdge)
  obtain ⟨hparts, hall⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  have hpart : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  have hc : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hpart
  have hgeom : ActualPartGeometryR execution.params exactIds
      (selectedC5TerminalSpec idSets execution.params o execution.lines) inp o execution.graph
      execution.measured q.1 := hall q.1 hpart
  obtain ⟨candidate, chosen, cg, run, loops, area, used, _, hchosen, hvalue, hresolved, hrun,
    hloops, hplace⟩ := hgeom
  rw [← c5TransportCandidateDecls used execution.graph q.1.1 candidate,
    ← componentRunR_edges_declsR hrun] at howned
  obtain ⟨edge, hedgeMem, hdecl⟩ := List.mem_map.mp howned
  obtain ⟨i, hedge⟩ := List.mem_iff_getElem?.mp hedgeMem
  have houtEdge : res.scene.routes[edge.decl]? = some out := by rwa [hdecl]
  have hedgeSelf := c5EmittedSelfLoop_edge_self execution hc hrun hedge houtEdge hself
  exact ⟨run.exact.contains edge.tail, packed, c, q, candidate, run, loops, area, used, cg, i,
    edge, hpack, hselected, ⟨chosen, hchosen, hvalue⟩, hresolved, hrun, hloops, hplace,
    hedge, hedgeSelf, rfl, houtEdge⟩

theorem regionC5SelectedExactLoop_boundary {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {out : Route} (h : R5_SelectedLoopR execution out true) : EmittedC5Boundary res.scene out := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpack, hselected, _, _, hrun, hloops, hplace,
    hedge, hself, hexact, hout⟩ := h
  exact regionC5SelectedExactLoopEndpoints execution hwf hpack hselected hrun hloops hplace
    hedge hself hexact hout

def R_ActiveBoundarySelectedResidual (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ¬ R_AllComponentsFallbackR execution →
    ∀ out ∈ res.scene.routes,
      ((out.fromId ≠ out.toId ∧ R5_OwningFallbackR execution out) ∨
        (out.fromId = out.toId ∧ R5_SelectedLoopR execution out false ∧
          ¬ R5_SelectedLoopR execution out true)) →
      EmittedC5Boundary res.scene out

theorem r_activeBoundaryR_iff_selectedResidual (exactIds : List String)
    (idSets : List (String × List String)) :
    R_ActiveBoundaryR exactIds idSets ↔ R_ActiveBoundarySelectedResidual exactIds idSets := by
  classical
  constructor
  · intro h inp o res execution hwf hfp hactive out hout _
    exact h execution hwf hfp hactive out hout
  · intro h inp o res execution hwf hfp hactive out hout
    change EmittedC5Boundary res.scene out
    by_cases hself : out.fromId = out.toId
    · by_cases hexact : R5_SelectedLoopR execution out true
      · exact regionC5SelectedExactLoop_boundary execution hwf hexact
      · obtain ⟨isExact, hselected⟩ := regionC5EmittedSelfLoop_selected execution hout hself
        have hnonexact : R5_SelectedLoopR execution out false := by
          cases isExact with
          | false => exact hselected
          | true => exact (hexact hselected).elim
        exact h execution hwf hfp hactive out hout (Or.inr ⟨hself, hnonexact, hexact⟩)
    · rcases regionC5OrdinaryRouteBoundary_or_owningFallback execution hwf hfp hout hself with
        hboundary | howner
      · exact hboundary
      · exact h execution hwf hfp hactive out hout (Or.inl ⟨hself, howner⟩)

theorem r_activeBoundaryR_reindex_iff_selectedResidual (exactIds : List String)
    (idSets : List (String × List String)) :
    (∀ sub : Input, R_ActiveBoundaryR exactIds (reindexRegionSets idSets sub)) ↔
      (∀ sub : Input, R_ActiveBoundarySelectedResidual exactIds (reindexRegionSets idSets sub)) := by
  constructor
  · intro h sub
    exact (r_activeBoundaryR_iff_selectedResidual exactIds (reindexRegionSets idSets sub)).mp (h sub)
  · intro h sub
    exact (r_activeBoundaryR_iff_selectedResidual exactIds (reindexRegionSets idSets sub)).mpr (h sub)

theorem flatC5B_layoutRIds_reindex_of_selectedResidual (exactIds : List String)
    (idSets : List (String × List String))
    (h : ∀ sub : Input, R_ActiveBoundarySelectedResidual exactIds (reindexRegionSets idSets sub)) :
    FlatC5B (fun sub o => layoutRIds exactIds (reindexRegionSets idSets sub) sub o) := by
  intro sub o res hwf hfp hok
  exact flatC5B_layoutRIds_activeOnly exactIds (reindexRegionSets idSets sub)
    ((r_activeBoundaryR_reindex_iff_selectedResidual exactIds idSets).mpr h sub) hwf hfp hok

end Elegant.Layered.PipelineImpl

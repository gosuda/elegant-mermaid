import Elegant.Layered.ExactRunPathGroupsProof
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionPlacement
import Elegant.Layered.RegionPipeline
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionRunChainFacts
import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionFlatC4
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.FrameClearanceSeam

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region flat clause 6, well-formed-local (W) form (`flatC6B_layoutRIds_W`).

Packet P12 (`local://region-tower-plan.md`, field 6 `flatC6`): the region
twins of the eight `X6_` residuals of `ExactFlatC6Proof.lean`, each over
`SceneExecutionR exactIds idSets` with local `WellFormed`/`framedParents`
after the execution binder, plus the `FlatC6B` assembler replayed over
`SceneExecutionR`.

`FlatC6B` for regions is true as stated (the region plan section 4 lists no
C6 counterexample; region composite frames only strengthen the clearance
hypothesis). The assembly `r6_c6` replays `x6_c6` over the region route
source `r6c6RouteSourceR` (copy of `rpbRouteSourceR` with a file-unique
prefix, since that theorem is private to `RegionC5PlainBoundary.lean`).
The chain/loop transport cases stay open as `R6_ChainCaseW` /
`R6_LoopCaseW`, built from the narrower leaves by open builder functions
mirroring `flatC6B_layoutXW`.

Proved here: `R6_ChainEndpointKeysW` (`r6_chainEndpointKeys_holds`) and
`R6_DeclOutsidePathsW` (`r6_declOutsidePaths_holds`, modulo the run-level
path residual `R6_RunPathGroupsW` proved as `r6_runPathGroups_holds`),
by replaying `ExactFlatC6KeysPathsProof.lean` /
`ExactRunPathGroupsProof.lean` over `componentRunR_specR`.
`R6_ExclusiveRunNodeDecl` is proved in `RegionRunNodeIdentity`.
The remaining `R6_` leaves include `R6_ShelfPositiveW`,
`R6_LoopFootprintSeparationW`, `R6_BorderZeroRealW`,
`R6_RouteScopeBridgeW`, `R6_ChainCaseW`, and `R6_LoopCaseW`. They hold on
the well-formed, framed probe inputs in
`proofs/wip/Probe/RegionFlatC6TProbe.lean`: two-region, nested, titled,
two-cycle, and fixed-parent layouts.
-/

/-- Region twin of `X_ExclusiveRunNodeDecl`: the run node of an exclusive box
keeps its declaration through `componentRunR`. -/
def R6_ExclusiveRunNodeDecl (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec)
    (cg' : Graph) (run : Run),
    comp ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok (cg', run) →
    ∀ (v key : Nat) (source : ModelBox),
      comp[v]? = some key →
      inp.boxes[key]? = some source →
      RouteImpl.nodeDecl run.proper v = key

/-- Region twin of `X6_RouteScopeBridgeW`: same bridge disjunction with local
admission after the execution binder, over `componentRunR`. -/
def R6_RouteScopeBridgeW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {comp : List Nat} {candidate : Nat} {spec' : Option RegionSpec}
    {cg : Graph} {run : Run}
    {loops : List (Nat × LoopPlacement)} {area : Int}
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hcomp : comp ∈ components execution.graph)
    (_hrun : componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok (cg, run))
    (_hloops : componentLoops execution.params
      cg run execution.measured = .ok loops)
    (_hpart : q.1.2 = { placeComponentExact execution.params
      cg run 0 execution.measured loops with area := area })
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i : Nat} {edge : Edge}
    (_hedge : cg.edges[i]? = some edge)
    {route : Route} {box : Box}
    (_hroute : res.scene.routes[edge.decl]? = some route)
    (_hboxmem : box ∈ res.scene.boxes)
    (_hex : box.exclusive = true)
    (_hscope : box.id ∉ LayoutDump.routeScope res.scene.layoutDump route),
    (∃ v : Nat, v < cg.nodes.length ∧
      RouteImpl.IsReal run.proper v ∧
      (∀ rt ∈ run.routes, ∀ i₀ i₁,
        (RouteImpl.edgesOf run.proper rt.original).head? = some i₀ →
        (RouteImpl.edgesOf run.proper rt.original).getLast? = some i₁ →
        v ≠ (RouteImpl.edgeAt run.proper i₀).tail →
        v ≠ (RouteImpl.edgeAt run.proper i₁).head →
        RouteImpl.nodeDecl run.proper v ∉
          ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]?).map
            (·.node.clusterPath)).getD [] ∧
        RouteImpl.nodeDecl run.proper v ∉
          ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]?).map
            (·.node.clusterPath)).getD []) ∧
      box.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBoundsX execution.params
                cg run execution.measured loops).minX)
              (0 - (placeBoundsX execution.params
                cg run execution.measured loops).minY)
              (frameRect execution.params cg run v))))
    ∨
    ∃ c' : Nat, ∃ r' : Rect, c' ≠ c ∧ packed.boxes[c']? = some r' ∧
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH r')).Contained box.rect)

/-- Region twin of `X6_ChainEndpointKeysW`: endpoint resolution with local
admission after the execution binder, over `componentRunR`. -/
def R6_ChainEndpointKeysW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec)
    (cg' : Graph) (run : Run),
    comp ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok (cg', run) →
    ∀ (i : Nat) (edge : Edge) (native : EdgeRoute),
      (run.routes[i]? = some native) →
      (native.original = i) →
      (cg'.edges[i]? = some edge) →
      ∀ (i₀ i₁ : Nat),
        (RouteImpl.edgesOf run.proper native.original).head? = some i₀ →
        (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁ →
        ∃ (tailKey headKey index : Nat) (route₀ : ModelRoute) (raw : Edge)
          (nT nH : Node),
          comp[(RouteImpl.edgeAt run.proper i₀).tail]? = some tailKey ∧
          comp[(RouteImpl.edgeAt run.proper i₁).head]? = some headKey ∧
          execution.graph.nodes[tailKey]? = some nT ∧
          execution.graph.nodes[headKey]? = some nH ∧
          (nT.decl = raw.tail ∨ nT.decl = raw.head) ∧
          (nH.decl = raw.tail ∨ nH.decl = raw.head) ∧
          inp.routes[index]? = some route₀ ∧
          edgeOf inp route₀ index = .ok raw ∧
          edge.decl = index

/-- Region twin of `X6_DeclOutsidePathsW`: exclusive-decl path exclusion with
local admission after the execution binder, over `componentRunR`. -/
def R6_DeclOutsidePathsW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec)
    (cg' : Graph) (run : Run),
    comp ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok (cg', run) →
    ∀ (v : Nat) (key : Nat),
      RouteImpl.nodeDecl run.proper v = key →
      inp.boxes[key]?.map (·.exclusive) = some true →
      ∀ (i : Nat) (edge : Edge) (native : EdgeRoute),
        run.routes[i]? = some native →
        (cg'.edges[i]? = some edge) →
        ∀ (i₀ i₁ : Nat),
          (RouteImpl.edgesOf run.proper native.original).head? = some i₀ →
          (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁ →
          key ∉ ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]?).map
            (·.node.clusterPath)).getD [] ∧
          key ∉ ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]?).map
            (·.node.clusterPath)).getD []

/-- Region twin of `X6_ShelfPositiveW`: shelf positivity with local admission
after the execution binder. -/
def R6_ShelfPositiveW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {spec' : Option RegionSpec} {i : Nat} {edge : Edge}
    (_hedge : (componentCandidateR spec' execution.graph q.1.1 candidate).edges[i]? =
      some edge),
    0 < (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (packed.boxes[c]?.getD default))).w ∧
    0 < (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (packed.boxes[c]?.getD default))).h

/-- Region twin of `X6_LoopFootprintSeparationW`: footprint separation with
local admission after the execution binder. -/
def R6_LoopFootprintSeparationW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec)
    (cg' : Graph) (run : Run) (v b : Nat),
    comp ∈ components execution.graph →
    ((componentCandidateR spec' execution.graph comp candidate).nodes.getD b default).border = 0 →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok (cg', run) →
    LoopFootprintSeparation (componentCandidateR spec' execution.graph comp candidate) run
      execution.measured v b

/-- Region twin of `X6_BorderZeroRealW`: real-node border zero with local
admission after the execution binder. -/
def R6_BorderZeroRealW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (candidate : Nat) (spec' : Option RegionSpec) (cg : Graph) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed),
    ∀ {c : Nat} {q : (List Nat × Part) × Rect},
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    ∀ {area : Int} {loops : List (Nat × LoopPlacement)},
    q.1.2 = { placeComponentExact execution.params
      cg run 0 execution.measured loops with area := area } →
    q.1.1 ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok (cg, run) →
    ∀ {v : Nat} {b : Box},
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    0 < b.rect.w → 0 < b.rect.h →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              cg run execution.measured loops).minX)
            (0 - (placeBoundsX execution.params
              cg run execution.measured loops).minY)
            (frameRect execution.params cg run v)))) →
    ((componentCandidateR spec' execution.graph q.1.1 candidate).nodes.getD v default).border = 0

/-- Region twin of `X6_ChainCaseW`: chain clearance with local admission after
the execution binder. -/
def R6_ChainCaseW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true),
    FrameClearanceSeam inp o res → R6_RouteScopeBridgeW exactIds idSets →
    ∀ {r : Route} {b : Box}, r ∈ res.scene.routes → b ∈ res.scene.boxes →
    b.exclusive = true →
    b.id ∉ LayoutDump.routeScope res.scene.layoutDump r →
    ∀ {key : Nat}, res.scene.routes[key]? = some r → key < inp.routes.length →
    ∀ {packed : Pack.State} {c : Nat} {q : (List Nat × Part) × Rect}
      {candidate : Nat} {spec' : Option RegionSpec} {cg : Graph} {run : Run}
      {loops : List (Nat × LoopPlacement)}
      {i : Nat} {edge : Edge} (area : Int),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok (cg, run) →
    componentLoops execution.params
      cg run execution.measured = .ok loops →
    q.1.2 = { placeComponentExact execution.params
      cg run 0 execution.measured loops with area := area } →
    cg.edges[i]? = some edge →
    edge.decl = key →
    loops.find? (fun l => l.1 == edge.decl) = none →
    ¬ Polyline.hitsRect r.points b.rect

/-- Region twin of `X6_LoopCaseW`: loop clearance with local admission after
the execution binder. -/
def R6_LoopCaseW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true),
    FrameClearanceSeam inp o res → R6_RouteScopeBridgeW exactIds idSets →
    (∀ (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec)
      (cg' : Graph) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidateR spec' execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRunR execution.params (exactDecls exactIds inp) spec' inp
        (componentCandidateR spec' execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok (cg', run) →
      LoopFootprintSeparation (componentCandidateR spec' execution.graph comp candidate) run
        execution.measured v b) →
    ∀ {r : Route} {b : Box}, r ∈ res.scene.routes → b ∈ res.scene.boxes →
    b.exclusive = true →
    b.id ∉ LayoutDump.routeScope res.scene.layoutDump r →
    ∀ {key : Nat}, res.scene.routes[key]? = some r → key < inp.routes.length →
    ∀ {packed : Pack.State} {c : Nat} {q : (List Nat × Part) × Rect}
      {candidate : Nat} {spec' : Option RegionSpec} {cg : Graph} {run : Run}
      {loops : List (Nat × LoopPlacement)}
      {i : Nat} {edge : Edge} (area : Int),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok (cg, run) →
    componentLoops execution.params
      cg run execution.measured = .ok loops →
    q.1.2 = { placeComponentExact execution.params
      cg run 0 execution.measured loops with area := area } →
    cg.edges[i]? = some edge →
    edge.decl = key →
    ∀ {loop : Nat × LoopPlacement},
    loops.find? (fun l => l.1 == edge.decl) = some loop →
    ¬ Polyline.hitsRect r.points b.rect

/-- Mapped zip-indexed decl preservation (prefixed copy of `rpb_map_decl_of_mem`
in `RegionC5PlainBoundary.lean`, private there). -/
private theorem r6c6_map_decl_of_mem (l : List Edge) (n : Nat) (f : Edge × Nat → Edge)
    (hf : ∀ q ∈ l.zipIdx n, (f q).decl = q.1.decl) :
    (((l.zipIdx n).map f).map (·.decl) = l.map (·.decl)) := by
  induction l generalizing n with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    have htail := ih (n + 1) (fun q hq => hf q (List.mem_cons_of_mem (e, n) hq))
    rw [htail]
    have hhead := hf (e, n) (by simp)
    simpa using congrArg (fun d => d :: rest.map (·.decl)) hhead

/-- Region candidate preserves edge declarations (prefixed copy of
`rpbCandidateRDeclsR`, private there). -/
private theorem r6c6CandidateDecls (spec' : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec' g comp index).edges.map (·.decl) =
      (componentGraph g comp).edges.map (·.decl) := by
  cases spec' with
  | none => exact componentCandidate_decls g comp index
  | some _ =>
    unfold componentCandidateR
    dsimp only
    let raw := componentGraph g comp
    let sourceEdges := raw.edges.map Edge.original
    let flags := if index == 2 then groupGreedyFlags
      ({ raw with edges := sourceEdges } : Graph)
      else List.replicate sourceEdges.length false
    have hzip : ((sourceEdges.zipIdx.map fun q =>
        if flags.getD q.2 false then
          { q.1 with tail := q.1.head, head := q.1.tail, reversed := true }
        else q.1).map (·.decl)) = sourceEdges.map (·.decl) :=
      r6c6_map_decl_of_mem sourceEdges 0 _ (fun q _ => by split <;> rfl)
    have horig : (sourceEdges.map (·.decl)) = raw.edges.map (·.decl) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e _
      exact Edge.original_decl e
    rw [hzip, horig]

-- (namespace PipelineImpl continues; route source below stays inside it)
/-- Region route-component source (prefixed copy of `rpbRouteSourceR`, private
in `RegionC5PlainBoundary.lean`): every input route index resolves through
the exact graph to a selected component, a region run, loops, and a placed
part. -/
private theorem r6c6RouteSourceR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} (hkey : key < inp.routes.length) :
    ∃ (packed : Pack.State) (c : Nat) (q : (List Nat × Part) × Rect)
      (candidate : Nat) (run : Run) (loops : List (Nat × LoopPlacement))
      (area : Int) (spec' : Option RegionSpec) (cg : Graph)
      (i : Nat) (edge : Edge),
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q ∧
      componentRunR execution.params (exactDecls exactIds inp) spec' inp
        (componentCandidateR spec' execution.graph q.1.1 candidate)
        execution.measured (candidateOrder candidate) = .ok (cg, run) ∧
      componentLoops execution.params cg run execution.measured = .ok loops ∧
      q.1.2 = { placeComponentExact execution.params cg run 0
        execution.measured loops with area := area } ∧
      cg.edges[i]? = some edge ∧ edge.decl = key := by
  have hdecl : key ∈ execution.graph.edges.map (·.decl) := by
    rw [exactGraph_decl_rangeX execution.graph0_eq execution.graph_eq]
    exact List.mem_range'.mpr ⟨key, hkey, by omega⟩
  obtain ⟨globalEdge, hglobalEdge, hglobalDecl⟩ := List.mem_map.mp hdecl
  have hglobalBounds := sceneExecutionR_edges_boundedR execution globalEdge
    (List.mem_append_left _ hglobalEdge)
  obtain ⟨component, hcomponent, htail⟩ :=
    components_cover hglobalBounds.1 (sceneExecutionR_edges_boundedR execution)
  obtain ⟨hparts, hall⟩ := actual_components_parts_geometryR (by rfl)
    execution.components_eq
  have hcomponentPart : component ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hparts]
    exact hcomponent
  obtain ⟨part, hpartMember, hpartComponent⟩ := List.mem_map.mp hcomponentPart
  obtain ⟨candidate, _, cg, run, loops, area, spec', _, _, _, _, hrun,
    hloops, hpartdef⟩ := hall part hpartMember
  have htailPart : globalEdge.tail ∈ part.1 := by
    simpa only [hpartComponent] using htail
  have hrawDecl : globalEdge.decl ∈
      (componentGraph execution.graph part.1).edges.map (·.decl) := by
    unfold componentGraph
    dsimp only
    apply List.mem_map.mpr
    refine ⟨Edge.mk (part.1.idxOf globalEdge.tail)
      (part.1.idxOf globalEdge.head) globalEdge.minLen globalEdge.decl
      globalEdge.reversed, ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨globalEdge, List.mem_filter.mpr
      ⟨hglobalEdge, List.contains_iff_mem.mpr htailPart⟩, rfl⟩
  have hcandDecl : globalEdge.decl ∈ (componentCandidateR spec'
      execution.graph part.1 candidate).edges.map (·.decl) := by
    rw [r6c6CandidateDecls]
    exact hrawDecl
  have hrankDecl : globalEdge.decl ∈ cg.edges.map (·.decl) := by
    rw [componentRunR_edges_declsR hrun]
    exact hcandDecl
  rw [hglobalDecl] at hrankDecl
  obtain ⟨edge, hedgeMember, hedgeDecl⟩ := List.mem_map.mp hrankDecl
  obtain ⟨i, hedge⟩ := List.mem_iff_getElem?.mp hedgeMember
  obtain ⟨packed, hpacked, _⟩ := packAcc_components_disjoint execution.packed_eq
  obtain ⟨c, hpartIndex⟩ := List.mem_iff_getElem?.mp hpartMember
  have hc := (List.getElem?_eq_some_iff.mp hpartIndex).1
  have hpackedCount : packed.boxes.length =
      execution.componentsAcc.parts.length := by
    simpa only [List.length_map] using Pack.pack_count hpacked
  have hpositionBound : c < packed.boxes.length := by omega
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
      some (part, packed.boxes[c]'hpositionBound) :=
    List.getElem?_zip_eq_some.mpr
      ⟨hpartIndex, List.getElem?_eq_getElem hpositionBound⟩
  exact ⟨packed, c, (part, packed.boxes[c]'hpositionBound), candidate, run,
    loops, area, spec', cg, i, edge, hpacked, hselected, hrun, hloops,
    hpartdef, hedge, hedgeDecl⟩
/-- Executed region C6 core, replaying `x6_core` over `r6c6RouteSourceR`:
a scene route misses an exclusive scene box outside its route scope. -/
theorem r6_core {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hchain : R6_ChainCaseW exactIds idSets)
    (hloop : R6_LoopCaseW exactIds idSets)
    (hclear : FrameClearanceSeam inp o res)
    (hbridge : R6_RouteScopeBridgeW exactIds idSets)
    (hsepW : R6_LoopFootprintSeparationW exactIds idSets)
    {r : Route} {b : Box}
    (hr : r ∈ res.scene.routes) (hb : b ∈ res.scene.boxes)
    (hex : b.exclusive = true)
    (hscope : b.id ∉ LayoutDump.routeScope res.scene.layoutDump r) :
    ¬ Polyline.hitsRect r.points b.rect := by
  obtain ⟨key, hkget⟩ := List.mem_iff_getElem?.mp hr
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length execution.params inp o execution.lines
      execution.packedAcc execution.measured
  have hkey : key < inp.routes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hkget).1
  obtain ⟨packed, c, q, candidate, run, loops, area, spec', cg, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    r6c6RouteSourceR execution hkey
  have hsep : ∀ (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec)
      (cg' : Graph) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidateR spec' execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRunR execution.params (exactDecls exactIds inp) spec' inp
        (componentCandidateR spec' execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok (cg', run) →
      LoopFootprintSeparation (componentCandidateR spec' execution.graph comp candidate) run
        execution.measured v b :=
    fun comp candidate spec' cg' run v b hcomp hbord hrun =>
      hsepW execution hwf hfp comp candidate spec' cg' run v b hcomp hbord hrun
  cases hfound : loops.find? (fun l => l.1 == edge.decl) with
  | none =>
    exact hchain execution hwf hfp hclear hbridge hr hb hex hscope hkget hkey area
      hpacked hselected hrun hloops hpart hedge hdecl hfound
  | some loop =>
    exact hloop execution hwf hfp hclear hbridge hsep
      hr hb hex hscope hkget hkey area hpacked hselected hrun hloops hpart hedge hdecl
      hfound
/-- Flat clause 6 for the region pipeline, assembled from the executed
region seams, replaying `x6_c6`. -/
theorem r6_c6 {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hchain : R6_ChainCaseW exactIds idSets)
    (hloop : R6_LoopCaseW exactIds idSets)
    (hclear : FrameClearanceSeam inp o res)
    (hbridge : R6_RouteScopeBridgeW exactIds idSets)
    (hsepW : R6_LoopFootprintSeparationW exactIds idSets)
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    Validator.C6 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  intro r hr b hb hex hscope
  exact r6_core execution hwf hfp hchain hloop hclear hbridge hsepW hr hb hex hscope
/-- Flat clause 6 for the region pipeline from W-form premises: replay of
`flatC6B_layoutXW` over `SceneExecutionR`. `FlatC6B` supplies `WellFormed`,
`framedParents`, and the frame-clearance seam per input; each is threaded
into the W leaves. The chain/loop builders stay open (their leaves
`R6_ShelfPositiveW`, `R6_BorderZeroRealW`, `R6_ExclusiveRunNodeDecl` close
separately); the keys/paths leaves are closed below. -/
theorem flatC6B_layoutRIds_W (exactIds : List String)
    (idSets : List (String × List String))
    (hdecl : R6_ExclusiveRunNodeDecl exactIds idSets)
    (hkeysW : R6_ChainEndpointKeysW exactIds idSets)
    (hpathsW : R6_DeclOutsidePathsW exactIds idSets)
    (hposW : R6_ShelfPositiveW exactIds idSets)
    (hsepW : R6_LoopFootprintSeparationW exactIds idSets)
    (hbordW : R6_BorderZeroRealW exactIds idSets)
    (hbridgeW : R6_RouteScopeBridgeW exactIds idSets)
    (hchainW : R6_ExclusiveRunNodeDecl exactIds idSets →
      R6_ChainEndpointKeysW exactIds idSets →
      R6_DeclOutsidePathsW exactIds idSets → R6_ShelfPositiveW exactIds idSets →
      R6_ChainCaseW exactIds idSets)
    (hloopW : R6_ShelfPositiveW exactIds idSets → R6_BorderZeroRealW exactIds idSets →
      R6_LoopCaseW exactIds idSets) :
    FlatC6B (layoutRIds exactIds idSets) := by
  intro inp o res hwf hfp _hpos hclear hlay
  have hchain : R6_ChainCaseW exactIds idSets := hchainW hdecl hkeysW hpathsW hposW
  have hloop : R6_LoopCaseW exactIds idSets := hloopW hposW hbordW
  exact r6_c6 hwf hfp hchain hloop hclear hbridgeW hsepW hlay
/-- Residual (run-level cluster-path provenance, W form): every index occurring
in the cluster path of a proper node of an executed region component run is
the index of a group-role box of the input. Strictly simpler than the
endpoint exclusion (a per-node path-membership fact, not a route statement).
True on all probes in `proofs/wip/Probe/RegionFlatC6TProbe.lean`. -/
def R6_RunPathGroupsW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec)
    (cg' : Graph) (run : Run),
    comp ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok (cg', run) →
    ∀ (i : Nat) (nd : ProperNode),
      run.proper.nodes[i]? = some nd →
      ∀ (k : Nat), k ∈ nd.node.clusterPath → ∀ (b : ModelBox),
        inp.boxes[k]? = some b → b.role = .group
/-- Region exclusive-declaration path exclusion in W form, modulo the
run-level path residual `R6_RunPathGroupsW`: an exclusive declaration occurs
in no endpoint cluster path (mirror of
`exclusiveDeclOutsideEndpointPaths_of_clusterPath`; the run-node declaration
premise is already closed by `x_exclusiveRunNodeDecl_holds`). -/
theorem r6_declOutsidePaths_holds (exactIds : List String)
    (idSets : List (String × List String))
    (hgroups : R6_RunPathGroupsW exactIds idSets) :
    R6_DeclOutsidePathsW exactIds idSets := by
  intro inp o _res execution _hwf _hfp comp candidate spec' cg' run hcomp hrun v key hdecl hexcl i
    edge native hnative hedge i₀ i₁ hfirst hlast
  obtain ⟨source, hsource, hexcl'⟩ : ∃ source : ModelBox,
      inp.boxes[key]? = some source ∧ source.exclusive = true :=
    Option.map_eq_some_iff.mp hexcl
  have hrole : source.role ≠ .group := by
    intro hg
    obtain ⟨_, _, _, _, _, _, hgroupbox⟩ := (wellFormed_iff (inputModel inp o)).mp _hwf
    have hcontra := hgroupbox source (List.mem_of_getElem? hsource) hg
    rw [hcontra] at hexcl'
    exact Bool.noConfusion hexcl'
  constructor
  · intro hmem
    cases hnode : run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]? with
    | none => simp [hnode] at hmem
    | some nd =>
      simp only [hnode, Option.map_some, Option.getD_some] at hmem
      exact hrole (hgroups execution _hwf _hfp comp candidate spec' cg' run hcomp hrun _ nd
        hnode key hmem source hsource)
  · intro hmem
    cases hnode : run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]? with
    | none => simp [hnode] at hmem
    | some nd =>
      simp only [hnode, Option.map_some, Option.getD_some] at hmem
      exact hrole (hgroups execution _hwf _hfp comp candidate spec' cg' run hcomp hrun _ nd
        hnode key hmem source hsource)
/-- Endpoint projection of the pristine form of an edge (prefixed copy). -/
private theorem r6c6_edge_original_tail (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  unfold Edge.original
  split <;> simp_all
/-- Endpoint projection of the pristine form of an edge (prefixed copy). -/
private theorem r6c6_edge_original_head (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  unfold Edge.original
  split <;> simp_all
/-- Component lookup at the position of a member (prefixed copy). -/
private theorem r6c6_comp_idxOf_lookup {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))
/-- Endpoint case split on prepared boxes (prefixed copy). -/
private theorem r6c6_endpoint_cases {boxes : List ModelBox} (s : Bool) (i j : Nat) :
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
/-- Count monotonicity for the bottom-marker index argument (prefixed copy). -/
private theorem r6c6_countP_take_add_one {α : Type} (p : α → Bool)
    {l : List α} {i n : Nat} (hn : n ≠ 0) (hi : i < l.length) (hpi : p l[i] = true) :
    (l.take i).countP p + 1 ≤ (l.take (i + n)).countP p := by
  have hsplit : (l.take (i + n)).countP p =
      (l.take i).countP p + ((l.drop i).take n).countP p := by
    rw [List.take_add, List.countP_append]
  rw [hsplit]
  have hwindow : l[i] ∈ (l.drop i).take n := by
    have h1 : (l.drop i)[0]? = some l[i] := by
      rw [List.getElem?_drop, Nat.add_zero]
      exact List.getElem?_eq_getElem hi
    have h2 : ((l.drop i).take n)[0]? = (l.drop i)[0]? := by
      rw [List.getElem?_take]
      simp [Nat.pos_of_ne_zero hn]
    have h0 : ((l.drop i).take n)[0]? = some l[i] := by rw [h2, h1]
    exact List.mem_of_getElem? h0
  have hge : 1 ≤ (((l.drop i).take n).filter p).length := by
    have hmem : p l[i] = true := hpi
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hwindow, hmem⟩
  simp only [List.countP_eq_length_filter]
  omega
/-- Local copy of the bottom-marker list (definition matches `markExtras`). -/
private def r6c6_bottomNodesOf (full sub : List ModelBox) (off : Nat) : List Node :=
  (sub.zipIdx off).filterMap fun q =>
    if q.1.role == .group then
      some {
        decl := q.2, w := 0, h := 0,
        clusterPath := Compound.path full q.1 ++ [q.2], border := 2 }
    else none
/-- Bottom-node declaration lookup (prefixed copy). -/
private theorem r6c6_bottomNodesOf_getElem?_decl {full sub : List ModelBox} {off k : Nat}
    {x : Node} (hx : (r6c6_bottomNodesOf full sub off)[k]? = some x) :
    ∃ d g, sub[d]? = some g ∧ g.role = .group ∧ x.decl = d + off ∧
      ((sub.take d).filter fun b => b.role == .group).length = k := by
  induction sub generalizing off k with
  | nil => simp [r6c6_bottomNodesOf] at hx
  | cons b bs ih =>
    unfold r6c6_bottomNodesOf at hx
    rw [List.zipIdx_cons] at hx
    by_cases hb : b.role = .group
    · have hbeq : (b.role == .group) = true := beq_iff_eq.mpr hb
      simp only [hbeq, ↓reduceIte, List.filterMap_cons] at hx
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨0, b, List.getElem?_cons_zero, hb, by simp, by simp⟩
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := ih hx
        refine ⟨d + 1, g, ?_, hgg, ?_, ?_⟩
        · simpa using hdg
        · have : d + 1 + off = d + (off + 1) := by omega
          rw [this]; exact hdecl
        · have htake : ((b :: bs).take (d + 1)).filter
              (fun b => b.role == .group) =
            b :: (bs.take d).filter (fun b => b.role == .group) := by
            rw [List.take_succ_cons]
            simp [hb]
          rw [htake, List.length_cons, hcount]
    · have hbf : (b.role == .group) = false := by
        cases hz : (b.role == .group) with
        | true => exact absurd (beq_iff_eq.mp hz) hb
        | false => rfl
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, List.filterMap_cons] at hx
      obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := ih hx
      refine ⟨d + 1, g, ?_, hgg, ?_, ?_⟩
      · simpa using hdg
      · have : d + 1 + off = d + (off + 1) := by omega
        rw [this]; exact hdecl
      · have htake : ((b :: bs).take (d + 1)).filter
            (fun b => b.role == .group) =
          (bs.take d).filter (fun b => b.role == .group) := by
          rw [List.take_succ_cons]
          have hbf2 : (b.role == .group) = false := hbf
          simp only [hbf2, Bool.false_eq_true, ↓reduceIte, List.filter_cons]
        rw [htake, hcount]
/-- The bottom node at `Compound.bottomIndex boxes i` declares `i` (prefixed copy). -/
private theorem r6c6_bottom_node_decl {boxes : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {nodes : List Node} (hlen : nodes.length = boxes.length)
    {i j : Nat} {x : Node} {b : ModelBox}
    (hj : j = boxes.length + ((boxes.take i).filter fun b => b.role == .group).length)
    (hx : (Compound.markNodes boxes pad titles nodes)[j]? = some x)
    (hbi : boxes[i]? = some b) (hb : b.role = .group) :
    x.decl = i := by
  rw [markNodes_eq] at hx
  have htopLen : (nodes.zipIdx.map (markOne boxes pad titles)).length = nodes.length := by
    simp [List.length_map, List.length_zipIdx]
  have hjge : (nodes.zipIdx.map (markOne boxes pad titles)).length ≤ j := by
    rw [htopLen, hlen]; omega
  rw [List.getElem?_append_right hjge] at hx
  have hk : j - (nodes.zipIdx.map (markOne boxes pad titles)).length =
      ((boxes.take i).filter fun b => b.role == .group).length := by omega
  rw [hk] at hx
  have hme : markExtras boxes = r6c6_bottomNodesOf boxes boxes 0 := rfl
  rw [hme] at hx
  obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := r6c6_bottomNodesOf_getElem?_decl hx
  have hi : i < boxes.length := (List.getElem?_eq_some_iff.mp hbi).1
  have hcntI : ((boxes.take i).filter fun b => b.role == .group).length =
      j - (nodes.zipIdx.map (markOne boxes pad titles)).length := by omega
  have hidi : i = d := by
    rcases Nat.lt_trichotomy i d with hlt | heq | hgt
    · have hbdi : (fun b => b.role == .group) b = true := beq_iff_eq.mpr hb
      have hmono := r6c6_countP_take_add_one (p := fun b => b.role == .group)
        (l := boxes) (i := i) (n := d - i) (Nat.sub_ne_zero_of_lt hlt)
        (by omega) (by
          obtain ⟨_, heq⟩ := List.getElem_of_getElem? hbi
          rw [heq]; exact hbdi)
      have hrewrite : i + (d - i) = d := by omega
      rw [hrewrite, List.countP_eq_length_filter,
        List.countP_eq_length_filter] at hmono
      omega
    · exact heq
    · have hdi : d < boxes.length := (List.getElem?_eq_some_iff.mp hdg).1
      have hgid : (fun b => b.role == .group) g = true := beq_iff_eq.mpr hgg
      have hmono := r6c6_countP_take_add_one (p := fun b => b.role == .group)
        (l := boxes) (i := d) (n := i - d) (Nat.sub_ne_zero_of_lt hgt)
        (by omega) (by
          obtain ⟨_, heq⟩ := List.getElem_of_getElem? hdg
          rw [heq]; exact hgid)
      have hrewrite : d + (i - d) = i := by omega
      rw [hrewrite, List.countP_eq_length_filter,
        List.countP_eq_length_filter] at hmono
      omega
  subst hidi
  simpa using hdecl


/-- Reverse key lookup through `exactGraph` (prefixed copy, needed by alias
transport). -/
private theorem r6c6_node_key_rev {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g)
    {v : Nat} {nd : Node} (hv : g.nodes[v]? = some nd) :
    ∃ nd0, g0.nodes[v]? = some nd0 ∧ nd0.border = nd.border ∧
      nd0.clusterPath = nd.clusterPath ∧ nd0.decl = nd.decl := by
  have hlen : g.nodes.length = g0.nodes.length := exactGraph_length h
  have hvlt : v < g0.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have h0 : g0.nodes[v]? = some (g0.nodes[v]'hvlt) := List.getElem?_eq_getElem hvlt
  obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key h h0
  have heq : nd' = nd := Option.some.inj (hnd'.symm.trans hv)
  subst heq
  exact ⟨_, h0, hnb.symm, hnap.symm, hnd.symm⟩


/-- Region alias declaration transport: an aliased endpoint's exact-graph node
carries a model endpoint declaration (prefixed copy of `x6kp_alias_decl`,
over `SceneExecutionR`). -/
private theorem r6c6_alias_decl {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (s : Bool)
    {pos other : Nat} {src tgt : ModelBox}
    (hsrc : inp.boxes[pos]? = some src)
    (_htgt : inp.boxes[other]? = some tgt)
    {a : Nat}
    (ha : a = Compound.endpoint
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) s pos other)
    {node : Node} (hnode : execution.graph.nodes[a]? = some node) :
    node.decl = pos := by
  obtain ⟨nodes0, _edges0, titles0, hprepared, hlen_nodes, hmeta⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
          (mapM_getElem? _ _ _ h).1
      _ = inp.boxes.length := List.length_zipIdx
  have hprep_len : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box).length = inp.boxes.length := by
    simp
  have hlen0 : nodes0.length =
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box).length := by
    rw [hlen_nodes, hlines, hprep_len]
  have hbp : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[pos]? =
      some (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        { src with role := .node } else src) := by
    rw [List.getElem?_map, hsrc]
    simp
  obtain ⟨nd0, hnd0, _, _, hdecl0⟩ := r6c6_node_key_rev execution.graph_eq hnode
  have hnode0 : (Compound.prepare (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)
      execution.params.clusterPad titles0
      { nodes := nodes0, edges := _edges0, slot := execution.params.slot }).nodes[a]? =
      some nd0 := by
    rw [← hprepared]
    exact hnd0
  rw [← hdecl0]
  rcases r6c6_endpoint_cases (boxes := (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)) s pos other with h | ⟨hbot, hgroup⟩
  · have haPos : a = pos := ha.trans h
    rw [haPos] at hnode0
    by_cases hpbG : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        ({ src with role := .node } : ModelBox) else src).role = .group
    · have hfixedFalse : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false := by
        cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) with
        | true =>
          simp only [hf, ↓reduceIte] at hpbG
          exact absurd hpbG (by intro hcon; cases hcon)
        | false => rfl
      have hsrcGroup : src.role = .group := by
        rw [hfixedFalse] at hpbG hbp
        simpa using hpbG
      have hbp' : (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)[pos]? = some src := by
        simpa [hfixedFalse] using hbp
      have hi : pos < nodes0.length := by
        rw [hlen0, hprep_len]
        exact (List.getElem?_eq_some_iff.mp hsrc).1
      have hrec := Compound.prepare_group_title_record _ execution.params.clusterPad titles0
        { nodes := nodes0, edges := _edges0, slot := execution.params.slot }
        hi hbp' hsrcGroup
      have heq := Option.some.inj (hnode0.symm.trans hrec)
      have hdd : nd0.decl = (nodes0[pos]'hi).decl := by rw [heq]
      rw [hdd]
      exact (hmeta pos _ (List.getElem?_eq_getElem hi)).1
    · have hplain : ¬ (src.role = .group ∧
          inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false) := by
        intro ⟨hr, hf⟩
        simp [hf, hr] at hpbG
      have hng : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
          ({ src with role := .node } : ModelBox) else src).role ≠ .group := by
        by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = true
        · simp only [hf, ↓reduceIte]
          decide
        · have hf' : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false :=
            Bool.eq_false_iff.mpr hf
          simp only [hf']
          intro hrole
          exact hplain ⟨hrole, hf'⟩
      have hi : pos < nodes0.length := by
        rw [hlen0, hprep_len]
        exact (List.getElem?_eq_some_iff.mp hsrc).1
      have hrec := Compound.prepare_plain_node_record _ execution.params.clusterPad titles0
        { nodes := nodes0, edges := _edges0, slot := execution.params.slot }
        hi hbp hng
      have heq := Option.some.inj (hnode0.symm.trans hrec)
      have hdd : nd0.decl = (nodes0[pos]'hi).decl := by rw [heq]
      rw [hdd]
      exact (hmeta pos _ (List.getElem?_eq_getElem hi)).1
  · have haBot : a = Compound.bottomIndex
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) pos := ha.trans hbot
    have hpbG : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        ({ src with role := .node } : ModelBox) else src).role = .group := by
      have hb := hgroup _ hbp
      simpa using hb
    have hx : (Compound.markNodes (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
        execution.params.clusterPad titles0 nodes0)[a]? = some nd0 := by
      have h2 := hnode0
      rw [Compound.prepare_nodes] at h2
      exact h2
    have hj : a = (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box).length +
        (((inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box).take pos).filter
          fun b => b.role == .group).length := by
      rw [haBot]; rfl
    exact r6c6_bottom_node_decl hlen0 hj hx hbp hpbG
/-- Region alias declaration transport in disjunction form (prefixed copy of
`x6kp_alias_transport`, over `SceneExecutionR`). -/
private theorem r6c6_alias_transport {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {index : Nat} {route : ModelRoute} {raw : Edge}
    (_hroute : inp.routes[index]? = some route)
    (hraw : edgeOf inp route index = .ok raw)
    {a : Nat} {node : Node}
    (ha : a = (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).tail ∨
      a = (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).head)
    (hnode : execution.graph.nodes[a]? = some node) :
    node.decl = raw.tail ∨ node.decl = raw.head := by
  obtain ⟨_hdecl₂, _hrev₂, src, tgt, hsrc, _hsrcId, htgt, _htgtId⟩ :=
    edgeOf_semantic_endpoints hraw
  rcases ha with haT | haH
  · have htail : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail =
        Compound.endpoint (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) true raw.tail raw.head := rfl
    have haTail : a = Compound.endpoint (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) true raw.tail raw.head := by
      rw [haT, htail]
    have hdeclEq := r6c6_alias_decl execution true hsrc htgt haTail hnode
    exact Or.inl hdeclEq
  · have hhead : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head =
        Compound.endpoint (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) false raw.head raw.tail := rfl
    have haHead : a = Compound.endpoint (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) false raw.head raw.tail := by
      rw [haH, hhead]
    have hdeclEq := r6c6_alias_decl execution false htgt hsrc haHead hnode
    exact Or.inr hdeclEq
/-- Peel helper (prefixed copy: `bind_ok` is private in every module that uses it). -/
private theorem r6c6_bind_ok {α β : Type}
    {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Rank rewriting preserves each edge's `original` and `decl`: per-membership
version (prefixed copy of `rpbRankEdgeOrigMem`, private there). -/
private theorem r6c6RankEdgeOrigMem {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cgIn cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cgIn labels orderOptions = .ok (cg, run))
    {e : Edge} (hmem : e ∈ cg.edges) :
    ∃ e0 ∈ cgIn.edges, e.original = e0.original ∧ e.decl = e0.decl := by
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hs⟩ := componentRunR_specR hrun
  obtain ⟨hRs, hRank, hNorm, hLabels, hCoord, hMin, hOrd, hLabelWidths, hPlaced,
    hProxy, hDrop, hLanes, hYt, hYsMid, hReserve, hRoutes, hRouting, hCoordProper,
    hCoordYs, hBudget, hExact⟩ := hs
  rcases hRank with ⟨rr, hrsNone, _, _, heq, _⟩ | ⟨rm, _, hranked⟩
  · rw [heq] at hmem
    exact ⟨e, hmem, rfl, rfl⟩
  · unfold rankEquivalentR at hranked
    dsimp only at hranked
    split at hranked
    · have hF : False := by
        simp only [bind, Except.bind] at hranked
        exact absurd hranked (by simp)
      exact hF.elim
    · obtain ⟨conds, _, hranked⟩ := r6c6_bind_ok hranked
      obtain ⟨out1, _, hranked⟩ := r6c6_bind_ok hranked
      obtain ⟨flagsAndOut, _, hranked⟩ := r6c6_bind_ok hranked
      obtain ⟨ranked, _, hranked⟩ := r6c6_bind_ok hranked
      have he := Except.ok.inj hranked
      have heq := congrArg (fun q : List Int × Graph × Bool => q.2.1.edges) he
      dsimp only at heq
      rw [← heq] at hmem
      obtain ⟨q, hqmem, hqeq⟩ := List.mem_map.mp hmem
      obtain ⟨a, n⟩ := q
      have hamem : a ∈ cgIn.edges := List.fst_mem_of_mem_zipIdx hqmem
      refine ⟨a, hamem, ?_, ?_⟩ <;>
        (rw [← hqeq]; dsimp only; split)
      · rfl
      · split
        · rfl
        · exact Edge.reverse_original a
      · rfl
      · split
        · rfl
        · exact (Edge.reverse_identity a).1



/-- `Edge.original` is idempotent (prefixed copy). -/
private theorem r6c6_original_idempotent (edge : Edge) :
    edge.original.original = edge.original := by
  cases hr : edge.reversed <;> simp [Edge.original, hr]
/-- Region chain model source, no-region case: replay of `x6kp_chain_mid`
(the candidate coincides with the exact one, via `newComponentRegions_none`
and the `none` ranking arm). -/
private theorem r6c6_chain_mid_none {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {cg' : Graph} {run : Run}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) none inp
      (componentCandidateR none execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok (cg', run))
    {i : Nat} {edge : Edge} (hedge : cg'.edges[i]? = some edge) :
    ∃ (index : Nat) (route : ModelRoute) (raw : Edge),
      inp.routes[index]? = some route ∧ edgeOf inp route index = .ok raw ∧
      edge.decl = index ∧
      edge.original.tail = comp.idxOf
        (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) raw).tail ∧
      edge.original.head = comp.idxOf
        (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) raw).head ∧
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail ∈ comp ∧
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head ∈ comp := by
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hs⟩ := componentRunR_specR hrun
  obtain ⟨hRs, hRank, hNorm, hLabels, hCoord, hMin, hOrd, hLabelWidths, hPlaced,
    hProxy, hDrop, hLanes, hYt, hYsMid, hReserve, hRoutes, hRouting, hCoordProper,
    hCoordYs, hBudget, hExact⟩ := hs
  have hrs : rs = none := by
    have h := (newComponentRegions_none execution.params inp
      (componentCandidateR none execution.graph comp candidate)).symm.trans hRs
    simpa using (Except.ok.inj h).symm
  rcases hRank with ⟨rr, hrsNone, hrrank, _, heq, _⟩ | ⟨rm, hrsSome, hranked⟩
  · have hcg : cg' = componentCandidateR none execution.graph comp candidate := heq
    rw [hcg] at hedge
    have hcadEq : componentCandidateR none execution.graph comp candidate =
        componentCandidate execution.graph comp candidate := rfl
    rw [hcadEq] at hedge
    have hmem : edge ∈ (componentCandidate execution.graph comp candidate).edges :=
      List.mem_of_getElem? hedge
    obtain ⟨index, route, raw, _source, _target, hroute, hrawOf, hdeclIdx,
      _hrawsource, _hsourceId, _hrawtarget, _htargetId, _⟩ :=
      X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq hmem
    obtain ⟨gEdge, hgEdge, hgTailMem, hsemG⟩ :=
      componentCandidate_semantic_source hmem
    have hgEdge0 : gEdge ∈ execution.graph0.edges := by
      rw [exactGraph_edges execution.graph_eq] at hgEdge
      exact hgEdge
    obtain ⟨index₂, route₂, raw₂, hr2Route, hr2EdgeOf, hgeAlias⟩ :=
      measuredGraph_edge_source execution.graph0_eq hgEdge0
    obtain ⟨h2Decl, h2Rev, _, _, _, _⟩ := edgeOf_semantic_endpoints hr2EdgeOf
    have hgeRev : gEdge.reversed = false := by rw [hgeAlias]; exact h2Rev
    have hgeOrig : gEdge.original = gEdge := by
      cases gEdge with
      | mk tail head minLen decl reversed => cases hgeRev; rfl
    have hgeDeclIdx : edge.decl = index₂ := by
      have h1 : edge.decl = gEdge.decl := by
        have h := congrArg Edge.decl hsemG
        simpa only [Edge.original_decl] using h
      rw [h1, hgeAlias, Compound.aliasEdge_decl, h2Decl]
    have hidx₂ : index₂ = index := hgeDeclIdx.symm.trans hdeclIdx
    rw [hidx₂] at hr2Route
    have hroute₂Eq : route₂ = route :=
      Option.some.inj (hr2Route.symm.trans hroute)
    rw [hidx₂, hroute₂Eq] at hr2EdgeOf
    have hrawEq : raw₂ = raw := Except.ok.inj (hr2EdgeOf.symm.trans hrawOf)
    rw [hrawEq] at hgeAlias
    have hbd : ∀ e ∈ execution.graph.edges ++ Compound.constraints execution.graph,
        e.tail < execution.graph.nodes.length ∧
          e.head < execution.graph.nodes.length :=
      sceneExecutionR_edges_boundedR execution
    obtain ⟨comp', hcomp'In, hgTailC, hgHeadC⟩ :=
      components_edge_endpoints hbd (List.mem_append.mpr (Or.inl hgEdge))
    have hcompEq : comp' = comp :=
      components_shared_member_eq hcomp'In hcomp hgTailC hgTailMem
    have htailEq : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail = gEdge.tail :=
      (congrArg Edge.tail hgeAlias).symm
    have hheadEq : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head = gEdge.head :=
      (congrArg Edge.head hgeAlias).symm
    have hgHeadMem : gEdge.head ∈ comp := by rw [← hcompEq]; exact hgHeadC
    have hmemT : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail ∈ comp := by
      rw [htailEq]; exact hgTailMem
    have hmemH : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head ∈ comp := by
      rw [hheadEq]; exact hgHeadMem
    have hsemTail : edge.original.tail = comp.idxOf
        (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) raw).tail := by
      have h := congrArg Edge.tail hsemG
      rw [hgeOrig, hgeAlias] at h
      exact h
    have hsemHead : edge.original.head = comp.idxOf
        (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) raw).head := by
      have h := congrArg Edge.head hsemG
      rw [hgeOrig, hgeAlias] at h
      exact h
    exact ⟨index, route, raw, hroute, hrawOf, hdeclIdx, hsemTail, hsemHead, hmemT, hmemH⟩
  · exact absurd hrsSome (by rw [hrs]; simp)
/-- Original of a reversed edge is pristine (prefixed copy). -/
private theorem r6c6_original_reversed_false (edge : Edge) :
    (edge.original).reversed = false := by
  cases h : edge.reversed <;> simp [Edge.original, h]
















/-- Region run keeps the candidate nodes (copy of `rpbRunNodesEqR`). -/
private theorem r6c6RunNodesEqR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    cg'.nodes = cg.nodes := by
  obtain ⟨rs, _, _, _, _, _, _, _, _, _, _, _, _, _, hRs, hRank, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := componentRunR_specR h
  rcases hRank with ⟨rr, hrsNone, _, _, hcgEq, _⟩ | ⟨rm, _, hrank⟩
  · subst hrsNone
    rw [hcgEq]
  · exact rankEquivalentR_nodes_eq hrank

/-- `componentCandidateR` nodes are the component's graph-node projection. -/
private theorem r6c6_componentCandidateR_nodes (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec g comp index).nodes =
      comp.map (fun v => g.nodes.getD v default) := by
  cases spec with
  | none => exact componentCandidate_nodes g comp index
  | some _ => rfl

/-- Region execution lines cover every input box (copy of `X_lines_len`). -/
private theorem r6c6_lines_len {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (mapM_getElem? _ _ _ h).1
    _ = inp.boxes.length := List.length_zipIdx

/-- The region measured graph covers a nonfixed group box with a
declaration node (copy of `X_nonfixed_group_graph_node`). -/
private theorem r6c6_nonfixed_group_graph_node {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hgroup : source.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) :
    ∃ node : Node, execution.graph0.nodes[key]? = some node ∧ node.border = -2 ∧
      node.decl = key := by
  obtain ⟨nodes, edges, titles, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hi : key < nodes.length := by
    rw [hlength, r6c6_lines_len execution]
    exact (List.getElem?_eq_some_iff.mp hsource).1
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

/-- The region measured graph covers a plain box with a declaration node
(copy of `X_plain_graph_node`). -/
private theorem r6c6_plain_graph_node {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hplain : ¬(source.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false)) :
    ∃ node : Node, execution.graph0.nodes[key]? = some node ∧ node.border = 0 ∧
      node.clusterPath = Compound.path inp.boxes source ∧ node.decl = key := by
  obtain ⟨nodes, edges, titles, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hi : key < nodes.length := by
    rw [hlength, r6c6_lines_len execution]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hsource
  have hnotGroup : (if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
      { id := source.id, parent := source.parent, exclusive := source.exclusive,
        direction := source.direction, shape := source.shape, icon := source.icon,
        text := source.text } else source : ModelBox).role ≠ .group := by
    by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true
    · simp only [hf, ↓reduceIte]
      decide
    · have hf' : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false :=
        Bool.eq_false_iff.mpr hf
      simp only [hf']
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

/-- The exact graph node behind a model box carries that box index as its
declaration (copy of `X_graphNodeDeclOfBox`). -/
private theorem r6c6_graphNodeDeclOfBox {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source) :
    ∃ node : Node, execution.graph.nodes[key]? = some node ∧ node.decl = key := by
  by_cases h : source.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false
  · obtain ⟨hrole, hfixed⟩ := h
    obtain ⟨node, hn, _, hdecl⟩ :=
      r6c6_nonfixed_group_graph_node execution hsource hrole hfixed
    obtain ⟨node', hn', _, _, hnd⟩ := exactGraph_node_key execution.graph_eq hn
    exact ⟨node', hn', hnd.trans hdecl⟩
  · have hplain : ¬ (source.role = .group ∧
        inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) := h
    obtain ⟨node, hn, _, _, hdecl⟩ :=
      r6c6_plain_graph_node execution hsource hplain
    obtain ⟨node', hn', _, _, hnd⟩ := exactGraph_node_key execution.graph_eq hn
    exact ⟨node', hn', hnd.trans hdecl⟩

/-- `sizeProperPortsX` keeps declarations, dummy flags, borders and paths
(copy of `X_sizeProperPortsX_decl`). -/
private theorem r6c6_sizeProperPortsX_decl {P : Params} {exact : List Nat} {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (sizeProperPortsX P exact p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  unfold sizeProperPortsX
  simp only [List.getElem?_map, List.getElem?_zipIdx, hv, Option.map_some]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> split <;> rfl

/-- The exact coordinate graph keeps every prefix declaration and path
(copy of `X_coordinateGraphX_decl_prefix`). -/
private theorem r6c6_coordinateGraphX_decl_prefix {P : Params} {exact : List Nat}
    {p : Proper} {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (coordinateGraphX P exact p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧
      (nd.dummy = false → qn.node.clusterPath = nd.node.clusterPath) := by
  unfold coordinateGraphX at ⊢
  obtain ⟨s1, hs1, hdecl1, hdum1, hbord1, hpath1⟩ := r6c6_sizeProperPortsX_decl hv
  obtain ⟨t1, ht1, hdecl2, hdum2, hbord2, hpath2⟩ := titleReservations_decl hs1
  obtain ⟨c1, hc1, hdecl3, hdum3, hbord3, hpath3⟩ :=
    addClusterBorders_decl (w := P.clusterBorderW) ht1
  obtain ⟨e1, he1, hdecl4, hdum4, hbord4, hpath4⟩ := clearProxyExtents_decl hc1
  obtain ⟨m1, hm1, hdecl5, hdum5, hbord5⟩ := materialize_decl he1
  refine ⟨m1, hm1, ?_, ?_, ?_, ?_⟩
  · exact hdecl5.trans (hdecl4.trans (hdecl3.trans (hdecl2.trans hdecl1)))
  · exact hdum5.trans (hdum4.trans (hdum3.trans (hdum2.trans hdum1)))
  · exact hbord5.trans (hbord4.trans (hbord3.trans (hbord2.trans hbord1)))
  · intro hnd
    have he1dum : e1.dummy = false := by
      have h1 : s1.dummy = nd.dummy := hdum1
      have h2 : t1.dummy = s1.dummy := hdum2
      have h3 : c1.dummy = t1.dummy := hdum3
      have h4 : e1.dummy = c1.dummy := hdum4
      rw [h4, h3, h2, h1, hnd]
    have hme : m1.node.clusterPath = e1.node.clusterPath := by
      have hlookup : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some e1 := he1
      unfold materializeDummyPaths at hm1
      simp only [List.getElem?_map, List.getElem?_zipIdx, hlookup,
        Option.map_some] at hm1
      have hF : e1.dummy = false := he1dum
      simp only [hF, Bool.false_eq_true, ↓reduceIte] at hm1
      have heq := Option.some.inj hm1
      rw [heq]
    rw [hme, hpath4, hpath3, hpath2, hpath1]

/-- `titleReservationsR` keeps every prefix declaration and path (only
dimensions change on the prefix). -/
private theorem r6c6_titleReservationsR_decl_prefix {titles : List (Int × Int)}
    {pad : Int} {p : Proper} {v : Nat} {nd : ProperNode}
    (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (titleReservationsR titles pad p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  have hvlt : v < p.nodes.length := (List.getElem?_eq_some_iff.mp hv).1
  unfold titleReservationsR
  have hlen : (p.nodes.map fun node =>
      if node.node.border == -2 || node.node.border == 2 then
        { node with node := { node.node with w := 0, h := 0 } } else node).length =
      p.nodes.length := by simp
  rw [List.getElem?_append_left (by rw [hlen]; exact hvlt)]
  simp only [List.getElem?_map, hv, Option.map_some]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> split <;> rfl

/-- The region coordinate graph keeps every prefix declaration and path. -/
private theorem r6c6_coordinateGraphR_decl_prefix {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {p : Proper} {v : Nat} {nd : ProperNode}
    (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (coordinateGraphR P exact spec p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧
      (nd.dummy = false → qn.node.clusterPath = nd.node.clusterPath) := by
  cases spec with
  | none =>
    rw [coordinateGraphR_none]
    exact r6c6_coordinateGraphX_decl_prefix hv
  | some s =>
    unfold coordinateGraphR
    obtain ⟨s1, hs1, hdecl1, hdum1, hbord1, hpath1⟩ := r6c6_sizeProperPortsX_decl hv
    obtain ⟨t1, ht1, hdecl2, hdum2, hbord2, hpath2⟩ :=
      r6c6_titleReservationsR_decl_prefix hs1
    obtain ⟨c1, hc1, hdecl3, hdum3, hbord3, hpath3⟩ :=
      addClusterBorders_decl (w := P.clusterBorderW) ht1
    obtain ⟨e1, he1, hdecl4, hdum4, hbord4, hpath4⟩ := clearProxyExtents_decl hc1
    obtain ⟨m1, hm1, hdecl5, hdum5, hbord5⟩ := materialize_decl he1
    refine ⟨m1, hm1, ?_, ?_, ?_, ?_⟩
    · exact hdecl5.trans (hdecl4.trans (hdecl3.trans (hdecl2.trans hdecl1)))
    · exact hdum5.trans (hdum4.trans (hdum3.trans (hdum2.trans hdum1)))
    · exact hbord5.trans (hbord4.trans (hbord3.trans (hbord2.trans hbord1)))
    · intro hnd
      have he1dum : e1.dummy = false := by
        have h1 : s1.dummy = nd.dummy := hdum1
        have h2 : t1.dummy = s1.dummy := hdum2
        have h3 : c1.dummy = t1.dummy := hdum3
        have h4 : e1.dummy = c1.dummy := hdum4
        rw [h4, h3, h2, h1, hnd]
      have hme : m1.node.clusterPath = e1.node.clusterPath := by
        have hlookup : (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservationsR s.titles P.clusterPad
            (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
          some e1 := he1
        unfold materializeDummyPaths at hm1
        simp only [List.getElem?_map, List.getElem?_zipIdx, hlookup,
          Option.map_some] at hm1
        have hF : e1.dummy = false := he1dum
        simp only [hF, Bool.false_eq_true, ↓reduceIte] at hm1
        have heq := Option.some.inj hm1
        rw [heq]
      rw [hme, hpath4, hpath3, hpath2, hpath1]
end PipelineImpl

end Layered
end Elegant

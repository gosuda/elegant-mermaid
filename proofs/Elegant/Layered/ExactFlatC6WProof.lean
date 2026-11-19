import Elegant.Layered.ExactFlatC6Proof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact flat clause 6, well-formed-local (W) form (`flatC6B_layoutXW`).

Packet 6 of `local://exact-global-premise-audit.md`: W twins of the eight
`X6_` residuals of `ExactFlatC6Proof.lean`, each with `WellFormed` and
`framedParents` directly after the execution binder, plus the `FlatC6B`
assembler replayed over them. -/

/-- W twin of `X6_RouteScopeBridge`: same bridge disjunction with local
admission after the execution binder. -/
def X6_RouteScopeBridgeW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {comp : List Nat} {candidate : Nat} {run : Run}
    {loops : List (Nat × LoopPlacement)} {area : Int}
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hcomp : comp ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (_hloops : componentLoops execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured
      = .ok loops)
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph comp candidate) run 0 execution.measured
      loops with area := area })
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph comp candidate).edges[i]? =
      some edge)
    {route : Route} {box : Box}
    (_hroute : res.scene.routes[edge.decl]? = some route)
    (_hboxmem : box ∈ res.scene.boxes)
    (_hex : box.exclusive = true)
    (_hscope : box.id ∉ LayoutDump.routeScope res.scene.layoutDump route),
    (∃ v : Nat, v < (componentCandidate execution.graph comp candidate).nodes.length ∧
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
                (componentCandidate execution.graph comp candidate) run
                execution.measured loops).minX)
              (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph comp candidate) run
                execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run v))))
    ∨
    ∃ c' : Nat, ∃ r' : Rect, c' ≠ c ∧ packed.boxes[c']? = some r' ∧
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH r')).Contained box.rect)

/-- W twin of `X6_ChainEndpointKeys`: endpoint resolution with local
admission after the execution binder. -/
def X6_ChainEndpointKeysW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (i : Nat) (edge : Edge) (native : EdgeRoute),
      (run.routes[i]? = some native) →
      (native.original = i) →
      (componentCandidate execution.graph comp candidate).edges[i]? = some edge →
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

/-- W twin of `X6_DeclOutsidePaths`: exclusive-decl path exclusion with
local admission after the execution binder. -/
def X6_DeclOutsidePathsW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (v : Nat) (key : Nat),
      RouteImpl.nodeDecl run.proper v = key →
      inp.boxes[key]?.map (·.exclusive) = some true →
      ∀ (i : Nat) (edge : Edge) (native : EdgeRoute),
        run.routes[i]? = some native →
        (componentCandidate execution.graph comp candidate).edges[i]? = some edge →
        ∀ (i₀ i₁ : Nat),
          (RouteImpl.edgesOf run.proper native.original).head? = some i₀ →
          (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁ →
          key ∉ ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]?).map
            (·.node.clusterPath)).getD [] ∧
          key ∉ ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]?).map
            (·.node.clusterPath)).getD []

/-- W twin of `X6_ShelfPositive`: shelf positivity with local admission
after the execution binder. -/
def X6_ShelfPositiveW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? =
      some edge),
    0 < (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (packed.boxes[c]?.getD default))).w ∧
    0 < (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (packed.boxes[c]?.getD default))).h

/-- W twin of `X6_LoopFootprintSeparation`: footprint separation with local
admission after the execution binder. -/
def X6_LoopFootprintSeparationW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
    comp ∈ components execution.graph →
    ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
      execution.measured v b

/-- W twin of `X6_BorderZeroReal`: real-node border zero with local
admission after the execution binder. -/
def X6_BorderZeroRealW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (candidate : Nat) (run : Run) (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed),
    ∀ {c : Nat} {q : (List Nat × Part) × Rect},
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    ∀ {area : Int} {loops : List (Nat × LoopPlacement)},
    q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area } →
    q.1.1 ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ {v : Nat} {b : Box},
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    0 < b.rect.w → 0 < b.rect.h →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v default).border = 0

/-- W twin of `X6_ChainCase`: chain clearance with local admission after
the execution binder. -/
def X6_ChainCaseW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true),
    FrameClearanceSeam inp o res → X6_RouteScopeBridge exactIds inp o res →
    ∀ {r : Route} {b : Box}, r ∈ res.scene.routes → b ∈ res.scene.boxes →
    b.exclusive = true →
    b.id ∉ LayoutDump.routeScope res.scene.layoutDump r →
    ∀ {key : Nat}, res.scene.routes[key]? = some r → key < inp.routes.length →
    ∀ {packed : Pack.State} {c : Nat} {q : (List Nat × Part) × Rect}
      {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
      {i : Nat} {edge : Edge} (area : Int),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      = .ok loops →
    q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area } →
    (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge →
    edge.decl = key →
    loops.find? (fun l => l.1 == edge.decl) = none →
    ¬ Polyline.hitsRect r.points b.rect

/-- W twin of `X6_LoopCase`: loop clearance with local admission after
the execution binder. -/
def X6_LoopCaseW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true),
    FrameClearanceSeam inp o res → X6_RouteScopeBridge exactIds inp o res →
    (∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b) →
    ∀ {r : Route} {b : Box}, r ∈ res.scene.routes → b ∈ res.scene.boxes →
    b.exclusive = true →
    b.id ∉ LayoutDump.routeScope res.scene.layoutDump r →
    ∀ {key : Nat}, res.scene.routes[key]? = some r → key < inp.routes.length →
    ∀ {packed : Pack.State} {c : Nat} {q : (List Nat × Part) × Rect}
      {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
      {i : Nat} {edge : Edge} (area : Int),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      = .ok loops →
    q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area } →
    (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge →
    edge.decl = key →
    ∀ {loop : Nat × LoopPlacement},
    loops.find? (fun l => l.1 == edge.decl) = some loop →
    ¬ Polyline.hitsRect r.points b.rect

/-- Flat clause 6 from W-form premises: replay of `flatC6B_layoutX` over
the W twins. `FlatC6B` supplies `WellFormed`, `framedParents`, and the
frame-clearance seam per input; each is threaded into the W leaves. -/
theorem flatC6B_layoutXW (exactIds : List String)
    (hdecl : X_ExclusiveRunNodeDecl exactIds)
    (hkeysW : X6_ChainEndpointKeysW exactIds)
    (hpathsW : X6_DeclOutsidePathsW exactIds)
    (hposW : X6_ShelfPositiveW exactIds)
    (hsepW : X6_LoopFootprintSeparationW exactIds)
    (hbordW : X6_BorderZeroRealW exactIds)
    (hbridgeW : X6_RouteScopeBridgeW exactIds)
    (hchainW : X_ExclusiveRunNodeDecl exactIds → X6_ChainEndpointKeysW exactIds →
      X6_DeclOutsidePathsW exactIds → X6_ShelfPositiveW exactIds →
      X6_ChainCaseW exactIds)
    (hloopW : X6_ShelfPositiveW exactIds → X6_BorderZeroRealW exactIds →
      X6_LoopCaseW exactIds) :
    FlatC6B (layoutX exactIds) := by
  intro inp o res hwf hfp hclear hlay
  have hkeys : X6_ChainEndpointKeys exactIds inp o res :=
    fun execution comp candidate run hcomp hrun i edge native hi horig hedge i₀ i₁ hi₀ hi₁ =>
      hkeysW execution hwf hfp comp candidate run hcomp hrun i edge native hi horig hedge i₀ i₁ hi₀ hi₁
  have hpaths : X6_DeclOutsidePaths exactIds inp o res :=
    fun execution comp candidate run hcomp hrun v key hv hkey i edge native hi hedge i₀ i₁ hi₀ hi₁ =>
      hpathsW execution hwf hfp comp candidate run hcomp hrun v key hv hkey i edge native hi hedge i₀ i₁ hi₀ hi₁
  have hpos : X6_ShelfPositive exactIds inp o res :=
    fun execution packed hpacked c q hsel candidate i edge hedge =>
      hposW execution hwf hfp packed hpacked hsel hedge
  have hsep : X6_LoopFootprintSeparation exactIds inp o res :=
    fun execution comp candidate run v b hcomp hbord hrun =>
      hsepW execution hwf hfp comp candidate run v b hcomp hbord hrun
  have hbord : X6_BorderZeroReal exactIds inp o res :=
    fun execution candidate run packed hpack c q hsel area loops hpart hmem hrun v b hreal hb hex hw hh heq =>
      hbordW execution hwf hfp candidate run packed hpack hsel hpart hmem hrun hreal hb hex hw hh heq
  have hbridge : X6_RouteScopeBridge exactIds inp o res :=
    fun execution packed hpacked comp candidate run loops area c q hcomp hrun hloops hpart hsel i edge hedge route box hroute hmem hex hscope =>
      hbridgeW execution hwf hfp packed hpacked hcomp hrun hloops hpart hsel hedge hroute hmem hex hscope
  have hchainWfull : X6_ChainCaseW exactIds := hchainW hdecl hkeysW hpathsW hposW
  have hloopWfull : X6_LoopCaseW exactIds := hloopW hposW hbordW
  have hchain : X6_ChainCase exactIds inp o res :=
    fun execution hclearE hbridgeE r b hr hb hex hscope key hk hkey packed c q candidate run loops i edge area hpack hsel hrun hloops hpart hedge hdeclE hfind =>
      hchainWfull execution hwf hfp hclearE hbridgeE hr hb hex hscope hk hkey area hpack hsel hrun hloops hpart hedge hdeclE hfind
  have hloop : X6_LoopCase exactIds inp o res :=
    fun execution hclearE hbridgeE hsepE r b hr hb hex hscope key hk hkey packed c q candidate run loops i edge area hpack hsel hrun hloops hpart hedge hdeclE loop hfind =>
      hloopWfull execution hwf hfp hclearE hbridgeE hsepE hr hb hex hscope hk hkey area hpack hsel hrun hloops hpart hedge hdeclE hfind
  exact x6_c6 hchain hloop hclear hbridge hsep hlay

end PipelineImpl
end Layered
end Elegant

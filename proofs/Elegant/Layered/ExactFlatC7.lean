import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.LabelsC7
import Elegant.Layered.LabelsC7Bridges
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.PartSeparation
import Elegant.Layered.LabelsClearance
import Elegant.Layered.RunLocalLabelClearanceProof
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.RankSiblingDisjoint
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact flat C7: `FlatC7B (layoutX exactIds)`.

Replays `layout_c7` over `SceneExecutionX`. The plain seams quantify over
plain `SceneExecution`, which a successful `layoutX` does not produce, so the
X proof rebuilds each seam over the exact execution. The handed-over plain
hypotheses are vacuous for exact results and stay unused; the X leaves below
mirror the plain proof's documented residuals, one pipeline stage each. -/

/-- X loop-branch residual: mirror of `RunLocalLoopSeparation` over
`componentRunX`. One placement branch only. -/
def X_RunLocalLoopSeparation (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    labelEnvelope execution.params cg run execution.measured k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    Elegant.Layered.LoopFootprintSeparation execution.params cg run
      execution.measured k e env v

/-- X forward-branch residual: mirror of `RunLocalForwardSeparation` over
`componentRunX`. One placement branch only. -/
def X_RunLocalForwardSeparation (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat) (r : Rect),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail ≠ e.head →
    e.reversed = false →
    labelEnvelope execution.params cg run execution.measured k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    r ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) →
    Elegant.Layered.RectAxisSeparated r (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- X reversed-branch residual: mirror of `RunLocalReversedSeparation` over
`componentRunX`. One placement branch only. -/
def X_RunLocalReversedSeparation (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat) (r : Rect),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail ≠ e.head →
    e.reversed = true →
    labelEnvelope execution.params cg run execution.measured k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    r ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) →
    (RouteImpl.boxRect run.proper run.xs run.ys v).x +
      (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤ r.x

/-- X placement residual: mirror of `RouteLabelsPlaced` over `componentRunX`.
About the placement phase only. -/
def X_RouteLabelsPlaced : Prop :=
  ∀ (P : Params) (exact : List Nat) (cg : Graph) (labels : List MeasuredLabel)
    (orderOptions : OrderOptions) (run : Run) (l : MeasuredLabel)
    (edge : Nat) (e : Edge),
    componentRunX P exact cg labels orderOptions = .ok run →
    cg.edges[edge]? = some e → l ∈ routeLabels labels e.decl →
    ∃ rect, (l.index, rect) ∈ placedLabels P cg run labels

/-- X run-phase id residual: mirror of `ExclusiveRunNodeDecl` over
`componentRunX`. No geometry. -/
def X_ExclusiveRunNodeDecl (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (v key : Nat) (source : ModelBox),
      comp[v]? = some key →
      inp.boxes[key]? = some source →
      RouteImpl.nodeDecl run.proper v = key

/-- X measured-graph id residual: mirror of `ExclusiveKeyOutsideCgPaths` over
the exact execution graph. -/
def X_ExclusiveKeyOutsideCgPaths (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (v key : Nat) (source : ModelBox)
    (execution : SceneExecutionX exactIds inp o res),
    comp ∈ components execution.graph →
    comp[v]? = some key →
    inp.boxes[key]? = some source → source.exclusive = true →
    ∀ (u : Nat) (nd : Node),
      (componentCandidate execution.graph comp candidate).nodes[u]? = some nd →
      key ∉ nd.clusterPath

/-- X caption label: mirror of `captionLabel` over the exact execution. -/
def X_captionLabel (exactIds : List String) {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (ownerIndex : Nat) (source : ModelLabel) (lines : List String) : Label :=
  ⟨source.id, source.owner,
    sceneCaptionRect execution.params inp o execution.lines
      execution.packedAcc ownerIndex source.owner, lines⟩

/-- X caption residual: mirror of `CaptionScopeClearance` over the exact
execution. The single geometric caption fact. -/
def X_CaptionScopeClearance (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (index ownerIndex : Nat) (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (X_captionLabel exactIds execution ownerIndex source lines) →
    ¬ (sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- X run-local clearance: mirror of `RunLocalLabelClearance` over the exact
execution. -/
def X_RunLocalLabelClearance (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (edge decl v : Nat)
    (e : Edge) (l : MeasuredLabel),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    (cg.edges[edge]?) = some e →
    (cg.edges[edge]?).map (·.decl) = some decl →
    l ∈ routeLabels execution.measured decl →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    ¬ (Elegant.Layered.routeLabelRect execution.params cg run execution.measured l).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- X label bridge: mirror of `LabelBelongsToRun` over the exact execution,
with `placeComponentExact`/`placeBoundsX` transports. -/
def X_LabelBelongsToRun (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel) (measured : MeasuredLabel),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = some measured →
    ∃ (comp : List Nat) (candidate : Nat) (run : Run)
      (orderOptions : OrderOptions) (cg : Graph) (edge decl : Nat)
      (px py m h : Int) (d : Direction)
      (packed : Pack.State) (c : Nat) (labelPart : List Nat × Part)
      (shelfc : Rect) (loops : List (Nat × LoopPlacement)) (area : Int)
      (rl : Nat × Rect),
      comp ∈ components execution.graph ∧
      cg = componentCandidate execution.graph comp candidate ∧
      componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
        orderOptions = .ok run ∧
      orderOptions = candidateOrder candidate ∧
      (cg.edges[edge]?).map (·.decl) = some decl ∧
      measured ∈ routeLabels execution.measured decl ∧
      l.rect = shiftRect m m
        (orientRect d h (shiftRect px py
          (Elegant.Layered.routeLabelRect execution.params cg run execution.measured measured))) ∧
      m = execution.params.canvasMargin ∧
      h = execution.packedAcc.canvasH ∧
      d = o.direction ∧
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (execution.componentsAcc.parts.zip packed.boxes)[c]? = some (labelPart, shelfc) ∧
      labelPart.1 = comp ∧
      labelPart.2 = { placeComponentExact execution.params cg run 0
        execution.measured loops with area := area } ∧
      px = shelfc.x + (0 - (placeBoundsX execution.params cg run execution.measured
        loops).minX) ∧
      py = shelfc.y + (-(placeBoundsX execution.params cg run execution.measured
        loops).minY) ∧
      rl ∈ labelPart.2.labels ∧
      l.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect shelfc.x shelfc.y rl.2))

/-- X box bridge: mirror of `ExclusiveBoxInLabelRun` over the exact execution. -/
def X_ExclusiveBoxInLabelRun (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel) (measured : MeasuredLabel)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (cg : Graph) (edge decl : Nat)
    (e : Edge)
    (packed : Pack.State) (c : Nat) (labelPart : List Nat × Part)
    (shelfc : Rect) (loops : List (Nat × LoopPlacement)) (area : Int)
    (rl : Nat × Rect),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = some measured →
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      (candidateOrder candidate) = .ok run →
    (cg.edges[edge]?) = some e →
    (cg.edges[edge]?).map (·.decl) = some decl →
    measured ∈ routeLabels execution.measured decl →
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some (labelPart, shelfc) →
    labelPart.1 = comp →
    labelPart.2 = { placeComponentExact execution.params cg run 0
      execution.measured loops with area := area } →
    rl ∈ labelPart.2.labels →
    l.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect shelfc.x shelfc.y rl.2)) →
    ∀ (b : Box),
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    (∃ v : Nat,
      v < run.proper.nodes.length ∧
      RouteImpl.IsReal run.proper v ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] ∧
      b.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect
            (shelfc.x + (0 - (placeBoundsX execution.params cg run
              execution.measured loops).minX))
            (shelfc.y + (-(placeBoundsX execution.params cg run
              execution.measured loops).minY))
            (RouteImpl.boxRect run.proper run.xs run.ys v)))) ∨
    (∃ (packed' : Pack.State) (c d' : Nat)
      (labelPart' boxPart : List Nat × Part)
      (shelfc' shelfd : Rect) (rl' : Nat × Rect) (r : Rect),
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed' ∧
      execution.componentsAcc.parts[c]? = some labelPart' ∧
      packed'.boxes[c]? = some shelfc' ∧
      execution.componentsAcc.parts[d']? = some boxPart ∧
      packed'.boxes[d']? = some shelfd ∧
      c ≠ d' ∧
      rl' ∈ labelPart'.2.labels ∧
      r ∈ boxPart.2.rects ∧
      l.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect shelfc'.x shelfc'.y rl'.2)) ∧
      b.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect shelfd.x shelfd.y r)))

/-- X dump bridge: mirror of `RouteLabelDumpBridges` over the exact execution. -/
def X_RouteLabelDumpBridges (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel) (measured : MeasuredLabel) (b : Box),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = some measured →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    (∃ (comp : List Nat) (candidate : Nat) (run : Run)
      (orderOptions : OrderOptions) (cg : Graph) (edge decl v : Nat)
      (e : Edge) (px py m h : Int) (d : Direction),
      comp ∈ components execution.graph ∧
      cg = componentCandidate execution.graph comp candidate ∧
      componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
        orderOptions = .ok run ∧
      (cg.edges[edge]?) = some e ∧
      (cg.edges[edge]?).map (·.decl) = some decl ∧
      measured ∈ routeLabels execution.measured decl ∧
      v < run.proper.nodes.length ∧
      RouteImpl.IsReal run.proper v ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] ∧
      l.rect = shiftRect m m
        (orientRect d h (shiftRect px py
          (Elegant.Layered.routeLabelRect execution.params cg run execution.measured measured))) ∧
      b.rect = shiftRect m m
        (orientRect d h (shiftRect px py
          (RouteImpl.boxRect run.proper run.xs run.ys v)))) ∨
    (∃ (packed : Pack.State) (c d : Nat)
      (labelPart boxPart : List Nat × Part)
      (shelfc shelfd : Rect) (rl : Nat × Rect) (r : Rect),
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      execution.componentsAcc.parts[c]? = some labelPart ∧
      packed.boxes[c]? = some shelfc ∧
      execution.componentsAcc.parts[d]? = some boxPart ∧
      packed.boxes[d]? = some shelfd ∧
      c ≠ d ∧
      rl ∈ labelPart.2.labels ∧
      r ∈ boxPart.2.rects ∧
      l.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect shelfc.x shelfc.y rl.2)) ∧
      b.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect shelfd.x shelfd.y r)))

abbrev X_LabelRunsClearExclusiveBoxes (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  X_RunLocalLabelClearance exactIds inp o res ∧ X_RouteLabelDumpBridges exactIds inp o res

/-- X packing seam: mirror of `PartsSeparated` over the exact execution. -/
def X_PartsSeparated (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (packed : Pack.State)
    (c : Nat) (part : List Nat × Part) (shelf : Rect),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    execution.componentsAcc.parts[c]? = some part →
    packed.boxes[c]? = some shelf →
    (∀ l ∈ part.2.labels,
        Rect.Contained
          (shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect shelf.x shelf.y ⟨0, 0, shelf.w, shelf.h⟩)))
          (shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect shelf.x shelf.y l.2)))) ∧
    (∀ r ∈ part.2.rects,
        Rect.Contained
          (shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect shelf.x shelf.y ⟨0, 0, shelf.w, shelf.h⟩)))
          (shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect shelf.x shelf.y r))))

/-- X caption seam: mirror of `SceneCaptionBoxContainment` over the exact
execution. -/
def X_SceneCaptionBoxContainment (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = none →
    (∃ ownerIndex : Nat, inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex) →
    ∀ b : Box, b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
      b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
      ¬ l.rect.meetsInterior b.rect

/-- A pair selected from the packed zip projects to the shelf selected from
the packed boxes at the same index. -/
private theorem X_zip_getElem?_right {α β : Type} {xs : List α} {ys : List β}
    {c : Nat} {x : α} {y : β} (h : (xs.zip ys)[c]? = some (x, y)) :
    ys[c]? = some y :=
  (List.getElem?_zip_eq_some.mp h).2

/-- A candidate graph has exactly the component's nodes. -/
private theorem X_candidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- `mapM` preserves length on success. -/
private theorem X_mapM_ok_len {err α β : Type} (f : α → Except err β) :
    ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    change Except.ok [] = Except.ok out at h
    injection h with hout
    subst out
    rfl
  | cons a l ih =>
    intro out h
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error err =>
      rw [ha] at h
      change Except.error err = Except.ok out at h
      cases h
    | ok b =>
      cases hxs : l.mapM f with
      | error err =>
        rw [ha, hxs] at h
        change Except.error err = Except.ok out at h
        cases h
      | ok xs =>
        rw [ha, hxs] at h
        change Except.ok (b :: xs) = Except.ok out at h
        injection h with hout
        subst out
        exact congrArg Nat.succ (ih xs hxs)

/-- The exact execution covers every input box with a graph node. -/
private theorem X_lines_len {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length := X_mapM_ok_len _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- X label source split: mirror of `SceneExecution.label_source`; the proof
uses only the shared `sceneOf` equation. -/
theorem X_label_source_split {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {label : SceneLabel}
    (hl : label ∈ res.scene.labels) :
    ∃ (source : ModelLabel) (index : Nat),
      inp.labels[index]? = some source ∧
      inp.boxes.any (fun box => box.id == source.owner && box.exclusive) = false ∧
      label.id = source.id ∧ label.owner = source.owner ∧
      ((∃ measured,
          execution.measured.find? (fun item => item.index == index) = some measured) ∨
        (execution.measured.find? (fun item => item.index == index) = none ∧
          ∃ ownerIndex, inp.boxes.findIdx?
            (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex)) := by
  rw [execution.scene_eq] at hl
  obtain ⟨q, hq, hemitted⟩ := List.mem_filterMap.mp hl
  have hsource := List.mem_zipIdx_iff_getElem?.mp hq
  cases hexclusive : inp.boxes.any
      (fun box => box.id == q.1.owner && box.exclusive) with
  | true => simp only [hexclusive, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hexclusive, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hm : execution.measured.find? (fun item => item.index == q.2) with
    | some measured =>
      simp only [hm, Option.some.injEq] at hemitted
      subst label
      exact ⟨q.1, q.2, hsource, hexclusive, rfl, rfl, Or.inl ⟨measured, hm⟩⟩
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx?
          (fun box => box.id == q.1.owner && !box.exclusive) with
      | none => simp only [ho] at hemitted; cases hemitted
      | some ownerIndex =>
        simp only [ho, Option.some.injEq] at hemitted
        subst label
        exact ⟨q.1, q.2, hsource, hexclusive, rfl, rfl,
          Or.inr ⟨hm, ownerIndex, ho⟩⟩

/-- The placement bounds of `placeComponentExact`: the `boundsOf` argument
the exact placement itself builds. -/
private theorem X_placeComponentExact_rects_get {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} {cursor : Int}
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- The labels an exact placed component stores are the placed pairs shifted
by the negated placement bounds (cursor `0`). -/
theorem X_placeComponentExact_labels_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} :
    (placeComponentExact P cg run 0 labels loops).labels =
      (placedLabels P cg run labels).map (fun q =>
        (q.1, shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
          (-(placeBoundsX P cg run labels loops).minY) q.2)) := by
  unfold placeComponentExact placeBoundsX
  rfl

/-- One exact `placePart` appends exactly one part and folds its label pairs
into the accumulator. -/
theorem X_placePart_labels_step {comp : List Nat} {cg : Graph} {run : Run}
    {P : Params} {acc acc' : Acc} {labels : List MeasuredLabel}
    (h : placePart comp cg run P acc labels (@placeComponentExact) true = .ok acc') :
    ∃ part : Part,
      acc'.parts = acc.parts ++ [(comp, part)] ∧
      acc'.labels = part.labels.foldl (fun a q => a.set! q.1 q.2) acc.labels := by
  unfold placePart at h
  obtain ⟨loops, hloops, hres⟩ := bind_ok h
  dsimp only at hres
  split at hres
  · simp at hres
  · have hok := Except.ok.inj hres
    apply Exists.intro
    exact ⟨Eq.symm (congrArg Acc.parts hok), Eq.symm (congrArg Acc.labels hok)⟩

/-- One exact `layoutComponentX` step appends exactly one part and folds its
label pairs into the accumulator. -/
theorem X_layoutComponent_labels_step {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponentX P exactIds inp o g acc comp measured = .ok acc') :
    ∃ (part : Part) (area : Int),
      acc'.labels = part.labels.foldl (fun a q => a.set! q.1 q.2) acc.labels ∧
      acc'.parts = acc.parts ++ [(comp, { part with area := area })] ∧
      acc.labels.size = acc'.labels.size := by
  have hsizes := (layoutComponentX_sizes h).2.2
  unfold layoutComponentX at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨result, hres, h⟩ := bind_ok h
  obtain ⟨part, hparts, hlab⟩ := X_placePart_labels_step hres
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hdrop : result.parts.drop acc.parts.length = [(comp, part)] := by
    rw [hparts]; simp
  have hpp := (congrArg Acc.parts he).symm
  dsimp only at hpp
  rw [hdrop, List.map_cons, List.map_nil] at hpp
  have hll := (congrArg Acc.labels he).symm
  dsimp only at hll
  exact ⟨part, _, hll.trans hlab, hpp, hsizes⟩

/-- Exact fold structure: the output parts are the start parts plus one entry
per component. -/
private theorem X_fold_parts_structure {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel} :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM
        (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start =
        .ok out →
      ∃ parts, out.parts = start.parts ++ parts ∧ parts.map (·.1) = comps := by
  intro comps
  induction comps with
  | nil =>
    intro start out h
    rw [List.foldlM_nil] at h
    have houtEq : start = out := Except.ok.inj h
    refine ⟨[], ?_, rfl⟩
    rw [← houtEq, List.append_nil]
  | cons comp comps ih =>
    intro start out h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok h
    obtain ⟨part0, area0, _, hmidParts, _⟩ := X_layoutComponent_labels_step hmid
    obtain ⟨parts, hout, hmap⟩ := ih mid out hrest
    refine ⟨(comp, { part0 with area := area0 }) :: parts, ?_, ?_⟩
    · rw [hout, hmidParts, List.append_assoc, List.singleton_append]
    · simp only [List.map_cons, hmap]

/-- The exact component fold preserves the label array size. -/
theorem X_components_fold_labels_size {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel} :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM
        (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start =
        .ok out → out.labels.size = start.labels.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok h
    rw [X_components_fold_labels_size comps mid out hrest]
    exact (layoutComponentX_sizes hmid).2.2.symm

/-- If no exact part of the fold output carries a key, the fold leaves that
entry at its starting value. -/
theorem X_fold_labels_getD_of_no_carry {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel} :
    ∀ (comps : List (List Nat)) (start out : Acc) (i : Nat),
      comps.foldlM
        (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start =
        .ok out →
      (∀ p ∈ out.parts, ∀ r : Rect, (i, r) ∉ p.2.labels) →
      out.labels.getD i default = start.labels.getD i default := by
  intro comps
  induction comps with
  | nil =>
    intro start out i h _
    have he : start = out := Except.ok.inj h
    rw [he]
  | cons comp comps ih =>
    intro start out i h hno
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok h
    obtain ⟨part0, area0, hmidLabels, hmidParts, _⟩ := X_layoutComponent_labels_step hmid
    obtain ⟨appended', houtparts', _⟩ := X_fold_parts_structure comps mid out hrest
    have hpartmem : (comp, { part0 with area := area0 }) ∈ out.parts := by
      rw [houtparts', hmidParts]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr List.mem_cons_self)))
    rw [ih mid out i hrest hno, hmidLabels,
      labels_set_foldl_getD_ne part0.labels start.labels i
        (fun p hp he => hno (comp, { part0 with area := area0 }) hpartmem p.2
          (by rw [← he]; exact hp))]

/-- Exact executed parts carry their component and exact run. -/
theorem X_execution_part_run {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {part : List Nat × Part}
    (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ (index : Nat) (run : Run) (loops : List (Nat × LoopPlacement)) (area : Int),
      part.1 ∈ components execution.graph ∧
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph part.1 index) execution.measured
        (candidateOrder index) = .ok run ∧
      part.2 = { placeComponentExact execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area } := by
  obtain ⟨hmap, _⟩ := actual_components_parts_geometryX (by rfl) execution.components_eq
  obtain ⟨index, run, loops, area, hrun, _, heq, _, _, _, _⟩ :=
    execution.actual_component_sizing (exactBorder2Unchanged_discharge execution) hpart
  refine ⟨index, run, loops, area, ?_, hrun, heq⟩
  rw [← hmap]
  exact List.mem_map_of_mem hpart

/-- X scene label rect: mirror of `scene_label_rect`; the proof uses only the
shared `sceneOf` equation and well-formedness. -/
theorem X_scene_label_rect {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {l : SceneLabel} {index : Nat}
    {source : ModelLabel} {measured : MeasuredLabel}
    (hwf : WellFormed (inputModel inp o))
    (hl : l ∈ res.scene.labels) (hin : inp.labels[index]? = some source)
    (hid : l.id = source.id)
    (hmeasured : execution.measured.find? (fun label => label.index == index) = some measured) :
    l.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.labels.getD measured.index default)) := by
  have hids : (inp.labels.map (·.id)).Nodup := Elegant.Layered.labelIds_nodup hwf
  have hindex : index < inp.labels.length := (List.getElem?_eq_some_iff.mp hin).1
  rw [execution.scene_eq] at hl
  obtain ⟨q, hq, hemitted⟩ := List.mem_filterMap.mp hl
  obtain ⟨q1, q2⟩ := q
  have hp : inp.labels[q2]? = some q1 := List.mem_zipIdx_iff_getElem?.mp hq
  have hq2l : q2 < inp.labels.length := (List.getElem?_eq_some_iff.mp hp).1
  rw [List.getElem?_eq_getElem hq2l] at hp
  rw [List.getElem?_eq_getElem hindex] at hin
  have hp : inp.labels[q2] = q1 := Option.some.inj hp
  have hin : inp.labels[index] = source := Option.some.inj hin
  have hkey : l.id = q1.id → q2 = index := by
    intro lid
    refine hids.eq_of_getElem_eq
      (by simpa only [List.length_map] using hq2l)
      (by simpa only [List.length_map] using hindex) ?_
    rw [List.getElem_map, List.getElem_map, hp, hin]
    exact lid.symm.trans hid
  dsimp only at hemitted
  split at hemitted
  · simp at hemitted
  · split at hemitted
    · next label hfind =>
      have lid : l.id = q1.id :=
        (congrArg (fun s => s.toLabel.id) (Option.some.inj hemitted)).symm
      have hq2 : q2 = index := hkey lid
      rw [hq2] at hfind
      have hlm : label = measured :=
        Option.some.inj (hfind.symm.trans hmeasured)
      have hr := (congrArg (fun s => s.toLabel.rect) (Option.some.inj hemitted)).symm
      dsimp only at hr
      rw [hlm] at hr
      exact hr
    · next hfind =>
      split at hemitted
      · simp at hemitted
      · next idx hidx =>
        have lid : l.id = q1.id :=
          (congrArg (fun s => s.toLabel.id) (Option.some.inj hemitted)).symm
        have hq2 : q2 = index := hkey lid
        rw [hq2] at hfind
        rw [hmeasured] at hfind
        cases hfind

/-- X run-local label clearance holds modulo the three X branch residuals. -/
theorem X_runLocalLabelClearance_holds {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (hloop : X_RunLocalLoopSeparation exactIds)
    (hfwd : X_RunLocalForwardSeparation exactIds)
    (hrev : X_RunLocalReversedSeparation exactIds) :
    X_RunLocalLabelClearance exactIds inp o res := by
  intro execution comp candidate run orderOptions cg edge decl v e l
    hcomp hcg hrun he hedge hl hlen hreal hscope₀ hscope₁
  have hlab := execution.measured_nonneg
  have hslot := componentRunX_slot_nonneg hrun
  have hnd : (execution.measured.map (·.index)).Nodup :=
    measureLabels_index_nodup execution.measured_eq
  by_cases hex : ∃ rect, (l.index, rect) ∈
      placedLabels execution.params cg run execution.measured
  · obtain ⟨rect, hmem⟩ := hex
    have hroute : Elegant.Layered.routeLabelRect execution.params cg run
        execution.measured l = rect :=
      routeLabelRect_of_mem hnd hmem
    rw [hroute]
    obtain ⟨ml, edge', e', env, rect', hmlmem, hmlidx, hfind, he', henv,
        hfindstk, hreq⟩ := placedLabels_pair_inv hnd hmem
    subst hreq
    have hml : ml = l :=
      measured_eq_of_index_eq execution.measured hnd ml l hmlmem
        (Elegant.Layered.mem_measured_of_mem_routeLabels hl) hmlidx
    subst hml
    have hmemstk := List.mem_of_find?_eq_some hfindstk
    have hr : rect ∈ Labels.stackRects env.x env.y cg.slot
        ((routeLabels execution.measured e'.decl).map fun q => (q.width, q.height)) :=
      (List.of_mem_zip hmemstk).2
    have hedecl : e.decl = decl := by
      rw [he] at hedge
      simpa using hedge
    have hedge' : e'.decl = decl := by
      obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
      have hgg : cg.edges[edge'] = e' := (List.getElem?_eq_some_iff.mp he').2
      have hpred : e'.decl = ml.edge :=
        beq_iff_eq.mp (by have hmatch' := hmatch; rw [hgg] at hmatch'; simpa using hmatch')
      have hll : ml.edge = decl := by
        have hp := (List.mem_filter.mp hl).2
        simpa using hp
      exact hpred.trans hll
    have hnd_decl : (cg.edges.map (·.decl)).Nodup := by
      rw [hcg]
      exact componentCandidate_decls_nodup execution.graph comp candidate
        (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
    have hEE : e = e' :=
      nodup_map_eq_of_mem hnd_decl (List.mem_of_getElem? he)
        (List.mem_of_getElem? he') (hedecl.trans hedge'.symm)
    rw [hEE] at hscope₀ hscope₁
    have hsep_loop : e'.tail = e'.head →
        Elegant.Layered.LoopFootprintSeparation execution.params cg run
          execution.measured edge' e' env v :=
      fun heq => hloop inp o res execution comp candidate run orderOptions cg edge' e' env v
        hcomp hcg hrun he' heq henv hlen hreal hscope₀ hscope₁
    have hsep_forward : e'.tail ≠ e'.head → e'.reversed = false →
        Elegant.Layered.RectAxisSeparated rect
          (RouteImpl.boxRect run.proper run.xs run.ys v) :=
      fun hne hrev' => hfwd inp o res execution comp candidate run orderOptions cg edge' e' env v rect
        hcomp hcg hrun he' hne hrev' henv hlen hreal hscope₀ hscope₁ hr
    have hsep_reversed : e'.tail ≠ e'.head → e'.reversed = true →
        (RouteImpl.boxRect run.proper run.xs run.ys v).x +
          (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤ rect.x :=
      fun hne hrev' => hrev inp o res execution comp candidate run orderOptions cg edge' e' env v rect
        hcomp hcg hrun he' hne hrev' henv hlen hreal hscope₀ hscope₁ hr
    exact Elegant.Layered.runLocalLabelClearance he' henv hslot hlab hr
      hsep_loop hsep_forward hsep_reversed
  · have hfilter : (placedLabels execution.params cg run execution.measured).filter
        (fun q => q.1 == l.index) = [] := by
      rw [List.filter_eq_nil_iff]
      intro qq hqq hcond
      simp only [beq_iff_eq] at hcond
      exact hex ⟨qq.2, by rw [← hcond]; exact hqq⟩
    have hroute0 : Elegant.Layered.routeLabelRect execution.params cg run
        execution.measured l = ⟨0, 0, 0, 0⟩ := by
      unfold Elegant.Layered.routeLabelRect
      rw [hfilter]
      rfl
    rw [hroute0]
    exact emptyRect_meets_none

/-- X label bridge: mirror of `labelBelongsToRun` over the exact execution. -/
theorem X_labelBelongsToRun {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hroute_placed : X_RouteLabelsPlaced) :
    X_LabelBelongsToRun exactIds inp o res := by
  intro execution l index source measured hl hin hid hmeasured
  have hfindmem : measured ∈ execution.measured := List.mem_of_find?_eq_some hmeasured
  have hidxeq : measured.index = index := by
    simpa using List.find?_some hmeasured
  obtain ⟨hidxlt, hedgrt⟩ := measureLabels_source execution.measured_eq hfindmem
  have hnd : (execution.measured.map (·.index)).Nodup :=
    measureLabels_index_nodup execution.measured_eq
  have hscene := X_scene_label_rect execution hwf hl hin hid hmeasured
  have hpk := execution.packed_eq
  unfold packAcc at hpk
  obtain ⟨packedSt, hpack, hfold⟩ := bind_ok hpk
  have hpackedAcc : execution.packedAcc =
      (execution.componentsAcc.parts.zip packedSt.boxes).foldl packStep
        ({ execution.componentsAcc with canvasW := packedSt.width, canvasH := packedSt.height, titles := [] } : Acc) := (Except.ok.inj hfold).symm
  have hsizeComp : execution.componentsAcc.labels.size = inp.labels.length := by
    have h := X_components_fold_labels_size (components execution.graph) _ _
      execution.components_eq
    rw [h]
    simp
  have hprov := packFold_labels_provenance
    (execution.componentsAcc.parts.zip packedSt.boxes)
    ({ execution.componentsAcc with canvasW := packedSt.width, canvasH := packedSt.height, titles := [] } : Acc)
    measured.index (execution.packedAcc.labels.getD measured.index default)
    (by change measured.index < execution.componentsAcc.labels.size; rw [hsizeComp]; exact hidxlt)
    (by rw [hpackedAcc])
  rcases hprov with ⟨q, hqzip, r0, hmemlabels, hrpacked⟩ | ⟨hnocarryzip, hstartval⟩
  · have hqpart : q.1 ∈ execution.componentsAcc.parts := (List.of_mem_zip hqzip).1
    obtain ⟨cand, run, loops, area, hcomp, hrun, hpartdef⟩ :=
      X_execution_part_run execution hqpart
    have hplacedmem : (measured.index, r0) ∈
        (placeComponentExact execution.params (componentCandidate execution.graph q.1.1 cand)
          run 0 execution.measured loops).labels := by
      rw [hpartdef] at hmemlabels
      exact hmemlabels
    rw [X_placeComponentExact_labels_eq] at hplacedmem
    obtain ⟨pair, hpair, hpairEq⟩ := List.mem_map.mp hplacedmem
    have hpair1 : pair.1 = measured.index := congrArg Prod.fst hpairEq
    have hpair2 : shiftRect (0 - (placeBoundsX execution.params
          (componentCandidate execution.graph q.1.1 cand) run execution.measured
          loops).minX)
        (-(placeBoundsX execution.params
          (componentCandidate execution.graph q.1.1 cand) run execution.measured
          loops).minY) pair.2 = r0 := congrArg Prod.snd hpairEq
    have hplaced : (measured.index, pair.2) ∈
        placedLabels execution.params (componentCandidate execution.graph q.1.1 cand)
          run execution.measured := by
      have h : (pair.1, pair.2) ∈ placedLabels execution.params
          (componentCandidate execution.graph q.1.1 cand) run execution.measured := hpair
      rw [hpair1] at h
      exact h
    obtain ⟨ml, edge, e, env, rect, hmlmem, hmlidx, hfindex, hgetedge, henv,
      hfindstack, hreq⟩ := placedLabels_pair_inv hnd hplaced
    have hml : ml = measured :=
      measured_eq_of_index_eq execution.measured hnd ml measured hmlmem hfindmem
        (by rw [hmlidx])
    subst hml
    have hroutemem : ml ∈ routeLabels execution.measured e.decl :=
      (List.of_mem_zip (List.mem_of_find?_eq_some hfindstack)).1
    have hrouteRect : Elegant.Layered.routeLabelRect execution.params
        (componentCandidate execution.graph q.1.1 cand) run execution.measured ml =
        pair.2 := routeLabelRect_of_mem hnd hplaced
    obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hqzip
    have hrect1 : l.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect (q.2.x + (0 - (placeBoundsX execution.params
            (componentCandidate execution.graph q.1.1 cand) run execution.measured
            loops).minX))
            (q.2.y + (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 cand) run execution.measured
              loops).minY))
            (Elegant.Layered.routeLabelRect execution.params
              (componentCandidate execution.graph q.1.1 cand) run execution.measured
              ml))) := by
      rw [hscene, hrouteRect, hrpacked, ← hpair2, shiftRect_shiftRect]
    have hlrect2 : l.rect = shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y r0)) := by
      rw [hscene, hrpacked]
    refine ⟨q.1.1, cand, run, candidateOrder cand,
      componentCandidate execution.graph q.1.1 cand, edge, e.decl,
      q.2.x + (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 cand) run execution.measured
        loops).minX),
      q.2.y + (-(placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 cand) run execution.measured
        loops).minY),
      execution.params.canvasMargin, execution.packedAcc.canvasH, o.direction,
      packedSt, c, q.1, q.2, loops, area, (ml.index, r0),
      hcomp, rfl, hrun, rfl, by simp [hgetedge], hroutemem, hrect1,
      rfl, rfl, rfl, hpack, hc, rfl, hpartdef, rfl, rfl, hmemlabels, hlrect2⟩
  · have hnocarry : ∀ part ∈ execution.componentsAcc.parts, ∀ r : Rect,
        (measured.index, r) ∉ part.2.labels := by
      intro part hpart r hmem
      obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpart
      have hclen : c < execution.componentsAcc.parts.length :=
        (List.getElem?_eq_some_iff.mp hc).1
      have hboxlen : packedSt.boxes.length = execution.componentsAcc.parts.length := by
        rw [Pack.pack_count hpack, List.length_map]
      have hcbox : packedSt.boxes[c]? = some packedSt.boxes[c] :=
        List.getElem?_eq_getElem (by rw [hboxlen]; exact hclen)
      have hpair : (execution.componentsAcc.parts.zip packedSt.boxes)[c]? =
          some (part, packedSt.boxes[c]) := List.getElem?_zip_eq_some.mpr ⟨hc, hcbox⟩
      exact hnocarryzip (part, packedSt.boxes[c]) (List.mem_of_getElem? hpair) r hmem
    have hcompdef : execution.componentsAcc.labels.getD measured.index default = default := by
      rw [X_fold_labels_getD_of_no_carry (components execution.graph) _ _ _
        execution.components_eq hnocarry]
      change (Array.replicate inp.labels.length default).getD measured.index default = default
      unfold Array.getD
      split <;> simp
    have hpackeddef : execution.packedAcc.labels.getD measured.index default = default := by
      rw [← hstartval]
      exact hcompdef
    obtain ⟨ge, hge, hgedcl⟩ := measuredGraph_edge_decl execution.graph0_eq hedgrt
    have hlines : execution.lines.length = inp.boxes.length := X_lines_len execution
    have hbd0 := measuredGraph_edges_bounded execution.graph0_eq hlines ge hge
    have hlen : execution.graph.nodes.length = execution.graph0.nodes.length :=
      exactGraph_length execution.graph_eq
    have htailbound : ge.tail < execution.graph.nodes.length := by omega
    obtain ⟨comp, hcomp, htailmem⟩ :=
      components_cover htailbound (sceneExecutionX_edges_bounded execution)
    have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩ : Acc).parts = [] := rfl
    obtain ⟨hm, _⟩ := actual_components_parts_geometryX (by rfl) execution.components_eq
    have hcompmap : comp ∈ execution.componentsAcc.parts.map (·.1) := by
      rw [hm]; exact hcomp
    obtain ⟨part, hpartmem, hpartcomp⟩ := List.mem_map.mp hcompmap
    obtain ⟨cand, run, loops, area, _, hrun, hpartdef⟩ :=
      X_execution_part_run execution hpartmem
    have htailmem' : ge.tail ∈ part.1 := hpartcomp ▸ htailmem
    have htailcontains : part.1.contains ge.tail = true := by simpa using htailmem'
    have hge' : ge ∈ execution.graph.edges := by
      have heq := exactGraph_edges execution.graph_eq
      rw [heq]
      exact hge
    obtain ⟨ce, hce, hcedcl⟩ := componentGraph_decl_edge hge' htailcontains
    have hdeclmem : measured.edge ∈
        (componentGraph execution.graph part.1).edges.map (·.decl) :=
      List.mem_map.mpr ⟨ce, hce, hcedcl.trans hgedcl⟩
    obtain ⟨edge, e, hgetedge, hedef⟩ :=
      componentCandidate_decl_edge (index := cand) hdeclmem
    have hroutemem : measured ∈ routeLabels execution.measured e.decl :=
      List.mem_filter.mpr ⟨hfindmem, by simp [hedef]⟩
    have hnoplaced : ∀ qq ∈ placedLabels execution.params
        (componentCandidate execution.graph part.1 cand) run execution.measured,
        qq.1 ≠ measured.index := by
      intro qq hqq hq1
      have hpartqq : (measured.index, shiftRect (0 - (placeBoundsX execution.params
            (componentCandidate execution.graph part.1 cand) run execution.measured
            loops).minX)
          (-(placeBoundsX execution.params
            (componentCandidate execution.graph part.1 cand) run execution.measured
            loops).minY) qq.2) ∈ part.2.labels := by
        rw [hpartdef, X_placeComponentExact_labels_eq]
        exact List.mem_map.mpr ⟨qq, hqq, by rw [hq1]⟩
      exact hnocarry part hpartmem _ hpartqq
    have hroute0 : Elegant.Layered.routeLabelRect execution.params
        (componentCandidate execution.graph part.1 cand) run execution.measured measured =
        ⟨0, 0, 0, 0⟩ := by
      unfold Elegant.Layered.routeLabelRect
      have hfilter : (placedLabels execution.params
          (componentCandidate execution.graph part.1 cand) run execution.measured).filter
          (fun qq => qq.1 == measured.index) = [] := by
        rw [List.filter_eq_nil_iff]
        intro qq hqq hcond
        simp only [beq_iff_eq] at hcond
        exact hnoplaced qq hqq hcond
      rw [hfilter]
      rfl
    obtain ⟨rect, hmem⟩ := hroute_placed execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph part.1 cand) execution.measured
      (candidateOrder cand) run measured edge e hrun hgetedge hroutemem
    exact False.elim (hnoplaced _ hmem rfl)


/-- X run source nodes are real: mirror of `componentRun_source_isReal` over
`componentRunX_spec`, with `sizeProperPortsX_key` in place of the plain sizing
key. -/
theorem X_componentRun_source_isReal {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node) :
    RouteImpl.IsReal run.proper v := by
  obtain ⟨_, normalized, labeled, projected, hn, hl, hc, _, _, hp, hd, _, _, _⟩ :=
    componentRunX_spec hrun
  have hnormalized := normalize_node_record hn hnode
  have hlabeled := addLabelNodes_untouched_node hl hnormalized rfl
  have hsized : Metadata.NodeMetadata labeled (sizeProperPortsX P exact labeled) := by
    apply Metadata.nodeMetadata_of_lookup_maps
    intro index
    have hk := congrArg (Option.map (fun t : Bool × Int × List Nat => t.1))
      (sizeProperPortsX_key P exact labeled index)
    simpa only [Option.map_map, Function.comp_def] using hk
  have htitled : Metadata.NodeMetadata (sizeProperPortsX P exact labeled)
      (titleReservations (sizeProperPortsX P exact labeled)) :=
    Metadata.nodeMetadata_map_append titleF (fun nd => (titleF_keys nd).1) _
      (titleReservations_nodes _)
  have hbordered := Metadata.nodeMetadata_borderExtension
    (OrderImpl.addClusterBorders_metadata (titleReservations (sizeProperPortsX P exact labeled))
      P.clusterBorderW)
  have hcleared : Metadata.NodeMetadata
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)) :=
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

/-- An exclusive source box of a successful exact execution is a border-0 node. -/
private theorem X_exclusive_source_border_zero {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hlinesLen : execution.lines.length = inp.boxes.length)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hex : source.exclusive = true) :
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.border = 0 := by
  have hrole : source.role ≠ .group :=
    wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource) hex
  have hkeyLen : key < execution.lines.length := by
    rw [hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hline : execution.lines[key]? = some execution.lines[key] :=
    List.getElem?_eq_some_iff.mpr ⟨hkeyLen, rfl⟩
  obtain ⟨node0, hnode0, hborder0⟩ :=
    measuredGraph_exclusive_node_border_zero execution.checked
      execution.graph0_eq hline hsource hrole
  obtain ⟨node, hnode, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hnode0
  exact ⟨node, hnode, hborder.trans hborder0⟩

/-- Exact frame entry of a chosen part: the zipped part rect at a component
position is the placement shift of the run frame rect. -/
theorem X_chosen_part_frame_entry {P : Params} {graph : Graph} {component : List Nat}
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)} {part : Part} {area : Int}
    (hpart : part = { placeComponentExact P (componentCandidate graph component candidate)
      run 0 labels loops with area := area })
    {i key : Nat} (hkey : component[i]? = some key) :
    (component.zip part.rects)[i]? = some (key,
      shiftRect (0 - (placeBoundsX P (componentCandidate graph component candidate)
        run labels loops).minX)
        (-(placeBoundsX P (componentCandidate graph component candidate)
          run labels loops).minY)
        (frameRect P (componentCandidate graph component candidate) run i)) := by
  have hilen : i < (componentCandidate graph component candidate).nodes.length := by
    rw [X_candidate_nodes_length]
    exact (List.getElem?_eq_some_iff.mp hkey).1
  rw [hpart]
  refine List.getElem?_zip_eq_some.mpr ⟨hkey, ?_⟩
  exact X_placeComponentExact_rects_get hilen

/-- X box bridge: mirror of `exclusiveBoxInLabelRun` over the exact execution. -/
theorem X_exclusiveBoxInLabelRun {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hdecl : X_ExclusiveRunNodeDecl exactIds)
    (hkey : X_ExclusiveKeyOutsideCgPaths exactIds) :
    X_ExclusiveBoxInLabelRun exactIds inp o res := by
  intro execution l index source measured comp candidate run cg _edge _decl e
    packed c labelPart shelfc loops area rl
    _hlmem _hin _hid _hmeasured hcomp hcg hrun _he _hdeclmap _hmlabel hpacked hselected
    hpart1 hpartdef hrlmem hlrect b hdump hex _hscope
  subst hcg
  have hboxes : b ∈ res.scene.boxes := hdump
  rw [execution.boxes_eq_mapX] at hboxes
  obtain ⟨⟨bsource, key⟩, hq, rfl⟩ := List.mem_map.mp hboxes
  have hsource : inp.boxes[key]? = some bsource :=
    List.mem_zipIdx_iff_getElem?.mp hq
  have hkeylen : key < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeylen
  have hexcl : bsource.exclusive = true := hex
  have hgraphlen : key < execution.graph.nodes.length :=
    sceneExecutionX_graph_len execution hkeylen
  have hgnode : execution.graph.nodes[key]? =
      some (execution.graph.nodes[key]'hgraphlen) := List.getElem?_eq_getElem hgraphlen
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  by_cases hmem : key ∈ labelPart.1
  · obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
    have hcompv : comp[v]? = some key := by
      rw [← hpart1]; exact hv
    have hvlen : v < (componentCandidate execution.graph comp candidate).nodes.length := by
      rw [X_candidate_nodes_length]
      exact (List.getElem?_eq_some_iff.mp hcompv).1
    have hproper : v < run.proper.nodes.length :=
      componentRunX_original_nodes_covered hrun v hvlen
    obtain ⟨gnode', hgnode', hgborder⟩ :=
      X_exclusive_source_border_zero execution hwf (X_lines_len execution) hsource hexcl
    have hcgnode : (componentCandidate execution.graph comp candidate).nodes[v]? =
        some gnode' := candidate_node_of_part_key hcompv hgnode'
    have hreal := X_componentRun_source_isReal hrun hcgnode
    have hnodeDecl : RouteImpl.nodeDecl run.proper v = key :=
      hdecl inp o res execution comp candidate run hcomp hrun v key bsource hcompv hsource
    have hs0 : RouteImpl.nodeDecl run.proper v ∉
        (((componentCandidate execution.graph comp candidate).nodes[e.tail]?).map
          (·.clusterPath)).getD [] := by
      rw [hnodeDecl]
      cases htail : (componentCandidate execution.graph comp candidate).nodes[e.tail]? with
      | none => simp
      | some nd =>
        simp only [Option.getD_some, Option.map_some]
        exact hkey inp o res hwf hframed comp candidate v key bsource execution
          hcomp hcompv hsource hexcl e.tail nd htail
    have hs1 : RouteImpl.nodeDecl run.proper v ∉
        (((componentCandidate execution.graph comp candidate).nodes[e.head]?).map
          (·.clusterPath)).getD [] := by
      rw [hnodeDecl]
      cases hhead : (componentCandidate execution.graph comp candidate).nodes[e.head]? with
      | none => simp
      | some nd =>
        simp only [Option.getD_some, Option.map_some]
        exact hkey inp o res hwf hframed comp candidate v key bsource execution
          hcomp hcompv hsource hexcl e.head nd hhead
    have hentry := X_chosen_part_frame_entry (P := execution.params)
      (graph := execution.graph) (component := labelPart.1) (candidate := candidate)
      (run := run) (labels := execution.measured) (loops := loops)
      (part := labelPart.2) (area := area)
      (hpart := by rw [hpart1]; exact hpartdef) hv
    have hval := actual_components_packed_rect_valueX hempty execution.components_eq
      execution.packed_eq packed hpacked hselected hentry hkeysize default
    have hborder : ((componentCandidate execution.graph comp candidate).nodes.getD v
        default).border ≠ -2 := by
      rw [List.getD_eq_getElem?_getD, hcgnode, Option.getD_some, hgborder]
      omega
    have hframe := plain_frame_eq_boxRect execution.params
      (componentCandidate execution.graph comp candidate) run v hproper hborder
    refine Or.inl ⟨v, hproper, hreal, hs0, hs1, ?_⟩
    have hbrect : (Box.mk bsource.id bsource.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD key default)))
        bsource.parent bsource.exclusive).rect =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD key default)) := rfl
    rw [hbrect, hval, hpart1, hframe, shiftRect_shiftRect]
  · obtain ⟨boxPart, hboxPartmem, entry, hentrymem, hentrykey⟩ :=
      sceneExecutionX_parts_entry execution hkeylen
    have hkeymem : key ∈ boxPart.1 := by
      have hmemzip : (key, entry.2) ∈ boxPart.1.zip boxPart.2.rects := by
        have heq : entry = (key, entry.2) := congrArg (·, entry.2) hentrykey
        rw [heq] at hentrymem
        exact hentrymem
      exact (List.of_mem_zip hmemzip).1
    have hne : boxPart.1 ≠ labelPart.1 := by
      intro hcontra
      rw [hcontra] at hkeymem
      exact hmem hkeymem
    obtain ⟨d', hd'⟩ := List.mem_iff_getElem?.mp hboxPartmem
    have hd'len : d' < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hd').1
    have hboxlen : packed.boxes.length = execution.componentsAcc.parts.length := by
      rw [Pack.pack_count hpacked, List.length_map]
    have hshelf : packed.boxes[d']? = some packed.boxes[d'] :=
      List.getElem?_eq_getElem (by rw [hboxlen]; exact hd'len)
    have hselected' : (execution.componentsAcc.parts.zip packed.boxes)[d']? =
        some (boxPart, packed.boxes[d']) :=
      List.getElem?_zip_eq_some.mpr ⟨hd', hshelf⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hentrymem
    have hentry2 : (boxPart.1.zip boxPart.2.rects)[i]? = some (key, entry.2) := by
      have heq : entry = (key, entry.2) := congrArg (·, entry.2) hentrykey
      rw [heq] at hi
      exact hi
    have hval' := actual_components_packed_rect_valueX hempty execution.components_eq
      execution.packed_eq packed hpacked hselected' hentry2 hkeysize default
    have hcpart : execution.componentsAcc.parts[c]? = some labelPart :=
      zip_getElem?_left hselected
    have hcshelf : packed.boxes[c]? = some shelfc :=
      X_zip_getElem?_right hselected
    have hdpart : execution.componentsAcc.parts[d']? = some boxPart := hd'
    have hdshelf : packed.boxes[d']? = some packed.boxes[d'] := hshelf
    have hc'ne : c ≠ d' := by
      intro heq
      have hqc : execution.componentsAcc.parts[c]? = some boxPart := by
        rw [heq]; exact hdpart
      have hpe : labelPart = boxPart := Option.some.inj (hcpart.symm.trans hqc)
      rw [hpe] at hne
      exact hne rfl
    refine Or.inr ⟨packed, c, d', labelPart, boxPart, shelfc, packed.boxes[d'],
      rl, entry.2, hpacked, hcpart, hcshelf, hdpart, hdshelf, hc'ne, hrlmem,
      (List.of_mem_zip hentrymem).2, hlrect, ?_⟩
    have hbrect : (Box.mk bsource.id bsource.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD key default)))
        bsource.parent bsource.exclusive).rect =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD key default)) := rfl
    rw [hbrect, hval']

/-- X bridge assembly: mirror of `routeLabelDumpBridges`. -/
theorem X_routeLabelDumpBridges {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (hlabel : X_LabelBelongsToRun exactIds inp o res)
    (hbox : X_ExclusiveBoxInLabelRun exactIds inp o res) :
    X_RouteLabelDumpBridges exactIds inp o res := by
  intro execution l index source measured b hlmem hin hleq hmeasured hdump hex hscope
  obtain ⟨comp, candidate, run, orderOptions, cg, edge, decl, px, py, m, hgt, dir,
      packed, c, labelPart, shelfc, loops, area, rl,
      hcomp, hcg, hrun, hord, hedge, hmlabel, hrect,
      hm, hh, hd, hpacked, hselected, hpart1, hpartdef, hpx, hpy, hrlmem, hlrect⟩ :=
    hlabel execution l index source measured hlmem hin hleq hmeasured
  obtain ⟨e, he⟩ : ∃ e, (cg.edges[edge]?) = some e := by
    cases h : cg.edges[edge]? with
    | none => simp [h] at hedge
    | some e => exact ⟨e, rfl⟩
  have hrun' : componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      (candidateOrder candidate) = .ok run := by
    rw [← hord]; exact hrun
  have hrect' : l.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect
          (shelfc.x + (0 - (placeBoundsX execution.params cg run execution.measured
            loops).minX))
          (shelfc.y + (-(placeBoundsX execution.params cg run execution.measured
            loops).minY))
          (Elegant.Layered.routeLabelRect execution.params cg run execution.measured measured))) := by
    rw [hrect, hm, hh, hd, hpx, hpy]
  obtain ⟨v, hv, hreal, hs0, hs1, hbrect⟩ |
    ⟨packed', c', d', labelPart', boxPart, shelfc', shelfd, rl', r, hpacked', hcpart,
      hcshelf, hdpart, hdshelf, hcd, hrlmem', hrmem, hlrect', hbrect'⟩ :=
    hbox execution l index source measured comp candidate run cg edge decl e
      packed c labelPart shelfc loops area rl
      hlmem hin hleq hmeasured hcomp hcg hrun' he hedge hmlabel hpacked hselected
      hpart1 hpartdef hrlmem hlrect b hdump hex hscope
  · exact Or.inl ⟨comp, candidate, run, orderOptions, cg, edge, decl, v, e,
      shelfc.x + (0 - (placeBoundsX execution.params cg run execution.measured
        loops).minX),
      shelfc.y + (-(placeBoundsX execution.params cg run execution.measured
        loops).minY),
      execution.params.canvasMargin, execution.packedAcc.canvasH, o.direction,
      hcomp, hcg, hrun, he, hedge, hmlabel, hv, hreal, hs0, hs1,
      hrect', hbrect⟩
  · exact Or.inr ⟨packed', c', d', labelPart', boxPart, shelfc', shelfd, rl', r, hpacked',
      hcpart, hcshelf, hdpart, hdshelf, hcd, hrlmem', hrmem, hlrect', hbrect'⟩

/-- X packing separation holds unconditionally: mirror of `partsSeparated_holds`. -/
theorem X_partsSeparated_holds {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} :
    X_PartsSeparated exactIds inp o res := by
  intro execution packed c part shelf hpack hmem hshelf
  obtain ⟨hbLen, hbEq⟩ := List.getElem?_eq_some_iff.mp hshelf
  have hmemlist : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hmem
  have hbounded := exactPartsBounded' execution part hmemlist
  unfold PartBounded at hbounded
  have hmapLen : c < (execution.componentsAcc.parts.map
      (fun q => Pack.Item.mk q.2.width q.2.height q.2.area)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hmem).1
  have hpartget := (List.getElem?_eq_some_iff.mp hmem).2
  have hitem : (execution.componentsAcc.parts.map
      (fun q => Pack.Item.mk q.2.width q.2.height q.2.area))[c] =
      Pack.Item.mk part.2.width part.2.height part.2.area := by
    rw [List.getElem_map, hpartget]
  obtain ⟨hsw, hsh⟩ := packShelfDims hpack hbLen hmapLen
  subst hbEq
  have hwb : packed.boxes[c].w = part.2.width := by
    rw [hsw, hitem]
  have hhb : packed.boxes[c].h = part.2.height := by
    rw [hsh, hitem]
  refine ⟨fun l hl => ?_, fun r hr => ?_⟩
  · refine orient_transport_contained ?_
    simp only [shiftRect, Rect.Contained]
    rw [hwb, hhb]
    obtain ⟨_, _, _, _, _, hlabels⟩ := hbounded
    obtain ⟨hl1, hl2, hl3, hl4, _, _⟩ := hlabels l hl
    omega
  · refine orient_transport_contained ?_
    simp only [shiftRect, Rect.Contained]
    rw [hwb, hhb]
    obtain ⟨_, _, hrects, _, _, _⟩ := hbounded
    obtain ⟨hr1, hr2, hr3, hr4, _, _⟩ := hrects r hr
    omega

/-- Two positions of a model label list whose labels share an id are equal. -/
private theorem X_caption_index_eq_of_id_eq {l : List ModelLabel}
    (hn : (l.map (·.id)).Nodup) {i j : Nat} {a b : ModelLabel}
    (hi : l[i]? = some a) (hj : l[j]? = some b) (hid : a.id = b.id) : i = j := by
  have hin : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjn : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hget : (l.map (·.id))[i]? = (l.map (·.id))[j]? := by
    rw [List.getElem?_map, hi, List.getElem?_map, hj]
    simp only [Option.map_some]
    exact congrArg Option.some hid
  have e1 : (l.map (·.id))[i]? = some a.id := by
    rw [List.getElem?_map, hi, Option.map_some]
  have e2 : (l.map (·.id))[j]? = some a.id := by
    rw [List.getElem?_map, hj, Option.map_some, hid]
  have h3 : i < (l.map (·.id)).length := by simpa using hin
  have h4 : j < (l.map (·.id)).length := by simpa using hjn
  have hv : (l.map (·.id))[i]'h3 = (l.map (·.id))[j]'h4 :=
    Option.some.inj ((List.getElem?_eq_getElem h3).symm.trans (e1.trans (e2.symm.trans
      (List.getElem?_eq_getElem h4))))
  have hp := List.pairwise_iff_getElem.mp hn
  by_cases hlt : i < j
  · exact absurd hv (hp i j h3 h4 hlt)
  · by_cases hjt : j < i
    · exact absurd hv.symm (hp j i h4 h3 hjt)
    · omega

/-- X caption containment: mirror of `sceneCaptionBoxContainment`. -/
theorem X_sceneCaptionBoxContainment {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hclear : X_CaptionScopeClearance exactIds) :
    X_SceneCaptionBoxContainment exactIds inp o res := by
  intro execution l index source hl hsrc hid hmeas howner b hb hex hscope
  rw [execution.scene_eq] at hl
  obtain ⟨q, hq, hemitted⟩ := List.mem_filterMap.mp hl
  obtain ⟨lmodel, lindex⟩ := q
  have hsrcL : inp.labels[lindex]? = some lmodel := List.mem_zipIdx_iff_getElem?.mp hq
  have hlabelNodes := Elegant.Layered.labelIds_nodup hwf
  cases hexcl : inp.boxes.any
      (fun box => box.id == lmodel.owner && box.exclusive) with
  | true =>
    rw [hexcl] at hemitted
    simp only [↓reduceIte] at hemitted
    cases hemitted
  | false =>
    rw [hexcl] at hemitted
    simp only at hemitted
    cases hm : execution.measured.find? (fun item => item.index == lindex) with
    | some measured =>
      rw [hm] at hemitted
      have heq : l = _ := (Option.some.inj hemitted).symm
      have hidEq : lmodel.id = source.id := by
        have h1 : l.id = lmodel.id := by rw [heq]
        exact h1.symm.trans hid
      have hindex : lindex = index :=
        X_caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
      rw [hindex] at hm
      rw [hm] at hmeas
      cases hmeas
    | none =>
      rw [hm] at hemitted
      cases ho : inp.boxes.findIdx?
          (fun box => box.id == lmodel.owner && !box.exclusive) with
      | none =>
        rw [ho] at hemitted
        cases hemitted
      | some ownerIndex =>
        rw [ho] at hemitted
        have heq : l = _ := (Option.some.inj hemitted).symm
        have hidEq : lmodel.id = source.id := by
          have h1 : l.id = lmodel.id := by rw [heq]
          exact h1.symm.trans hid
        have hindex : lindex = index :=
          X_caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
        rw [hindex] at hsrcL
        have hlmodel : lmodel = source := Option.some.inj (hsrcL.symm.trans hsrc)
        have hoS : inp.boxes.findIdx?
            (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex := by
          rw [← hlmodel]
          exact ho
        have hrect : l.rect = sceneCaptionRect execution.params inp o
            execution.lines execution.packedAcc ownerIndex source.owner := by
          rw [congrArg (fun s : SceneLabel => s.rect) heq]
          unfold sceneCaptionRect
          rw [hlmodel]
          rfl
        have hscope' : b.id ∉ res.scene.layoutDump.labelOwnerAnc
            (X_captionLabel exactIds execution ownerIndex source l.lines) := by
          have hown : (X_captionLabel exactIds execution ownerIndex source l.lines).owner =
              l.toLabel.owner := by
            simp only [X_captionLabel]
            have h2 : l.owner = source.owner := by
              rw [congrArg (fun s : SceneLabel => s.owner) heq]
              rw [hlmodel]
            rw [h2]
          rw [Elegant.Layered.labelOwnerAnc_congr_owner hown]
          exact hscope
        have hclr := hclear inp o res execution index ownerIndex source l.lines b hsrc
          (by rw [hindex] at hm; exact hm) hoS hb hex hscope'
        rw [hrect]
        exact hclr

/-- X flat C7 assembly: mirror of `layout_c7` over the exact execution. -/
theorem X_layout_c7 {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (hsep : X_PartsSeparated exactIds inp o res)
    (hseam1 : X_LabelRunsClearExclusiveBoxes exactIds inp o res)
    (hseam2 : X_SceneCaptionBoxContainment exactIds inp o res)
    (h : layoutX exactIds inp o = .ok res) :
    Validator.C7 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  intro l hl b hb hex hscope
  rw [Scene.layoutDump] at hl
  obtain ⟨sl, hsl, hleq⟩ := List.mem_map.mp hl
  subst hleq
  obtain ⟨source, index, hsource, _, hid, _, hbranch⟩ :=
    X_label_source_split execution hsl
  cases hbranch with
  | inl hmeas =>
    obtain ⟨measured, hmeasured⟩ := hmeas
    obtain ⟨comp, candidate, run, orderOptions, cg, edge, decl, v, e,
        px, py, m, hgt, hdir, hcomp, hcg, hrun, he, hedge, hmlabel, hv, hreal,
        hs0, hs1, hlreq, hbreq⟩ |
      ⟨packed, c, d, labelPart, boxPart, shelfc, shelfd, rl, r, hpacked,
        hcpart, hcshelf, hdpart, hdshelf, hcd, hrlmem, hrmem, hlrect, hbrect⟩ :=
      hseam1.2 execution sl index source measured b hsl hsource hid hmeasured
        hb hex hscope
    · have hclr := hseam1.1 execution comp candidate run orderOptions cg edge decl v e
        measured hcomp hcg hrun he hedge hmlabel hv hreal hs0 hs1
      have hrect : sl.toLabel.rect = sl.rect := rfl
      rw [hrect, hlreq, hbreq]
      exact not_meetsInterior_transport hclr
    · obtain ⟨hlwithin, _⟩ := hsep execution packed c labelPart shelfc hpacked
        hcpart hcshelf
      obtain ⟨_, hrwithin⟩ := hsep execution packed d boxPart shelfd hpacked
        hdpart hdshelf
      have hlw := hlwithin rl hrlmem
      have hrw := hrwithin r hrmem
      rw [← hlrect] at hlw
      rw [← hbrect] at hrw
      obtain ⟨hc1, hsc⟩ := List.getElem?_eq_some_iff.mp hcshelf
      obtain ⟨hd1, hsd⟩ := List.getElem?_eq_some_iff.mp hdshelf
      have hboxes := Pack.pack_boxes_disjoint hpacked c d hc1 hd1 hcd
      rw [hsc, hsd] at hboxes
      have hT : ¬ (shiftRect execution.params.canvasMargin
          execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH shelfc)).meetsInterior
          (shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH shelfd)) :=
        not_meetsInterior_shiftRect
          (not_meetsInterior_orientRect hboxes)
      have hso : shiftRect shelfc.x shelfc.y
          (Rect.mk 0 0 shelfc.w shelfc.h) = shelfc := by
        cases shelfc; simp [shiftRect]
      have hsdo : shiftRect shelfd.x shelfd.y
          (Rect.mk 0 0 shelfd.w shelfd.h) = shelfd := by
        cases shelfd; simp [shiftRect]
      rw [hso] at hlw
      rw [hsdo] at hrw
      have hrect : sl.toLabel.rect = sl.rect := rfl
      rw [hrect]
      exact not_meetsInterior_of_contained hT hlw hrw
  | inr hcap =>
    obtain ⟨hnone, howner⟩ := hcap
    obtain ⟨ownerIndex, hownerIdx⟩ := howner
    exact hseam2 execution sl index source hsl hsource hid hnone
      ⟨ownerIndex, hownerIdx⟩ b hb hex hscope

/-- Flat C7 for the exact pipeline: every successful `layoutX` keeps every
label clear of exclusive boxes outside the label's owner scope, modulo the
X branch, placement, and caption residuals. -/
theorem flatC7B_layoutX (exactIds : List String)
    (hloop : X_RunLocalLoopSeparation exactIds)
    (hfwd : X_RunLocalForwardSeparation exactIds)
    (hrev : X_RunLocalReversedSeparation exactIds)
    (hplaced : X_RouteLabelsPlaced)
    (hdecl : X_ExclusiveRunNodeDecl exactIds)
    (hkey : X_ExclusiveKeyOutsideCgPaths exactIds)
    (hcap : X_CaptionScopeClearance exactIds) :
    FlatC7B (layoutX exactIds) := by
  intro inp o res hwf hfp _hfit hsep hseam1 hseam2 h
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hrunlocal : X_RunLocalLabelClearance exactIds inp o res :=
    X_runLocalLabelClearance_holds (inp := inp) (o := o) (res := res) hloop hfwd hrev
  have hbelong : X_LabelBelongsToRun exactIds inp o res :=
    X_labelBelongsToRun (inp := inp) (o := o) (res := res) hwf hplaced
  have hbox : X_ExclusiveBoxInLabelRun exactIds inp o res :=
    X_exclusiveBoxInLabelRun (inp := inp) (o := o) (res := res) hwf hfp hdecl hkey
  have hbridges : X_RouteLabelDumpBridges exactIds inp o res :=
    X_routeLabelDumpBridges (inp := inp) (o := o) (res := res) hbelong hbox
  have hparts : X_PartsSeparated exactIds inp o res :=
    X_partsSeparated_holds (inp := inp) (o := o) (res := res)
  have hcaps : X_SceneCaptionBoxContainment exactIds inp o res :=
    X_sceneCaptionBoxContainment (inp := inp) (o := o) (res := res) hwf hcap
  exact X_layout_c7 hwf hfp hparts ⟨hrunlocal, hbridges⟩ hcaps h

end PipelineImpl
end Layered
end Elegant

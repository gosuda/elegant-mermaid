import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionFlatInset
import Elegant.Layered.RegionReduction
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactFlatC7
import Elegant.Layered.RegionFlatC5
import Elegant.Layered.ExactLoopEnvelopeLayerProof
import Elegant.Layered.ExactLoopEnvelopeReserveProof
set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region flat C7 (`layoutRIds`).

Packet P7 of `local://region-tower-plan.md` (field 7, `flatC7`): the region
analogue of `flatC7B_layoutX_fit` (`Layered/ExactFlatC7Fit.lean:137-143`) and
its W form `flatC7B_layoutX_fitW` (`Layered/ExactCaptionScopeFitWProof.lean`).

W form means: the local `WellFormed (inputModel inp o)` (and `InputFixedFit`)
premises appear after the execution binder, so family theorems discharge them
per executed input instead of over all inputs. No `framedParents` premise
appears on the caption leaves: none of the consumed exact leaves needs it.

Proved here:
- `R7_runLocalLoopSeparation_of_envelopeMiss`: the loop-separation bridge
  replays verbatim over `componentRunR` (envelope containment is
  run-origin independent; only slot nonnegativity and measured
  nonnegativity are needed, both available for regions).
- `R7_ownerSelfMiss_none_holds` / `R7_plainReserve_none_holds`: the own-node
  (`XLEM_self_holds`) and plain-reserve (`XLEM_plainReserve_holds`) leaves
  replay for empty region sets via `componentRunR_none` (titles are
  irrelevant there: `coordinateGraphR_none`). The execution conversion
  `r7_executionX_of_nil` uses `layoutComponentR_none`; the decls-nodup
  bridge (`r7_candidateR_decls_nodup`, via `rfc5_edges_decls`) covers the
  rewritten graph.
- `flatC7B_layoutRIds_W`: the W assembly replaying `flatC7B_layoutX_fitW`
  over `SceneExecutionR`, from the W loop separation, the run-local
  forward/reversed separations (via `r7_runLocalLabelClearance_holds`), the
  assembled bridges, the chosen-run sizing residual
  (`R_PartSizingRResidual`, via `r7_partsSeparated_holds`), and the W caption
  clearance (via `r7_sceneCaptionBoxContainmentFitW` into `r7_layout_c7`).

Open named residuals include `R7_RunLocalForwardSeparation`,
`R7_RunLocalReversedSeparation`, `R7_LoopEnvelopeMiss`,
`R7_OwnerSelfMiss` and `R7_PlainReserve` for nonempty sets,
`R7_SameRankMiss`, `R7_OtherRankMiss`, `R7_OtherOwner`,
`R7_CaptionTitleBranch`, and `R7_CaptionDescendantClear`.
The route-placement and exclusive-node identity leaves are proved in
`RegionLabelPlacementProof`, `RegionRunNodeIdentity`, and `RegionExclusivePath`.

Truth note (plan section 4 item 4): the `some`-case reserve
(`R7_PlainReserve` with `titleReservationsR` giving titles their own height)
was suspect — region titles could decouple loop-band heights from rank
bands — so only the `none` case is closed here. The probe
(`proofs/wip/Probe/RegionFlatC7TProbe.lean`) executes six inputs (flat,
single-region-set, nested-region-set, zero-size fixed, empty, duplicate-id
self-loops) against `layoutRIds` success, `Validator.c7`, and the reserve
inequality on every component run: all succeed with `c7 = true` and every
reserve check `true`, including both `some`-case self-loops. The suspicion
is not confirmed on these probes; the `some`-case leaves stay open pending
the full P3/P5 replay, true on every executed probe row.
-/
/-- Region spec fixed by the executed input, exactly as `SceneExecutionR`
threads it into the components fold. -/
def r7Spec (idSets : List (String × List String)) (o : Options)
    (P : Params) (lines : List (List Measure.Line)) : Option RegionSpec :=
  if idSets.isEmpty then none
    else some (RegionSpec.mk idSets (lines.map fun ls =>
      let width := ls.foldl (fun w line => max w line.width) 0
      let height := (max 1 ls.length : Int) * P.lineH
      match o.direction with
      | .LR | .RL => (height, width)
      | .TB | .BT => (width, height)))

/-- Effective per-component spec, exactly as `componentTrialR` downgrades it:
a component with no regions runs with `none`. -/
def r7Eff (idSets : List (String × List String)) (o : Options)
    (P : Params) (lines : List (List Measure.Line))
    (rs : Option ComponentRegions) : Option RegionSpec :=
  if rs.isSome then r7Spec idSets o P lines else none

/-- Region loop-envelope miss: mirror of `X_LoopEnvelopeMiss` over
`SceneExecutionR` / `componentRunR`. Edge and node lookups run over the
rewritten graph `cg'` that the run was computed on. -/
def R7_LoopEnvelopeMiss (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] →
    ¬ (loopFootprintExt cg' run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Region loop-branch residual: mirror of `X_RunLocalLoopSeparation` over
`SceneExecutionR` / `componentRunR`. -/
def R7_RunLocalLoopSeparation (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[k]? = some e →
    e.tail = e.head →
    labelEnvelope execution.params cg' run execution.measured k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] →
    Elegant.Layered.LoopFootprintSeparation execution.params cg' run
      execution.measured k e env v

/-- Region forward-branch residual: mirror of `X_RunLocalForwardSeparation`. -/
def R7_RunLocalForwardSeparation (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat) (r : Rect),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[k]? = some e →
    e.tail ≠ e.head →
    e.reversed = false →
    labelEnvelope execution.params cg' run execution.measured k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] →
    r ∈ Labels.stackRects env.x env.y cg'.slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) →
    Elegant.Layered.RectAxisSeparated r (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Region reversed-branch residual: mirror of `X_RunLocalReversedSeparation`. -/
def R7_RunLocalReversedSeparation (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (k : Nat) (e : Edge)
    (env : Rect) (v : Nat) (r : Rect),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[k]? = some e →
    e.tail ≠ e.head →
    e.reversed = true →
    labelEnvelope execution.params cg' run execution.measured k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] →
    r ∈ Labels.stackRects env.x env.y cg'.slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) →
    (RouteImpl.boxRect run.proper run.xs run.ys v).x +
      (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤ r.x
/-- Region placement residual: mirror of `X_RouteLabelsPlaced` over
`componentRunR`. About the placement phase only. -/
def R7_RouteLabelsPlaced : Prop :=
  ∀ (P : Params) (exact : List Nat) (spec : Option RegionSpec) (inp : Input)
    (cg cg' : Graph) (labels : List MeasuredLabel)
    (orderOptions : OrderOptions) (run : Run) (l : MeasuredLabel)
    (edge : Nat) (e : Edge),
    componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    cg'.edges[edge]? = some e → l ∈ routeLabels labels e.decl →
    ∃ rect, (l.index, rect) ∈ placedLabels P cg' run labels

/-- Region run-phase id residual: mirror of `X_ExclusiveRunNodeDecl` over
`SceneExecutionR` / `componentRunR`. No geometry. -/
def R7_ExclusiveRunNodeDecl (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    ∀ (v key : Nat) (source : ModelBox),
      comp[v]? = some key →
      inp.boxes[key]? = some source →
      RouteImpl.nodeDecl run.proper v = key

/-- Region measured-graph id residual: mirror of
`X_ExclusiveKeyOutsideCgPaths` over the region execution graph. -/
def R7_ExclusiveKeyOutsideCgPaths (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (v key : Nat) (source : ModelBox)
    (execution : SceneExecutionR exactIds idSets inp o res),
    comp ∈ components execution.graph →
    comp[v]? = some key →
    inp.boxes[key]? = some source → source.exclusive = true →
    ∀ (u : Nat) (nd : Node),
      (componentCandidateR (r7Spec idSets o execution.params execution.lines)
        execution.graph comp candidate).nodes[u]? = some nd →
      key ∉ nd.clusterPath

/-- Region caption label: mirror of `X_captionLabel` over the region
execution. -/
def R7_captionLabel (exactIds : List String) {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (ownerIndex : Nat) (source : ModelLabel) (lines : List String) : Label :=
  ⟨source.id, source.owner,
    sceneCaptionRect execution.params inp o execution.lines
      execution.packedAcc ownerIndex source.owner, lines⟩

/-- Well-formed-local region caption clearance: mirror of
`X_CaptionScopeClearanceFitW` over `SceneExecutionR`, with local `WellFormed`
and `InputFixedFit` premises after the execution binder. -/
def R7_CaptionScopeClearanceFitW (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) →
    InputFixedFit inp o →
    ∀ (index ownerIndex : Nat) (source : ModelLabel) (lines : List String) (b : Box),
      inp.labels[index]? = some source →
      execution.measured.find? (fun item => item.index == index) = none →
      inp.boxes.findIdx?
        (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
      b ∈ res.scene.layoutDump.boxes →
      b.exclusive = true →
      b.id ∉ res.scene.layoutDump.labelOwnerAnc
        (R7_captionLabel exactIds execution ownerIndex source lines) →
      ¬ (sceneCaptionRect execution.params inp o execution.lines
          execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- Region own-node envelope leaf: mirror of `XLEM_OwnerSelfMiss`. The
footprint of a plain loop owner misses the owner box. -/
def R7_OwnerSelfMiss (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (cg'.nodes.getD e.tail default).border = 0 →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {pu : Nat}, layer[pu]? = some e.tail → layer[pu]? = some v →
    ¬ (loopFootprintExt cg' run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Region plain-reserve leaf: mirror of `XLEM_PlainReserve`. A self-loop on
a non-exact plain owner reserves its band stack in the owner frame. -/
def R7_PlainReserve (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (k : Nat) (e : Edge),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[k]? = some e →
    e.tail = e.head →
    (cg'.nodes.getD e.tail default).border ≠ -2 →
    run.exact.contains e.tail = false →
    ((loopSizes cg'.edges execution.measured e.tail cg'.slot).length : Int) *
      Loops.band cg'.slot (loopSizes cg'.edges execution.measured e.tail cg'.slot) ≤
      (frameRect execution.params cg' run e.tail).h

/-- Region same-rank envelope leaf: mirror of `X_loopEnvSameRank`. -/
def R7_SameRankMiss (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[k]? = some e →
    e.tail = e.head →
    run.exact.contains e.tail = true →
    (∀ nt, cg'.nodes[e.tail]? = some nt → nt.border = 0) →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] →
    ∀ (r : Nat) (l : List Nat),
    run.layers[r]? = some l → e.tail ∈ l → v ∈ l → v ≠ e.tail →
    ¬ (loopFootprintExt cg' run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Region other-rank envelope leaf: mirror of `X_loopEnvOtherRank`. -/
def R7_OtherRankMiss (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[k]? = some e →
    e.tail = e.head →
    run.exact.contains e.tail = true →
    (∀ nt, cg'.nodes[e.tail]? = some nt → nt.border = 0) →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] →
    ∀ (rt rv : Nat) (lt lv : List Nat),
    run.layers[rt]? = some lt → e.tail ∈ lt →
    run.layers[rv]? = some lv → v ∈ lv → rt ≠ rv →
    ¬ (loopFootprintExt cg' run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Region nonstandard-owner envelope leaf: mirror of `X_loopEnvOtherOwner`.
No probe exercises a non-exact or non-zero-border loop owner, so it holds
vacuously there. -/
def R7_OtherOwner (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (run.exact.contains e.tail = false ∨
      ∃ nt, cg'.nodes[e.tail]? = some nt ∧ nt.border ≠ 0) →
    ¬ (loopFootprintExt cg' run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)
/-- Region run-local clearance: mirror of `X_RunLocalLabelClearance` over
the region execution. -/
def R7_RunLocalLabelClearance (exactIds : List String)
    (idSets : List (String × List String)) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (edge decl v : Nat)
    (e : Edge) (l : MeasuredLabel),
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    (cg'.edges[edge]?) = some e →
    (cg'.edges[edge]?).map (·.decl) = some decl →
    l ∈ routeLabels execution.measured decl →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] →
    ¬ (Elegant.Layered.routeLabelRect execution.params cg' run execution.measured l).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Region label bridge: mirror of `X_RouteLabelDumpBridges` over the region
execution. -/
def R7_RouteLabelDumpBridges (exactIds : List String)
    (idSets : List (String × List String)) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionR exactIds idSets inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel) (measured : MeasuredLabel) (b : Box),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = some measured →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    (∃ (comp : List Nat) (candidate : Nat) (run : Run)
      (orderOptions : OrderOptions) (cg cg' : Graph) (edge decl v : Nat)
      (e : Edge) (px py m h : Int) (d : Direction),
      comp ∈ components execution.graph ∧
      ∃ (rs : Option ComponentRegions),
      newComponentRegions (r7Spec idSets o execution.params execution.lines)
        execution.params inp (componentGraph execution.graph comp) = .ok rs ∧
      cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
        execution.graph comp candidate ∧
      componentRunR execution.params (exactDecls exactIds inp)
        (r7Eff idSets o execution.params execution.lines rs)
        inp cg execution.measured orderOptions = .ok (cg', run) ∧
      (cg'.edges[edge]?) = some e ∧
      (cg'.edges[edge]?).map (·.decl) = some decl ∧
      measured ∈ routeLabels execution.measured decl ∧
      v < run.proper.nodes.length ∧
      RouteImpl.IsReal run.proper v ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] ∧
      l.rect = shiftRect m m
        (orientRect d h (shiftRect px py
          (Elegant.Layered.routeLabelRect execution.params cg' run execution.measured measured))) ∧
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

/-- Region label-runs seam: mirror of `X_LabelRunsClearExclusiveBoxes`. -/
abbrev R7_LabelRunsClearExclusiveBoxes (exactIds : List String)
    (idSets : List (String × List String)) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  R7_RunLocalLabelClearance exactIds idSets inp o res ∧
    R7_RouteLabelDumpBridges exactIds idSets inp o res

/-- Region packing seam: mirror of `X_PartsSeparated` over the region
execution. -/
def R7_PartsSeparated (exactIds : List String)
    (idSets : List (String × List String)) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionR exactIds idSets inp o res) (packed : Pack.State)
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

/-- Region caption seam: mirror of `X_SceneCaptionBoxContainment` over the
region execution. -/
def R7_SceneCaptionBoxContainment (exactIds : List String)
    (idSets : List (String × List String)) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionR exactIds idSets inp o res) (l : SceneLabel) (index : Nat)
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

/-- Region title-branch caption leaf: mirror of `X_CaptionTitleBranchClear`. -/
def R7_CaptionTitleBranch (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res) (index ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (R7_captionLabel exactIds execution ownerIndex source lines) →
    ((sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find?
          (fun title => title.1 == source.owner)).isSome = true →
    ¬ (sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- Region descendant caption leaf: mirror of
`X_CaptionDescendantSamePartClear`. -/
def R7_CaptionDescendantClear (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionR exactIds idSets inp o res)
    (index ownerIndex bi : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (R7_captionLabel exactIds execution ownerIndex source lines) →
    source.owner ∈ res.scene.layoutDump.ancestors b.id →
    ∀ (kO kB posO posB : Nat) (partO partB : List Nat × Part),
      res.scene.boxes[bi]? = some b →
      execution.componentsAcc.parts[kO]? = some partO →
      execution.componentsAcc.parts[kB]? = some partB →
      partO.1[posO]? = some ownerIndex →
      partB.1[posB]? = some bi →
      ¬ (sceneCaptionRect execution.params inp o execution.lines
          execution.packedAcc ownerIndex source.owner).meetsInterior b.rect
/-- Empty region sets fix the spec to `none`, definitionally. -/
private theorem r7Spec_nil (o : Options) (P : Params)
    (lines : List (List Measure.Line)) : r7Spec [] o P lines = none := rfl

/-- A successful region run rejects a negative component label-stack slot,
exactly like the exact run (replay of `componentRunX_slot_nonneg` over
`componentRunR_specR`). -/
private theorem r7_componentRunR_slot_nonneg {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    0 ≤ cg'.slot := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hRest⟩ := componentRunR_specR h
  obtain ⟨_, _, hNorm, _⟩ := hRest
  unfold NormalizeImpl.normalize at hNorm
  split at hNorm
  · simp at hNorm
  · rename_i slot hs
    split at hNorm
    · rename_i hc
      by_cases hz : cg'.slot = 0
      · omega
      · have he : cg'.slot = slot := by
          simpa [NormalizeImpl.slotOf, hz] using hs
        rw [he]
        exact hc.2.2
    · simp at hNorm

/-- Invert the plain-width loop `labelEnvelope` branch over a region run
(copy of `XEnvT_envelope_eq`; the envelope equation is run-origin
independent). -/
private theorem r7_env_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hloop : e.tail = e.head) (hnoex : run.exact.contains e.tail = false)
    (henv : labelEnvelope P cg run labels k e = some env) :
    env = (Loops.placement (frameRect P cg run e.tail) cg.slot
      (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
      (loopEdges cg.edges e.tail).length
      (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
      (stackSize cg.slot (routeLabels labels e.decl))).label := by
  unfold labelEnvelope at henv
  obtain ⟨_first, _hfirst, hrest⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (e.tail == e.head) = true := by simp [hloop]
  simp only [hb, hnoex] at hrest
  exact (Option.some.inj hrest).symm

/-- Invert the exact-width loop `labelEnvelope` branch over a region run
(copy of `XEnvT_exact_envelope_eq`). -/
private theorem r7_exact_env_eq {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hloop : e.tail = e.head) (hex : run.exact.contains e.tail = true)
    (henv : labelEnvelope P cg run labels k e = some env) :
    env = (Loops.exactPlacement (frameRect P cg run e.tail) cg.slot
      (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
      (loopEdges cg.edges e.tail).length
      (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
      (stackSize cg.slot (routeLabels labels e.decl))).label := by
  unfold labelEnvelope at henv
  obtain ⟨_first, _hfirst, hrest⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (e.tail == e.head) = true := by simp [hloop]
  simp only [hb, hex] at hrest
  exact (Option.some.inj hrest).symm

/-- Loop separation over the region run from the extended footprint miss:
replay of `X_runLocalLoopSeparation_of_envelopeMiss`. The envelope is
contained in the extended footprint in both width branches, and the residual
keeps that footprint off every in-scope box. -/
theorem R7_runLocalLoopSeparation_of_envelopeMiss (exactIds : List String)
    (idSets : List (String × List String))
    (h : R7_LoopEnvelopeMiss exactIds idSets) :
    R7_RunLocalLoopSeparation exactIds idSets := by
  unfold R7_RunLocalLoopSeparation
  intro inp o res execution comp candidate run orderOptions cg cg' k e env v
    hcomp rs hNew hcg hrun hk hloop henv hv hreal hscope₀ hscope₁
  have hslot := r7_componentRunR_slot_nonneg hrun
  have hlab := SceneExecutionR.measured_nonnegR execution
  have hmiss := h inp o res execution comp candidate run orderOptions cg cg' k e v
    hcomp rs hNew hcg hrun hk hloop hv hreal hscope₀ hscope₁
  by_cases htrue : run.exact.contains e.tail = true
  · have henv_eq := r7_exact_env_eq hloop htrue henv
    have hcont := X_loopExactEnvelope_containedExt hslot hlab hk hloop henv_eq htrue
    exact Elegant.Layered.not_meetsInterior_of_contained hcont hmiss
  · have hfalse : run.exact.contains e.tail = false := by
      cases he : run.exact.contains e.tail with
      | true => exact absurd he htrue
      | false => rfl
    have henv_eq := r7_env_eq hloop hfalse henv
    have hcont := X_loopEnvelope_containedExt hslot hlab hfalse hk hloop henv_eq
    exact Elegant.Layered.not_meetsInterior_of_contained hcont hmiss
/-- The region execution with empty region sets is the exact execution:
`layoutComponentR` coincides with `layoutComponentX` under `none`
(`layoutComponentR_none`), so the components fold is the exact fold. -/
private theorem r7_foldX_of_nil {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {graph : Graph} {measured : List MeasuredLabel}
    {lines : List (List Measure.Line)} {mid : Acc}
    (h : (components graph).foldlM
      (fun acc comp => layoutComponentR P exactIds (r7Spec [] o P lines) inp o
        graph acc comp measured)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩ = .ok mid) :
    (components graph).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o graph acc comp measured)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩ = .ok mid := by
  rw [r7Spec_nil] at h
  simpa only [layoutComponentR_none] using h

/-- Execution conversion for empty region sets. -/
private def r7_executionX_of_nil {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds [] inp o res) :
    SceneExecutionX exactIds inp o res :=
  { params := execution.params
    metric := execution.metric
    lines := execution.lines
    measured := execution.measured
    graph0 := execution.graph0
    graph := execution.graph
    componentsAcc := execution.componentsAcc
    packedAcc := execution.packedAcc
    checked := execution.checked
    metric_eq := execution.metric_eq
    lines_eq := execution.lines_eq
    components_eq := by
      have hfold := execution.components_eq
      apply r7_foldX_of_nil
      exact hfold
    measured_eq := execution.measured_eq
    graph0_eq := execution.graph0_eq
    graph_eq := execution.graph_eq
    packed_eq := execution.packed_eq
    scene_eq := execution.scene_eq }

/-- Effective spec over empty region sets is `none`, whichever regions the
component reports. -/
private theorem r7Eff_nil (o : Options) (P : Params)
    (lines : List (List Measure.Line)) (rs : Option ComponentRegions) :
    r7Eff [] o P lines rs = none := by
  unfold r7Eff
  split
  · exact r7Spec_nil _ _ _
  · rfl

/-- The own-node envelope leaf replays for empty region sets: with no regions
the run is the exact run (`componentRunR_none`), so `XLEM_self_holds`
applies through the execution conversion. -/
theorem R7_ownerSelfMiss_none_holds :
    R7_OwnerSelfMiss [] [] := by
  intro inp o res execution comp candidate run orderOptions cg cg' k e v
    hcomp rs hNew hcg hrun hk hloop hv hreal hscope₀ hscope₁ hB0
    layer hlayer pu hpu hpv
  have heff : r7Eff [] o execution.params execution.lines rs = none :=
    r7Eff_nil _ _ _ _
  rw [heff] at hcg hrun
  rw [componentCandidateR_none] at hcg
  rw [componentRunR_none] at hrun
  cases hX : componentRunX execution.params (exactDecls [] inp) cg
      execution.measured orderOptions with
  | error err =>
    simp only [hX, Except.map] at hrun
    exact absurd hrun (by simp)
  | ok runX =>
    simp only [hX, Except.map] at hrun
    have hpair : (cg, runX) = (cg', run) := by injection hrun
    have hcg' : cg' = cg := by
      have h := congrArg Prod.fst hpair
      simpa using h.symm
    have hrunX : runX = run := by
      have h := congrArg Prod.snd hpair
      simpa using h
    subst hcg'
    rw [hrunX] at hX
    exact XLEM_self_holds [] inp o res (r7_executionX_of_nil execution)
      comp candidate run orderOptions cg' k e v hcomp hcg hX hk hloop hv hreal
      hscope₀ hscope₁ hB0 (layer := layer) hlayer (pu := pu) hpu hpv

/-- The plain-reserve leaf replays for empty region sets: same transport as
the own-node case, closing `XLEM_plainReserve_holds`. -/
theorem R7_plainReserve_none_holds :
    R7_PlainReserve [] [] := by
  intro inp o res execution comp candidate run orderOptions cg cg' k e
    hcomp rs hNew hcg hrun hedge hself hbdr hnex
  have heff : r7Eff [] o execution.params execution.lines rs = none :=
    r7Eff_nil _ _ _ _
  rw [heff] at hcg hrun
  rw [componentCandidateR_none] at hcg
  rw [componentRunR_none] at hrun
  cases hX : componentRunX execution.params (exactDecls [] inp) cg
      execution.measured orderOptions with
  | error err =>
    simp only [hX, Except.map] at hrun
    exact absurd hrun (by simp)
  | ok runX =>
    simp only [hX, Except.map] at hrun
    have hpair : (cg, runX) = (cg', run) := by injection hrun
    have hcg' : cg' = cg := by
      have h := congrArg Prod.fst hpair
      simpa using h.symm
    have hrunX : runX = run := by
      have h := congrArg Prod.snd hpair
      simpa using h
    subst hcg'
    rw [hrunX] at hX
    exact XLEM_plainReserve_holds [] inp o res (r7_executionX_of_nil execution)
      comp candidate run orderOptions cg' k e hcomp hcg hX hedge hself hbdr hnex
/-- Declaration list is unchanged by the reserved-lane flag map: the
per-edge record updates only touch endpoints and the reversed flag. -/
private theorem r7_flags_decls (flags : List Bool) (raw : Graph) :
    (((raw.edges.map Edge.original).zipIdx.map fun q =>
      if flags.getD q.2 false then
        ({ q.1 with tail := q.1.head, head := q.1.tail, reversed := true } : Edge)
      else q.1).map (·.decl)) = raw.edges.map (·.decl) := by
  have hFF : ((·.decl) ∘ fun q : Edge × Nat => if flags.getD q.2 false then
      ({ q.1 with tail := q.1.head, head := q.1.tail, reversed := true } : Edge)
      else q.1) = ((·.decl) ∘ Prod.fst) := by
    funext q
    simp only [Function.comp_def]
    split <;> rfl
  rw [List.map_map, hFF, ← List.map_map, List.zipIdx_map_fst]
  rw [List.map_map]
  simp only [Function.comp_def, Edge.original_decl]

/-- Region candidates preserve declaration lists: the `none` case is the
plain candidate (`componentCandidate_decls`); the `some` case only remaps
endpoints through the flag map. -/
private theorem r7_candidateR_decls (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec g comp index).edges.map (·.decl) =
      (componentGraph g comp).edges.map (·.decl) := by
  cases spec with
  | none =>
    simp only [componentCandidateR, componentCandidate_decls]
  | some s =>
    simp only [componentCandidateR]
    exact r7_flags_decls _ _

/-- Region candidate declarations are nodup over a nodup graph. -/
private theorem r7_candidateR_decls_nodup (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) (h : (g.edges.map (·.decl)).Nodup) :
    ((componentCandidateR spec g comp index).edges.map (·.decl)).Nodup := by
  rw [r7_candidateR_decls]
  exact componentGraph_decls_nodup _ _ h
/-- Region run-local label clearance holds modulo the three R branch
residuals: replay of `X_runLocalLabelClearance_holds` over
`SceneExecutionR` / `componentRunR`. Edge identity across the two lookups
comes from `cg'` declaration nodup (`rfc5_edges_decls` for the rewrite,
`r7_candidateR_decls_nodup` for the candidate, `exactGraph_decls_nodup`
for the graph). -/
private theorem r7_runLocalLabelClearance_holds {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input}
    {o : Options} {res : FamilyResult}
    (hloop : R7_RunLocalLoopSeparation exactIds idSets)
    (hfwd : R7_RunLocalForwardSeparation exactIds idSets)
    (hrev : R7_RunLocalReversedSeparation exactIds idSets) :
    R7_RunLocalLabelClearance exactIds idSets inp o res := by
  intro execution comp candidate run orderOptions cg cg' edge decl v e l
    hcomp rs hNew hcg hrun he hedge hl hlen hreal hscope₀ hscope₁
  have hlab := SceneExecutionR.measured_nonnegR execution
  have hslot := r7_componentRunR_slot_nonneg hrun
  have hnd : (execution.measured.map (·.index)).Nodup :=
    measureLabels_index_nodup execution.measured_eq
  by_cases hex : ∃ rect, (l.index, rect) ∈
      placedLabels execution.params cg' run execution.measured
  · obtain ⟨rect, hmem⟩ := hex
    have hroute : Elegant.Layered.routeLabelRect execution.params cg' run
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
    have hr : rect ∈ Labels.stackRects env.x env.y cg'.slot
        ((routeLabels execution.measured e'.decl).map fun q => (q.width, q.height)) :=
      (List.of_mem_zip hmemstk).2
    have hedecl : e.decl = decl := by
      rw [he] at hedge
      simpa using hedge
    have hedge' : e'.decl = decl := by
      obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
      have hgg : cg'.edges[edge'] = e' := (List.getElem?_eq_some_iff.mp he').2
      have hpred : e'.decl = ml.edge :=
        beq_iff_eq.mp (by have hmatch' := hmatch; rw [hgg] at hmatch'; simpa using hmatch')
      have hll : ml.edge = decl := by
        have hp := (List.mem_filter.mp hl).2
        simpa using hp
      exact hpred.trans hll
    have hnd_decl : (cg'.edges.map (·.decl)).Nodup := by
      rw [rfc5_edges_decls hrun, hcg]
      exact r7_candidateR_decls_nodup _ execution.graph comp candidate
        (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
    have hEE : e = e' :=
      nodup_map_eq_of_mem hnd_decl (List.mem_of_getElem? he)
        (List.mem_of_getElem? he') (hedecl.trans hedge'.symm)
    rw [hEE] at hscope₀ hscope₁
    have hsep_loop : e'.tail = e'.head →
        Elegant.Layered.LoopFootprintSeparation execution.params cg' run
          execution.measured edge' e' env v :=
      fun heq => hloop inp o res execution comp candidate run orderOptions cg cg'
        edge' e' env v hcomp rs hNew hcg hrun he' heq henv hlen hreal hscope₀ hscope₁
    have hsep_forward : e'.tail ≠ e'.head → e'.reversed = false →
        Elegant.Layered.RectAxisSeparated rect
          (RouteImpl.boxRect run.proper run.xs run.ys v) :=
      fun hne hrev' => hfwd inp o res execution comp candidate run orderOptions cg cg'
        edge' e' env v rect hcomp rs hNew hcg hrun he' hne hrev' henv hlen hreal
        hscope₀ hscope₁ hr
    have hsep_reversed : e'.tail ≠ e'.head → e'.reversed = true →
        (RouteImpl.boxRect run.proper run.xs run.ys v).x +
          (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤ rect.x :=
      fun hne hrev' => hrev inp o res execution comp candidate run orderOptions cg cg'
        edge' e' env v rect hcomp rs hNew hcg hrun he' hne hrev' henv hlen hreal
        hscope₀ hscope₁ hr
    exact Elegant.Layered.runLocalLabelClearance he' henv hslot hlab hr
      hsep_loop hsep_forward hsep_reversed
  · have hfilter : (placedLabels execution.params cg' run execution.measured).filter
        (fun q => q.1 == l.index) = [] := by
      rw [List.filter_eq_nil_iff]
      intro qq hqq hcond
      simp only [beq_iff_eq] at hcond
      exact hex ⟨qq.2, by rw [← hcond]; exact hqq⟩
    have hroute0 : Elegant.Layered.routeLabelRect execution.params cg' run
        execution.measured l = ⟨0, 0, 0, 0⟩ := by
      unfold Elegant.Layered.routeLabelRect
      rw [hfilter]
      rfl
    rw [hroute0]
    exact emptyRect_meets_none
/-- Region label source split: mirror of `X_label_source_split`; the proof
uses only the shared `sceneOf` equation. -/
private theorem r7_label_source_splitR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {label : SceneLabel}
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

/-- Region packing separation holds modulo the chosen-run sizing residual:
mirror of `X_partsSeparated_holds` via
`exactComponentPlacementR_bounded_of_residual` (the universal `R_PartSizingR`
was false and is deleted; `R_PartSizingRResidual` is the true narrower form). -/
private theorem r7_partsSeparated_holds {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input}
    {o : Options} {res : FamilyResult}
    (hres : R_PartSizingRResidual exactIds idSets) :
    R7_PartsSeparated exactIds idSets inp o res := by
  intro execution packed c part shelf hpack hmem hshelf
  obtain ⟨hbLen, hbEq⟩ := List.getElem?_eq_some_iff.mp hshelf
  have hmemlist : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hmem
  have hbounded := exactComponentPlacementR_bounded_of_residual execution hres
    part hmemlist
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

/-- Region flat C7 dispatch: mirror of `X_layout_c7` over the region
execution. -/
private theorem r7_layout_c7 {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (hsep : R7_PartsSeparated exactIds idSets inp o res)
    (hseam1 : R7_LabelRunsClearExclusiveBoxes exactIds idSets inp o res)
    (hseam2 : R7_SceneCaptionBoxContainment exactIds idSets inp o res)
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    Validator.C7 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  intro l hl b hb hex hscope
  rw [Scene.layoutDump] at hl
  obtain ⟨sl, hsl, hleq⟩ := List.mem_map.mp hl
  subst hleq
  obtain ⟨source, index, hsource, _, hid, _, hbranch⟩ :=
    r7_label_source_splitR execution hsl
  cases hbranch with
  | inl hmeas =>
    obtain ⟨measured, hmeasured⟩ := hmeas
    obtain ⟨comp, candidate, run, orderOptions, cg, cg', edge, decl, v, e,
        px, py, m, hgt, hdir, hcomp, rs, hNew, hcg, hrun, he, hedge, hmlabel, hv,
        hreal, hs0, hs1, hlreq, hbreq⟩ |
      ⟨packed, c, d, labelPart, boxPart, shelfc, shelfd, rl, r, hpacked,
        hcpart, hcshelf, hdpart, hdshelf, hcd, hrlmem, hrmem, hlrect, hbrect⟩ :=
      hseam1.2 execution sl index source measured b hsl hsource hid hmeasured
        hb hex hscope
    · have hclr := hseam1.1 execution comp candidate run orderOptions cg cg' edge
        decl v e measured hcomp rs hNew hcg hrun he hedge hmlabel hv hreal hs0 hs1
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
/-- `r7_` copy of the private `xcsw_caption_index_eq_of_id_eq`
(`ExactCaptionScopeFitWProof.lean`): two positions of a model label list
whose labels share an id are equal. Private lemmas do not resolve across
modules. -/
private theorem r7_caption_index_eq_of_id_eq {l : List ModelLabel}
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

/-- Fit-conditioned R caption containment over the W scope clearance:
mirror of `xcsw_sceneCaptionBoxContainmentFitW`
(`ExactCaptionScopeFitWProof.lean`) threading the executed input's
`WellFormed` premise into `hclearFitW`. No premise over all inputs. -/
private theorem r7_sceneCaptionBoxContainmentFitW {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfit : InputFixedFit inp o)
    (hclearFitW : R7_CaptionScopeClearanceFitW exactIds idSets) :
    R7_SceneCaptionBoxContainment exactIds idSets inp o res := by
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
        r7_caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
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
          r7_caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
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
            (R7_captionLabel exactIds execution ownerIndex source l.lines) := by
          have hown : (R7_captionLabel exactIds execution ownerIndex source l.lines).owner =
              l.toLabel.owner := by
            simp only [R7_captionLabel]
            have h2 : l.owner = source.owner := by
              rw [congrArg (fun s : SceneLabel => s.owner) heq]
              rw [hlmodel]
            rw [h2]
          rw [Elegant.Layered.labelOwnerAnc_congr_owner hown]
          exact hscope
        have hclr := hclearFitW inp o res execution hwf hfit index ownerIndex source
          l.lines b hsrc (by rw [hindex] at hm; exact hm) hoS hb hex hscope'
        rw [hrect]
        exact hclr
/-- Flat C7 for the region pipeline under W scope premises: replay of
`flatC7B_layoutX_fitW` (`ExactCaptionScopeFitWProof.lean`) over
`SceneExecutionR`. The loop separation feeds the run-local clearance with
the forward/reversed separations; the bridges are the assembled hypothesis;
the parts separation comes from the chosen-run sizing residual; the caption
containment comes from the W scope clearance at the ambient fit. -/
theorem flatC7B_layoutRIds_W (exactIds : List String)
    (idSets : List (String × List String))
    (hloop : R7_RunLocalLoopSeparation exactIds idSets)
    (hfwd : R7_RunLocalForwardSeparation exactIds idSets)
    (hrev : R7_RunLocalReversedSeparation exactIds idSets)
    (hbridges : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      R7_RouteLabelDumpBridges exactIds idSets inp o res)
    (hres : R_PartSizingRResidual exactIds idSets)
    (hcapFitW : R7_CaptionScopeClearanceFitW exactIds idSets) :
    FlatC7B (layoutRIds exactIds idSets) := by
  intro inp o res hwf hfp hfit hsep hseam1 hseam2 h
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hrunlocal : R7_RunLocalLabelClearance exactIds idSets inp o res :=
    r7_runLocalLabelClearance_holds (inp := inp) (o := o) (res := res) hloop
      hfwd hrev
  have hparts : R7_PartsSeparated exactIds idSets inp o res :=
    r7_partsSeparated_holds (inp := inp) (o := o) (res := res) hres
  have hcaps : R7_SceneCaptionBoxContainment exactIds idSets inp o res :=
    r7_sceneCaptionBoxContainmentFitW (inp := inp) (o := o) (res := res) hwf
      hfit hcapFitW
  exact r7_layout_c7 hwf hfp hparts ⟨hrunlocal, hbridges inp o res hwf hfp⟩ hcaps h

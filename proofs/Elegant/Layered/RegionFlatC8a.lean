import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionPositionsDisjoint
import Elegant.Layered.RegionBaseExecutedValidity
import Elegant.Layered.RegionPlacement
import Elegant.Layered.RegionReduction
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactBorderChainBProof
import Elegant.Layered.ExactForeignRankPairAnchorsProof
import Elegant.Layered.ExactPlainNodePathProof
import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.ExactForeignNonGroupSpansProof
import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.RecursiveBLiftsB
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered
open RegionImpl

/-! Flat C8a for the reindexed region base. Different packed parts and
exact (`none`) runs are closed. The selected active remainder concerns only
foreign group/box pairs actually emitted by one packed part. -/

/-- The border or member hulls of two unrelated groups in a successful
active region run are separated. -/
def R8a_Separated (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {s : RegionSpec} {rm : ComponentRegions} {candidate : Nat} {cg' : Graph}
      {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    newComponentRegions (some s) P inp
      (componentCandidateR (some s) graph comp candidate) = .ok (some rm) →
    componentRunR P (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) graph comp candidate) labels orderOptions =
      .ok (cg', run) →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidateR (some s) graph comp candidate).nodes[u]? = some uNode →
    (componentCandidateR (some s) graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 →
    uNode.decl ≠ wNode.decl →
    wNode.clusterPath.contains uNode.decl = false →
    uNode.clusterPath.contains wNode.decl = false →
    (boundsOf (groupBorderRects (componentCandidateR (some s) graph comp candidate) run
        uNode.decl) []).right ≤
        (boundsOf (groupBorderRects (componentCandidateR (some s) graph comp candidate) run
          wNode.decl) []).minX ∨
      (boundsOf (groupBorderRects (componentCandidateR (some s) graph comp candidate) run
        wNode.decl) []).right ≤
        (boundsOf (groupBorderRects (componentCandidateR (some s) graph comp candidate) run
          uNode.decl) []).minX ∨
      (boundsOf (groupMemberRects (componentCandidateR (some s) graph comp candidate) run
        uNode.decl) []).bottom ≤
        (boundsOf (groupMemberRects (componentCandidateR (some s) graph comp candidate) run
          wNode.decl) []).minY ∨
      (boundsOf (groupMemberRects (componentCandidateR (some s) graph comp candidate) run
        wNode.decl) []).bottom ≤
        (boundsOf (groupMemberRects (componentCandidateR (some s) graph comp candidate) run
          uNode.decl) []).minY

/-- A group's frame is disjoint from each foreign non-group box in a
successful active region run. -/
def R8a_NonGroupClear (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {s : RegionSpec} {rm : ComponentRegions} {candidate : Nat} {cg' : Graph}
      {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    newComponentRegions (some s) P inp
      (componentCandidateR (some s) graph comp candidate) = .ok (some rm) →
    componentRunR P (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) graph comp candidate) labels orderOptions =
      .ok (cg', run) →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidateR (some s) graph comp candidate).nodes[u]? = some uNode →
    (componentCandidateR (some s) graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border ≠ -2 →
    uNode.decl ≠ wNode.decl →
    wNode.clusterPath.contains uNode.decl = false →
    uNode.clusterPath.contains wNode.decl = false →
    Disjoint (frameRect P (componentCandidateR (some s) graph comp candidate) run u)
      (frameRect P (componentCandidateR (some s) graph comp candidate) run w)

/-- The remaining plain-pair C8a obligation in one placed part of the reindexed
base: the source group was demoted by a fixed size, and its foreign plain
peer has the same executed rank but a different source parent. The selected
spec activates region placement. No pinned-layer order is assumed. -/
def R8a_DemotedGroupPlainCrossParent (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res),
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {part : List Nat × Part}, part ∈ execution.componentsAcc.parts →
    ∀ {s : RegionSpec} {rm : ComponentRegions} {candidate : Nat}
      {cg' : Graph} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int},
    newComponentRegions (some s) execution.params inp
      (componentCandidateR (some s) execution.graph part.1 candidate) = .ok (some rm) →
    componentRunR execution.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) execution.graph part.1 candidate)
      execution.measured (candidateOrder candidate) = .ok (cg', run) →
    componentLoops execution.params cg' run execution.measured = .ok loops →
    part.2 = { placeComponentExact execution.params cg' run 0 execution.measured loops with
      area := area } →
    ∀ {u w : Nat} {uNode wNode : Node} {group other : ModelBox},
    part.1[u]? = some uNode.decl →
    part.1[w]? = some wNode.decl →
    inp.boxes[uNode.decl]? = some group →
    inp.boxes[wNode.decl]? = some other →
    group.role = .group →
    inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = true →
    cg'.nodes[u]? = some uNode → cg'.nodes[w]? = some wNode →
    uNode.border = 0 → wNode.border = 0 →
    uNode.decl ≠ wNode.decl →
    wNode.clusterPath.contains uNode.decl = false →
    uNode.clusterPath.contains wNode.decl = false →
    (rk run.proper.rank u).toNat = (rk run.proper.rank w).toNat →
    group.parent ≠ other.parent →
    Disjoint (frameRect execution.params cg' run u) (frameRect execution.params cg' run w)

private abbrev r8aLayoutSpec (idSets : List (String × List String))
    (o : Options) (P : Params) (lines : List (List Measure.Line)) : Option RegionSpec :=
  if idSets.isEmpty then none
  else some (RegionSpec.mk idSets (lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)))

structure R8a_SelectedPartRun {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (part : List Nat × Part) where
  candidate : Nat
  chosen : Portfolio.Candidate (Graph × Run)
  spec : Option RegionSpec
  regions : Option ComponentRegions
  cg : Graph
  run : Run
  loops : List (Nat × LoopPlacement)
  area : Int
  candidate_bound : candidate < 5
  portfolio_eq : Portfolio.portfolio o.thoroughness
    (componentTrialR execution.params exactIds
      (r8aLayoutSpec idSets o execution.params execution.lines)
      inp o execution.graph part.1 execution.measured) = .ok chosen
  winner_eq : chosen.value = (cg, run)
  regions_eq : newComponentRegions (r8aLayoutSpec idSets o execution.params execution.lines)
    execution.params inp (componentGraph execution.graph part.1) = .ok regions
  effective_eq : spec = if regions.isSome
    then r8aLayoutSpec idSets o execution.params execution.lines else none
  run_eq : componentRunR execution.params (exactDecls exactIds inp) spec inp
    (componentCandidateR spec execution.graph part.1 candidate)
    execution.measured (candidateOrder candidate) = .ok (cg, run)
  loops_eq : componentLoops execution.params cg run execution.measured = .ok loops
  part_eq : part.2 = { placeComponentExact execution.params cg run 0 execution.measured loops with
    area := area }

def r8aSelectedTransport {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (shelf : Rect) (cg : Graph) (run : Run) (loops : List (Nat × LoopPlacement))
    (rect : Rect) : Rect :=
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH
      (shiftRect shelf.x shelf.y (shiftRect (0 - bounds.minX) (-bounds.minY) rect)))

/-- An emitted foreign group/box pair from one active selected component. -/
structure R8a_SelectedPair {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (g b : Box) where
  part : List Nat × Part
  selected : R8a_SelectedPartRun execution part
  packed : Pack.State
  shelfIndex : Nat
  shelf : Rect
  spec : RegionSpec
  u : Nat
  w : Nat
  uNode : Node
  wNode : Node
  sourceGroup : ModelBox
  sourcePeer : ModelBox
  pack_eq : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
    execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
    (LayoutConst.component_aspect_den.get o.profile)
    (execution.componentsAcc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed
  shelf_eq : (execution.componentsAcc.parts.zip packed.boxes)[shelfIndex]? = some (part, shelf)
  active : selected.spec = some spec
  group_pos : part.1[u]? = some uNode.decl
  peer_pos : part.1[w]? = some wNode.decl
  group_node : selected.cg.nodes[u]? = some uNode
  peer_node : selected.cg.nodes[w]? = some wNode
  group_source : inp.boxes[uNode.decl]? = some sourceGroup
  peer_source : inp.boxes[wNode.decl]? = some sourcePeer
  group_role : sourceGroup.role = .group
  group_emit : g = Box.mk sourceGroup.id sourceGroup.role.id
    (r8aSelectedTransport execution shelf selected.cg selected.run selected.loops
      (frameRect execution.params selected.cg selected.run u))
    sourceGroup.parent sourceGroup.exclusive
  peer_emit : b = Box.mk sourcePeer.id sourcePeer.role.id
    (r8aSelectedTransport execution shelf selected.cg selected.run selected.loops
      (frameRect execution.params selected.cg selected.run w))
    sourcePeer.parent sourcePeer.exclusive
  group_mem : g ∈ res.scene.layoutDump.boxes
  peer_mem : b ∈ res.scene.layoutDump.boxes
  foreign_id : b.id ≠ g.id
  group_not_ancestor : g.id ∉ res.scene.layoutDump.ancestors b.id
  peer_not_ancestor : b.id ∉ res.scene.layoutDump.ancestors g.id
  decl_ne : uNode.decl ≠ wNode.decl
  group_not_in_path : wNode.clusterPath.contains uNode.decl = false
  peer_not_in_path : uNode.clusterPath.contains wNode.decl = false

inductive R8a_SelectedOpenCase {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {g b : Box} (pair : R8a_SelectedPair execution g b) : Prop
  | groups (hg : pair.uNode.border = -2) (hb : pair.wNode.border = -2)
  | groupPlain (hb : (pair.uNode.border = -2 ∧ pair.wNode.border = 0) ∨
      (pair.uNode.border = 0 ∧ pair.wNode.border = -2))
  | demotedCrossParent (hg : pair.uNode.border = 0) (hb : pair.wNode.border = 0)
      (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == pair.sourceGroup.id) = true)
      (hrank : (rk pair.selected.run.proper.rank pair.u).toNat =
        (rk pair.selected.run.proper.rank pair.w).toNat)
      (hparent : pair.sourceGroup.parent ≠ pair.sourcePeer.parent)

/-- On overlapping open rows, positive-width frames need a cross-axis gap.
Empty interiors impose no gap. -/
def R8a_OverlapRowsXGap (a b : Rect) : Prop :=
  max a.y b.y < min (a.y + a.h) (b.y + b.h) → 0 < a.w → 0 < b.w →
    a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x

private theorem r8aGap_iff_disjoint (a b : Rect) :
    R8a_OverlapRowsXGap a b ↔ Disjoint a b := by
  unfold R8a_OverlapRowsXGap Disjoint Rect.meetsInterior
  constructor
  · rintro gap ⟨hx, hy⟩
    have hgap := gap hy (by omega) (by omega)
    omega
  · intro h hy hw₁ hw₂
    omega

def R8a_SelectedClearance {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (g b : Box) (pair : R8a_SelectedPair execution g b), R8a_SelectedOpenCase pair →
    R8a_OverlapRowsXGap
      (frameRect execution.params pair.selected.cg pair.selected.run pair.u)
      (frameRect execution.params pair.selected.cg pair.selected.run pair.w)

def R8a_ReindexedSelectedClearance (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
    ∀ execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res,
      R8a_SelectedClearance execution

private theorem r8aSelectedTransport_disjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (shelf : Rect) (cg : Graph) (run : Run) (loops : List (Nat × LoopPlacement))
    (a b : Rect) :
    Disjoint (r8aSelectedTransport execution shelf cg run loops a)
      (r8aSelectedTransport execution shelf cg run loops b) ↔ Disjoint a b := by
  constructor
  · intro h hm
    apply h
    cases hd : o.direction <;>
      simp only [r8aSelectedTransport, hd, Rect.meetsInterior, shiftRect, orientRect] at hm ⊢ <;>
      omega
  · intro h
    unfold r8aSelectedTransport
    exact not_meetsInterior_shiftRect (not_meetsInterior_orientRect
      (not_meetsInterior_shiftRect (not_meetsInterior_shiftRect h)))

private theorem r8a_selectedClearance_of_c8a {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (h : Validator.C8a res.scene.layoutDump) : R8a_SelectedClearance execution := by
  intro g b pair _
  have hrole : g.role = "group" := by
    rw [pair.group_emit, pair.group_role] <;> rfl
  have hclear := h g pair.group_mem hrole b pair.peer_mem pair.foreign_id
    pair.group_not_ancestor pair.peer_not_ancestor
  have hg : g.rect =
      r8aSelectedTransport execution pair.shelf pair.selected.cg pair.selected.run
        pair.selected.loops (frameRect execution.params pair.selected.cg pair.selected.run pair.u) :=
    congrArg Box.rect pair.group_emit
  have hb : b.rect =
      r8aSelectedTransport execution pair.shelf pair.selected.cg pair.selected.run
        pair.selected.loops (frameRect execution.params pair.selected.cg pair.selected.run pair.w) :=
    congrArg Box.rect pair.peer_emit
  rw [hg, hb] at hclear
  exact (r8aGap_iff_disjoint _ _).mpr ((r8aSelectedTransport_disjoint _ _ _ _ _ _ _).mp hclear)

/-- File-unique helper: a `none`-spec region run is the exact run on the
same candidate graph (via `componentRunR_none`). -/
theorem r8aC8a_runX_of_none {P : Params} {exact : List Nat} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact none inp cg labels orderOptions = .ok (cg', run)) :
    componentRunX P exact cg labels orderOptions = .ok run ∧ cg' = cg := by
  have hmap := componentRunR_none P exact inp cg labels orderOptions
  rw [hmap] at h
  cases hx : componentRunX P exact cg labels orderOptions with
  | error e =>
    simp only [hx, Except.map] at h
    cases h
  | ok r =>
    have hmap' : Except.map (fun run => (cg, run))
        (componentRunX P exact cg labels orderOptions) = .ok (cg, r) := by
      rw [hx]
      rfl
    rw [hmap'] at h
    have hpair := Except.ok.inj h
    have hcg : cg' = cg := (congrArg Prod.fst hpair).symm
    have hr : run = r := (congrArg Prod.snd hpair).symm
    subst hr
    exact ⟨rfl, hcg⟩

/-- The `none` instance of `R8a_Order`: with no region spec the candidate
coincides (`componentCandidateR_none`) and the run coincides
(`componentRunR_none`), so the exact layer-order theorem applies. This is
the replayed premise; the `some` instance (pinned layers) stays open. -/
theorem R8a_order_none_holds (exactIds : List String) :
    ∀ {P : Params} {inp : Input} {o : Options}
      {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
      {graph0 graph : Graph},
      measuredGraph P inp o lines = .ok graph0 →
      exactGraph P exactIds inp o measured graph0 = .ok graph →
      ∀ {comp : List Nat}, comp ∈ components graph →
      ∀ {candidate : Nat} {cg' : Graph} {run : Run}
        {labels : List MeasuredLabel} {orderOptions : OrderOptions},
      componentRunR P (exactDecls exactIds inp) none inp
        (componentCandidateR none graph comp candidate) labels orderOptions =
        .ok (cg', run) →
      ∀ {u w : Nat} {uNode wNode : Node},
      (componentCandidateR none graph comp candidate).nodes[u]? = some uNode →
      (componentCandidateR none graph comp candidate).nodes[w]? = some wNode →
      uNode.border = -2 → wNode.border = -2 →
      uNode.decl ≠ wNode.decl →
      wNode.clusterPath.contains uNode.decl = false →
      uNode.clusterPath.contains wNode.decl = false →
      ∀ {layer : List Nat}, layer ∈ run.layers →
      (∀ (i j a b : Nat) (na nb : ProperNode),
          layer[i]? = some a → layer[j]? = some b →
          run.coordinateProper.nodes[a]? = some na →
          run.coordinateProper.nodes[b]? = some nb →
          (na.node.border = -1 ∨ na.node.border = 1) →
          na.node.clusterPath.getLast? = some uNode.decl →
          (nb.node.border = -1 ∨ nb.node.border = 1) →
          nb.node.clusterPath.getLast? = some wNode.decl →
          i < j) ∨
      (∀ (i j a b : Nat) (na nb : ProperNode),
          layer[i]? = some a → layer[j]? = some b →
          run.coordinateProper.nodes[a]? = some na →
          run.coordinateProper.nodes[b]? = some nb →
          (na.node.border = -1 ∨ na.node.border = 1) →
          na.node.clusterPath.getLast? = some uNode.decl →
          (nb.node.border = -1 ∨ nb.node.border = 1) →
          nb.node.clusterPath.getLast? = some wNode.decl →
          j < i) := by
  intro P inp o lines measured graph0 graph hg0 hgX comp hcomp candidate cg' run
    labels orderOptions hrun u w uNode wNode hu hw hbU hbW hne hpathW hpathU layer
    hlayer
  rw [componentCandidateR_none] at hu hw hrun
  obtain ⟨hX, rfl⟩ := r8aC8a_runX_of_none hrun
  exact XB_foreignBorderLayerOrder_holds exactIds hg0 hgX hcomp hX hu hw hbU hbW
    hne hpathW hpathU hlayer

/-- The `none` instance of `R8a_Bracket`: with no region spec the run
coincides with the exact run, so the exact bracket theorem applies. This
is the replayed premise; the `some` instance (`titleReservationsR`
`border 3` titles) stays open. -/
theorem R8a_bracket_none_holds (exactIds : List String) :
    ∀ {P : Params} {inp : Input} {o : Options}
      {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
      {graph0 graph : Graph},
      measuredGraph P inp o lines = .ok graph0 →
      exactGraph P exactIds inp o measured graph0 = .ok graph →
      lines.length = inp.boxes.length →
      WellFormed (inputModel inp o) →
      framedParents inp = true →
      ∀ {comp : List Nat}, comp ∈ components graph →
      ∀ {candidate : Nat} {cg' : Graph} {run : Run}
        {labels : List MeasuredLabel} {orderOptions : OrderOptions},
      componentRunR P (exactDecls exactIds inp) none inp
        (componentCandidateR none graph comp candidate) labels orderOptions =
        .ok (cg', run) →
      ∀ {decl : Nat} (r : Nat) {low high : Nat} {lowNd highNd : ProperNode},
        run.proper.nodes[low]? = some lowNd →
        lowNd.node.clusterPath.contains decl = true →
        (rk run.proper.rank low).toNat ≤ r →
        run.proper.nodes[high]? = some highNd →
        highNd.node.clusterPath.contains decl = true →
        r ≤ (rk run.proper.rank high).toNat →
        ∃ (mL mR : Nat) (nL nR : ProperNode),
          run.coordinateProper.nodes[mL]? = some nL ∧
          nL.node.border = -1 ∧
          nL.node.clusterPath.getLast? = some decl ∧
          rk run.coordinateProper.rank mL = (r : Int) ∧
          run.coordinateProper.nodes[mR]? = some nR ∧
          nR.node.border = 1 ∧
          nR.node.clusterPath.getLast? = some decl ∧
          rk run.coordinateProper.rank mR = (r : Int) := by
  intro P inp o lines measured graph0 graph hg0 hgX hlines hwf hfp comp hcomp
    candidate cg' run labels orderOptions hrun decl r low high lowNd highNd
    hlow hcontainLow hlerk hhigh hcontainHigh hhrer
  rw [componentCandidateR_none] at hrun
  obtain ⟨hX, rfl⟩ := r8aC8a_runX_of_none hrun
  exact XN_bracketMarkersAtRank_holds exactIds hg0 hgX hlines hwf hfp hcomp hX r
    hlow hcontainLow hlerk hhigh hcontainHigh hhrer

/-- File-unique inhabited fallback for `getD` on model boxes. -/
local instance r8aC8aInhabitedModelBox : Inhabited ModelBox := ⟨{ id := "" }⟩

/-- File-unique copy of `getElem_unique_of_nodup_map`. -/
private theorem r8aC8a_getElem_unique_of_nodup_map {α : Type} {f : α → String}
    {l : List α} (hnd : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hid : f x = f y) : x = y := by
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, hyj⟩ := List.mem_iff_getElem.mp hy
  by_cases hij : i = j
  · subst hij
    exact hxi.symm.trans hyj
  · exfalso
    have hp := List.pairwise_iff_getElem.mp hnd
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · have h := hp i j (by simpa using hi) (by simpa using hj) hlt
      exact h (by simp only [List.getElem_map, hxi, hyj, hid])
    · exact absurd heq hij
    · have h := hp j i (by simpa using hj) (by simpa using hi) hgt
      exact h (by simp only [List.getElem_map, hyj, hxi, ← hid])

/-- File-unique copy of `demote_id_parent`. -/
private theorem r8aC8a_demote_id_parent (inp : Input) (b : ModelBox) :
    (if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b).id = b.id ∧
      (if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b).parent = b.parent := by
  split <;> simp

/-- File-unique copy: `Disjoint` survives `shiftRect`. -/
private theorem r8aC8a_shiftRect_disjoint {a b : Rect} {dx dy : Int}
    (h : Disjoint a b) : Disjoint (shiftRect dx dy a) (shiftRect dx dy b) := by
  simp only [Disjoint, Rect.meetsInterior, shiftRect] at h ⊢
  omega

/-- File-unique copy: `Disjoint` survives `orientRect`. -/
private theorem r8aC8a_orientRect_disjoint {a b : Rect} {d : Direction} {h : Int}
    (hm : Disjoint a b) : Disjoint (orientRect d h a) (orientRect d h b) := by
  intro hc
  exact hm (meetsInterior_of_orientRect hc)

/-- File-unique copies: `zipIdx` preserves the first projection. -/
private theorem r8aC8a_zipIdxAux_map_fst {α : Type} (l : List α) (n : Nat) :
    (l.zipIdx n).map Prod.fst = l := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.map_cons, ih]
private theorem r8aC8a_zipIdx_map_fst {α : Type} (l : List α) :
    l.zipIdx.map Prod.fst = l := by
  have h := r8aC8a_zipIdxAux_map_fst l 0
  simpa only using h

/-- File-unique copy: id-injective lookup for dump boxes. -/
private theorem r8aC8a_eq_of_mem_idBox {boxes : List Box}
    (hnodup : (boxes.map (·.id)).Nodup) {a b : Box} (ha : a ∈ boxes)
    (hb : b ∈ boxes) (h : a.id = b.id) : a = b := by
  induction boxes generalizing a b with
  | nil => cases ha
  | cons c l ih =>
    rcases List.mem_cons.mp ha with rfl | hal
    · rcases List.mem_cons.mp hb with rfl | hbl
      · rfl
      · exact absurd (List.mem_map.mpr ⟨b, hbl, h.symm⟩) (List.nodup_cons.mp hnodup).1
    · rcases List.mem_cons.mp hb with rfl | hbl
      · exact absurd (List.mem_map.mpr ⟨a, hal, h⟩) (List.nodup_cons.mp hnodup).1
      · exact ih (List.nodup_cons.mp hnodup).2 hal hbl h

/-- File-unique copy of the ancestor-walk bridge: a strict model ancestor
index is an id of the dump ancestor walk. -/
private theorem r8aC8a_compound_mem_dump_go {boxes : List ModelBox} {d : LayoutDump}
    (himg : ∀ (i : Nat) (b : ModelBox), boxes[i]? = some b →
      ∃ (rect : Rect) (role : String),
        d.box? b.id = some (Box.mk b.id role rect b.parent b.exclusive)) :
    ∀ (fuel : Nat) (s : String) (i : Nat),
      i ∈ Compound.ancestors boxes (fuel + 1) s →
      i < boxes.length →
      (boxes[i]?.getD default).id ≠ s →
      (boxes[i]?.getD default).id ∈ LayoutDump.ancestors.go d fuel s := by
  intro fuel
  induction fuel with
  | zero =>
    intro s i hmem hi hne
    by_cases hs : s = ""
    · subst hs
      simp only [Compound.ancestors] at hmem
      exact absurd hmem (by simp)
    · have h3 : Compound.ancestors boxes (0 + 1) s =
          match boxes.findIdx? (fun box => box.id == s) with
        | none => []
        | some index =>
          match boxes[index]? with
          | none => []
          | some box => Compound.ancestors boxes 0 box.parent ++ [index] :=
        Compound.ancestors.eq_3 boxes s 0 hs
      rw [h3] at hmem
      cases hf : boxes.findIdx? (fun box => box.id == s) with
      | none => simp only [hf] at hmem; exact absurd hmem (by simp)
      | some j =>
        obtain ⟨hjb, hjid, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        simp only [hf] at hmem
        cases hb : boxes[j]? with
        | none => simp only [hb] at hmem; exact absurd hmem (by simp)
        | some bj =>
          obtain ⟨_, hbjEq⟩ := List.getElem?_eq_some_iff.mp hb
          simp only [hb] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · simp only [Compound.ancestors] at hmem
            exact absurd hmem (by simp)
          · rw [hmem] at hne
            have hgd : boxes[j]?.getD default = bj := by rw [hb]; rfl
            have hjid2 : bj.id = s := by
              rw [← hbjEq]
              exact beq_iff_eq.mp hjid
            exact absurd ((congrArg (·.id) hgd).trans hjid2) hne
  | succ fuel ih =>
    intro s i hmem hi hne
    by_cases hs : s = ""
    · subst hs
      simp only [Compound.ancestors] at hmem
      exact absurd hmem (by simp)
    · have h3 : Compound.ancestors boxes (fuel + 1 + 1) s =
          match boxes.findIdx? (fun box => box.id == s) with
        | none => []
        | some index =>
          match boxes[index]? with
          | none => []
          | some box => Compound.ancestors boxes (fuel + 1) box.parent ++ [index] :=
        Compound.ancestors.eq_3 boxes s (fuel + 1) hs
      rw [h3] at hmem
      cases hf : boxes.findIdx? (fun box => box.id == s) with
      | none => simp only [hf] at hmem; exact absurd hmem (by simp)
      | some j =>
        obtain ⟨_, hjid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        simp only [hf] at hmem
        cases hb : boxes[j]? with
        | none => simp only [hb] at hmem; exact absurd hmem (by simp)
        | some bj =>
          obtain ⟨_, hbjEq⟩ := List.getElem?_eq_some_iff.mp hb
          simp only [hb] at hmem
          have hjids : bj.id = s := by
            rw [← hbjEq]
            exact beq_iff_eq.mp hjid
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · obtain ⟨rect, role, excl, hbx⟩ : ∃ (rect : Rect) (role : String)
                (excl : Bool), d.box? s = some (Box.mk s role rect bj.parent excl) := by
              obtain ⟨rect, role, hx⟩ := himg j bj hb
              rw [hjids] at hx
              exact ⟨rect, role, bj.exclusive, hx⟩
            have hparNe : bj.parent ≠ "" := by
              intro hempty
              simp only [hempty, Compound.ancestors] at hmem
              exact absurd hmem (by simp)
            cases hd : d.box? s with
            | none => rw [hd] at hbx; exact absurd hbx (by simp)
            | some bx =>
              have hbxa : bx = Box.mk s role rect bj.parent excl :=
                Option.some.inj (hd.symm.trans hbx)
              have hbpar : bx.parent = bj.parent := by rw [hbxa]
              have hgo : LayoutDump.ancestors.go d (fuel + 1) s =
                  match d.box? s with
                  | none => []
                  | some bx' =>
                    if bx'.parent = "" then []
                    else bx'.parent :: LayoutDump.ancestors.go d fuel bx'.parent := rfl
              rw [hgo]
              simp only [hd, hbpar]
              split
              · rename_i hcond
                exact absurd hcond hparNe
              · by_cases hself : (boxes[i]?.getD default).id = bj.parent
                · rw [hself]
                  exact List.mem_cons_self
                · exact List.mem_cons.mpr (Or.inr (ih bj.parent i hmem hi hself))
          · rw [hmem] at hne
            have hgd : boxes[j]?.getD default = bj := by rw [hb]; rfl
            exact absurd ((congrArg (·.id) hgd).trans hjids) hne

/-- File-unique copy of the dump-ancestry transport. -/
private theorem r8aC8a_anc_of_path_mem {boxes : List ModelBox} {d : LayoutDump}
    (himg : ∀ (i : Nat) (b : ModelBox), boxes[i]? = some b →
      ∃ (rect : Rect) (role : String),
        d.box? b.id = some (Box.mk b.id role rect b.parent b.exclusive))
    (_hpre : ∀ bx : Box, bx ∈ d.boxes →
      ∃ b : ModelBox, b ∈ boxes ∧ b.id = bx.id ∧ b.parent = bx.parent)
    (_hid : ∀ (a b : ModelBox), a ∈ boxes → b ∈ boxes → a.id = b.id → a = b)
    (_hlen : d.boxes.length = boxes.length)
    {t p : String} {idx : Nat} {s : String}
    (hroot : ∃ (role : String) (rect : Rect) (excl : Bool),
      d.box? t = some (Box.mk t role rect p excl))
    (hidx : idx < boxes.length)
    (hs : (boxes[idx]?.getD default).id = s)
    (hmem : idx ∈ Compound.ancestors boxes boxes.length p) :
    s ∈ d.ancestors t := by
  cases hlen' : boxes.length with
  | zero => rw [hlen'] at hidx; exact absurd hidx (by omega)
  | succ fuel =>
    obtain ⟨role, rect, excl, hroot⟩ := hroot
    rw [hlen'] at hmem
    have hlenSucc : d.boxes.length = fuel + 1 := by rw [_hlen, hlen']
    have hgo : LayoutDump.ancestors.go d (fuel + 1) t =
        match d.box? t with
        | none => []
        | some bx =>
          if bx.parent = "" then [] else bx.parent :: LayoutDump.ancestors.go d fuel bx.parent :=
      rfl
    rw [LayoutDump.ancestors, hlenSucc, hgo]
    cases hd : d.box? t with
    | none => rw [hd] at hroot; exact absurd hroot (by simp)
    | some bx =>
      have hbxa : bx = Box.mk t role rect p excl :=
        Option.some.inj (hd.symm.trans hroot)
      have hbpar : bx.parent = p := by rw [hbxa]
      simp only [hbpar]
      split
      · rename_i hcond
        rw [hcond] at hmem
        simp only [Compound.ancestors] at hmem
        exact absurd hmem (by simp)
      · by_cases hself : (boxes[idx]?.getD default).id = p
        · rw [← hs, hself]
          exact List.mem_cons_self
        · have hgo2 := r8aC8a_compound_mem_dump_go himg fuel p idx hmem hidx hself
          rw [hs] at hgo2
          exact List.mem_cons.mpr (Or.inr hgo2)

/-- The exact graph node behind a source box, including the declaration
index and effective ancestor path. A plain record for a source group
identifies a fixed-size demotion. -/
private theorem r8aC8a_measuredGraphNodeX {exactIds : List String} {P : Params}
    {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {g0 g : Graph}
    (h0 : measuredGraph P inp o lines = .ok g0)
    (hg : exactGraph P exactIds inp o measured g0 = .ok g)
    (hlen : lines.length = inp.boxes.length)
    {eff : List ModelBox}
    (heff : eff = inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b)
    {k : Nat} {s : ModelBox} {sg : ModelBox}
    (hk : inp.boxes[k]? = some s)
    (hsg : eff[k]? = some sg) :
    ∃ node : Node,
      g.nodes[k]? = some node ∧
      node.decl = k ∧
      ((node.border = -2 ∧ node.clusterPath = Compound.path eff sg ++ [k]) ∨
        (node.border = 0 ∧ node.clusterPath = Compound.path eff sg ∧
          (s.role = .group → inp.fixedSizes.any (fun fixed => fixed.1 == s.id) = true))) := by
  obtain ⟨nodes, edges, titles, hprepared, hnodesLen, hmeta⟩ :=
    measuredGraph_prepared_source h0
  have hkLen : k < lines.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hk).1
  have hkNodes : k < nodes.length := by rw [hnodesLen]; exact hkLen
  obtain ⟨hn0decl, hn0border⟩ := hmeta k nodes[k] (List.getElem?_eq_getElem hkNodes)
  rw [heff] at hsg
  by_cases hrole : sg.role = .group
  · have hrec := Compound.prepare_group_title_record
      (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b)
      P.clusterPad titles ⟨nodes, edges, P.slot⟩ hkNodes hsg hrole
    have hget0 : g0.nodes[k]? = some { nodes[k]'hkNodes with clusterPath := Compound.path (inp.boxes.map fun b => if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then { b with role := .node } else b) sg ++ [k], border := -2, w := (titles.getD k (0, 0)).1, h := if nodes[k].loopExtent == 0 then (titles.getD k (0, 0)).2 + P.clusterPad else max ((titles.getD k (0, 0)).2 + P.clusterPad) nodes[k].h } := by
      rw [hprepared]
      exact hrec
    obtain ⟨nd, hnd, hbEq, hcEq, hdeclEq⟩ := exactGraph_node_key hg hget0
    refine ⟨nd, hnd, ?_, Or.inl ⟨?_, ?_⟩⟩
    · simp [hdeclEq, hn0decl]
    · simp [hbEq]
    · simp [hcEq]
      rw [← heff]
  · have hrec := Compound.prepare_plain_node_record
      (inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b)
      P.clusterPad titles ⟨nodes, edges, P.slot⟩ hkNodes hsg hrole
    have hget0 : g0.nodes[k]? = some { nodes[k]'hkNodes with clusterPath := Compound.path (inp.boxes.map fun b => if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then { b with role := .node } else b) sg } := by
      rw [hprepared]
      exact hrec
    obtain ⟨nd, hnd, hbEq, hcEq, hdeclEq⟩ := exactGraph_node_key hg hget0
    refine ⟨nd, hnd, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · simp [hdeclEq, hn0decl]
    · simp [hbEq, hn0border]
    · simp [hcEq]
      rw [← heff]
    · intro hgroup
      by_cases hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == s.id) = true
      · exact hfixed
      · have hsame : s = sg := by
          simpa only [List.getElem?_map, hk, Option.map_some, ite_eq_right hfixed,
            Option.some.injEq] using hsg
        exact False.elim (hrole (hsame ▸ hgroup))

/-- A part index below the executed parts is below the packed shelf boxes
(region copy of the flat helper). -/
private theorem r8aC8a_partPackedBoxLenR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {part : List Nat × Part}
    (hk : execution.componentsAcc.parts[k]? = some part) :
    k < packed.boxes.length := by
  have hkbl : k < execution.componentsAcc.parts.length :=
    (List.getElem?_eq_some_iff.mp hk).1
  have hcount := Pack.pack_count hpack
  rw [hcount, List.length_map]
  exact hkbl

/-- The region candidate keeps the component nodes (length form). -/
private theorem r8aC8a_candidateRLen (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec g comp index).nodes.length = comp.length := by
  cases spec with
  | none =>
    show (componentCandidate g comp index).nodes.length = comp.length
    rw [componentCandidate_nodes]
    show (comp.map fun v => g.nodes.getD v default).length = comp.length
    exact List.length_map ..
  | some _ =>
    unfold componentCandidateR componentGraph
    dsimp only
    exact List.length_map ..

/-- Packed shelf box dims follow the part item dims (region copy). -/
private theorem r8aC8a_packBoxDims {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out)
    {k : Nat} (hk : k < out.boxes.length) (hik : k < items.length) :
    out.boxes[k].w = items[k].width ∧ out.boxes[k].h = items[k].height := by
  have hd := Pack.pack_dimensions h
  unfold Pack.dimensions at hd
  have h1 := congrArg (fun l => l[k]?) hd
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hik] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  exact h1

/-- The chosen component run of one executed part, with its placement
equation and the resolved regions of a selected `some` spec. -/
private theorem r8aC8a_partPackedRunR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {k : Nat} {part : List Nat × Part}
    (hk : execution.componentsAcc.parts[k]? = some part) :
    Nonempty (R8a_SelectedPartRun execution part) := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨_, hall⟩ :=
    actual_components_parts_geometryR hempty execution.components_eq
  have hmem : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hk
  obtain ⟨index, chosen, cg, run, loops, area, spec, hindex, hportfolio, hwinner,
    ⟨regions, hregions, heffective⟩, hrun, hloops, hpart⟩ := hall part hmem
  exact ⟨⟨index, chosen, spec, regions, cg, run, loops, area, hindex, hportfolio,
    hwinner, hregions, heffective, hrun, hloops, hpart⟩⟩

/-- For one executed region part at pack index `k`: every member frame rect of
the part is contained in the part's packed shelf box, and the packed
accumulator stores exactly the placed frame (region copy of
`X_part_packed_frame`; frames are over the rewritten graph `cg'` that
`componentRunR` returns). -/
private theorem r8aC8a_partPackedFrameR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {part : List Nat × Part}
    (hk : execution.componentsAcc.parts[k]? = some part)
    (hkLen : k < packed.boxes.length) :
    ∃ selected : R8a_SelectedPartRun execution part,
      (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
        packed.boxes[k].Contained (shiftRect packed.boxes[k].x packed.boxes[k].y
          (shiftRect (0 - (placeBoundsX execution.params selected.cg selected.run
              execution.measured selected.loops).minX)
            (-(placeBoundsX execution.params selected.cg selected.run
              execution.measured selected.loops).minY)
            (frameRect execution.params selected.cg selected.run i)))) ∧
      (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
        execution.packedAcc.rects.getD key default =
          shiftRect packed.boxes[k].x packed.boxes[k].y
            (shiftRect (0 - (placeBoundsX execution.params selected.cg selected.run
                execution.measured selected.loops).minX)
              (-(placeBoundsX execution.params selected.cg selected.run
                execution.measured selected.loops).minY)
              (frameRect execution.params selected.cg selected.run i))) := by
  obtain ⟨selected⟩ := r8aC8a_partPackedRunR execution hk
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  have hbox : packed.boxes[k]? = some packed.boxes[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? =
      some (part, packed.boxes[k]) :=
    List.getElem?_zip_eq_some.mpr ⟨hk, hbox⟩
  have hplacedAt : ∀ (i key : Nat), part.1[i]? = some key →
      (placeComponentExact execution.params selected.cg selected.run 0 execution.measured
        selected.loops).rects[i]? =
      some (shiftRect (0 - (placeBoundsX execution.params selected.cg selected.run
          execution.measured selected.loops).minX)
        (-(placeBoundsX execution.params selected.cg selected.run
          execution.measured selected.loops).minY)
        (frameRect execution.params selected.cg selected.run i)) := by
    intro i key hkey
    have hilt : i < part.1.length := (List.getElem?_eq_some_iff.mp hkey).1
    have hcl : (componentCandidateR selected.spec execution.graph part.1
        selected.candidate).nodes.length = part.1.length := r8aC8a_candidateRLen _ _ _ _
    have hrl : selected.cg.nodes.length = (componentCandidateR selected.spec execution.graph
        part.1 selected.candidate).nodes.length := componentRunR_nodes_eq selected.run_eq
    have hi : i < selected.cg.nodes.length := by omega
    unfold placeComponentExact placeBoundsX
    simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
  refine ⟨selected, ?_, ?_⟩
  · intro i key hkey hkeyLen
    have hpartget := (List.getElem?_eq_some_iff.mp hk).2
    have hmapLen : k < (execution.componentsAcc.parts.map
        (fun part => Pack.Item.mk part.2.width part.2.height part.2.area)).length := by
      rw [List.length_map]
      exact (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨hw0, hh0⟩ := r8aC8a_packBoxDims hpack hkLen hmapLen
    have hitem : (execution.componentsAcc.parts.map
        (fun part => Pack.Item.mk part.2.width part.2.height part.2.area))[k] =
        Pack.Item.mk part.2.width part.2.height part.2.area := by
      rw [List.getElem_map, hpartget]
    have hwb : packed.boxes[k].w = part.2.width := by
      rw [hw0, hitem]
    have hhb : packed.boxes[k].h = part.2.height := by
      rw [hh0, hitem]
    have hwlink : part.2.width =
        (placeComponentExact execution.params selected.cg selected.run 0 execution.measured
          selected.loops).width := by
      have hcongr := congrArg Part.width selected.part_eq
      simpa using hcongr
    have hhlink : part.2.height =
        (placeComponentExact execution.params selected.cg selected.run 0 execution.measured
          selected.loops).height := by
      have hcongr := congrArg Part.height selected.part_eq
      simpa using hcongr
    have hmem := List.mem_of_getElem? (hplacedAt i key hkey)
    have hb := placeComponentExact_rects_bounds execution.params selected.cg selected.run 0
      execution.measured selected.loops _ hmem
    simp only [Rect.Contained, shiftRect] at hb ⊢
    rw [hwb, hhb, hwlink, hhlink]
    omega
  · intro i key hkey hkeyLen
    have hsize : key < execution.componentsAcc.rects.size := by
      rw [execution.components_rects_sizeR]; exact hkeyLen
    have hplaced := hplacedAt i key hkey
    have hrectpart : part.2.rects[i]? =
        some (shiftRect (0 - (placeBoundsX execution.params selected.cg selected.run
          execution.measured selected.loops).minX)
        (-(placeBoundsX execution.params selected.cg selected.run
          execution.measured selected.loops).minY)
        (frameRect execution.params selected.cg selected.run i)) := by
      rw [selected.part_eq]; exact hplaced
    have hentry : ((part, packed.boxes[k]).1.1.zip
        (part, packed.boxes[k]).1.2.rects)[i]? =
        some (key, shiftRect (0 - (placeBoundsX execution.params selected.cg selected.run
          execution.measured selected.loops).minX)
          (-(placeBoundsX execution.params selected.cg selected.run
            execution.measured selected.loops).minY)
          (frameRect execution.params selected.cg selected.run i)) :=
      List.getElem?_zip_eq_some.mpr ⟨hkey, hrectpart⟩
    exact actual_components_packed_rect_valueR hempty execution.components_eq
      execution.packed_eq packed hpack hselected hentry hsize default

/-- Clearance of a foreign frame pair in the exact run used by a `none`
part of the selected region execution. -/
theorem r8aC8a_clear_none {exactIds : List String}
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hg0 : measuredGraph P inp o lines = .ok graph0)
    (hgX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {u w : Nat} {uNode wNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hw : (componentCandidate graph comp candidate).nodes[w]? = some wNode)
    (hgroupU : uNode.border = -2) (hne : uNode.decl ≠ wNode.decl)
    (hpathW : wNode.clusterPath.contains uNode.decl = false)
    (hpathU : uNode.clusterPath.contains wNode.decl = false) :
    Disjoint (frameRect P (componentCandidate graph comp candidate) run u)
      (frameRect P (componentCandidate graph comp candidate) run w) := by
  have hchain : X_ForeignBorderChainXAligned exactIds :=
    @X_foreignBorderChainXAligned_framed exactIds
  have hgroupsX : XB_ForeignBorderSpansSeparated exactIds :=
    XB_foreignBorderSpansSeparated_holds exactIds
      (XB_foreignClusterRankSpans_holds exactIds (XB_foreignRankPairAnchors_holds exactIds))
      (XB_foreignBorderLayerOrder_holds exactIds) hchain
      (XB_orderedIntervals_holds exactIds) (XB_topNonneg_holds exactIds)
      (XB_memberNonempty_holds exactIds)
  have hothersX : XN_ForeignNonGroupSpansClear exactIds :=
    XN_foreignNonGroupSpansClear_holds exactIds
      (XN_bracketMarkersAtRank_holds exactIds)
      (XN_plainClearOfSideMarker_of_path exactIds (XN_plainNodePathResidual_holds exactIds))
      (XN_sideMarkerSpanAligned_of_chain exactIds hchain)
  by_cases hgroupW : wNode.border = -2
  · exact frameRect_disjoint_of_hulls hu hgroupU hw hgroupW
      (hgroupsX hg0 hgX hlines hwf hfp hcomp hrunX hu hw hgroupU hgroupW hne
        hpathW hpathU)
  · exact hothersX hg0 hgX hlines hwf hfp hcomp hrunX hu hw hgroupU hgroupW hne
      hpathW hpathU

/-- Same-part clearance in an active region run. -/
private theorem r8aC8a_clear_some {exactIds : List String}
    (hSep : R8a_Separated exactIds) (hNonGroup : R8a_NonGroupClear exactIds)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hg0 : measuredGraph P inp o lines = .ok graph0)
    (hgX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {s : RegionSpec} {rm : ComponentRegions} {candidate : Nat} {cg' : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hactive : newComponentRegions (some s) P inp
      (componentCandidateR (some s) graph comp candidate) = .ok (some rm))
    (hrunR : componentRunR P (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) graph comp candidate) labels orderOptions =
      .ok (cg', run))
    {u w : Nat} {uNode wNode : Node}
    (hu : (componentCandidateR (some s) graph comp candidate).nodes[u]? = some uNode)
    (hw : (componentCandidateR (some s) graph comp candidate).nodes[w]? = some wNode)
    (hgroupU : uNode.border = -2) (hne : uNode.decl ≠ wNode.decl)
    (hpathW : wNode.clusterPath.contains uNode.decl = false)
    (hpathU : uNode.clusterPath.contains wNode.decl = false) :
    Disjoint (frameRect P (componentCandidateR (some s) graph comp candidate) run u)
      (frameRect P (componentCandidateR (some s) graph comp candidate) run w) := by
  by_cases hgroupW : wNode.border = -2
  · exact frameRect_disjoint_of_hulls hu hgroupU hw hgroupW
      (hSep hg0 hgX hlines hwf hfp hcomp hactive hrunR hu hw hgroupU hgroupW hne
        hpathW hpathU)
  · exact hNonGroup hg0 hgX hlines hwf hfp hcomp hactive hrunR hu hw hgroupU hgroupW hne
      hpathW hpathU

/-- File-unique congruence: `frameRect` follows the node list. Used to move
span disjointness between the rewritten graph `cg'` and the candidate graph
(their node lists coincide by `componentRunR_nodes_eq` /
`rankEquivalentR_nodes_eq`). -/
private theorem r8aC8a_frameRect_congr {P : Params} {cg cg' : Graph} {run : Run}
    {i : Nat} (h : cg'.nodes = cg.nodes) :
    frameRect P cg' run i = frameRect P cg run i := by
  unfold frameRect nodeRect
  rw [h]

/-- Candidate and rewritten selected graphs differ only in edges. -/
private theorem r8aC8a_run_nodesR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    cg'.nodes = cg.nodes := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages h
  rcases stages.hRank with ⟨_, _, _, _, heq, _⟩ | ⟨_, _, hranked⟩
  · rw [heq]
  · exact rankEquivalentR_nodes_eq hranked

/-- Exact and already-separated pairs need no selected geometry premise. -/
theorem r8a_c8a_of_selectedClearance {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (clearance : R8a_SelectedClearance execution) :
    Validator.C8a res.scene.layoutDump := by
  have hboxesEq : res.scene.layoutDump.boxes = (inp.boxes.zipIdx.map fun q =>
      Box.mk q.1.id q.1.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD q.2 default)))
        q.1.parent q.1.exclusive) := by
    have h := execution.boxes_eq_mapR
    simp [Scene.layoutDump] at h ⊢
    exact h
  have hlen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    simp only [boxLines] at hl
    have h2 := (mapM_getElem? _ _ _ hl).1
    have hzip : (inp.boxes.zipIdx).length = inp.boxes.length := List.length_zipIdx
    omega
  have hpartsMap : execution.componentsAcc.parts.map (·.1) = components execution.graph :=
    (actual_components_parts_geometryR (by rfl) execution.components_eq).1
  have hidsNodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  let eff : List ModelBox := inp.boxes.map fun b =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
      { b with role := .node } else b
  have heff : eff = inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b := rfl
  have heffLen : eff.length = inp.boxes.length := by rw [heff, List.length_map]
  have heffGet : ∀ (k : Nat), eff[k]? =
      (inp.boxes[k]?).map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b := by
    intro k
    rw [heff, List.getElem?_map]
  have heffNodup : (eff.map (·.id)).Nodup := by
    have hcongr : eff.map (·.id) = inp.boxes.map (·.id) := by
      rw [heff, List.map_map]
      congr 1
      funext b
      exact (r8aC8a_demote_id_parent inp b).1
    rw [hcongr]
    exact hidsNodup
  have heffUnique : ∀ (a b : ModelBox), a ∈ eff → b ∈ eff → a.id = b.id → a = b :=
    fun a b ha hb hid => r8aC8a_getElem_unique_of_nodup_map heffNodup ha hb hid
  have hidsDumpNodup : (res.scene.layoutDump.boxes.map (·.id)).Nodup := by
    have hcongr : (res.scene.layoutDump.boxes.map (·.id)) = inp.boxes.map (·.id) := by
      rw [hboxesEq, List.map_map]
      simp only [Function.comp_def]
      have heq : (fun q : ModelBox × Nat => q.1.id) = (·.id) ∘ Prod.fst := by
        funext q
        rfl
      rw [heq, ← List.map_map, r8aC8a_zipIdx_map_fst]
    rw [hcongr]
    exact hidsNodup
  have himg : ∀ (k : Nat) (b : ModelBox), eff[k]? = some b →
      ∃ (rect : Rect) (role : String),
        res.scene.layoutDump.box? b.id =
          some (Box.mk b.id role rect b.parent b.exclusive) := by
    intro k b hib
    cases hin : inp.boxes[k]? with
    | none => rw [heffGet, hin] at hib; exact absurd hib (by simp)
    | some orig =>
      rw [heffGet, hin] at hib
      have hbEq : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
          { orig with role := .node } else orig) = b := Option.some.inj hib
      subst hbEq
      obtain ⟨h1, h2⟩ := r8aC8a_demote_id_parent inp orig
      have h3 : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
          { orig with role := .node } else orig).exclusive = orig.exclusive := by
        split <;> rfl
      rw [h1, h2, h3]
      have hmemZip : (orig, k) ∈ inp.boxes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hin
      have hmemBox : (Box.mk orig.id orig.role.id
          (shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (execution.packedAcc.rects.getD k default)))
          orig.parent orig.exclusive) ∈ res.scene.layoutDump.boxes := by
        rw [hboxesEq]
        exact List.mem_map.mpr ⟨(orig, k), hmemZip, rfl⟩
      have hbeq : ((Box.mk orig.id orig.role.id
            (shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH
                (execution.packedAcc.rects.getD k default)))
            orig.parent orig.exclusive).id == orig.id) = true := by
        simp
      have hsome : ((res.scene.layoutDump.boxes.find? fun b => b.id == orig.id).isSome =
          true) :=
        List.find?_isSome.mpr ⟨_, hmemBox, hbeq⟩
      cases hfind : res.scene.layoutDump.boxes.find? fun b => b.id == orig.id with
      | none => rw [hfind] at hsome; simp at hsome
      | some bx =>
        have hbxMem : bx ∈ res.scene.layoutDump.boxes :=
          List.mem_of_find?_eq_some hfind
        have hbxId : (bx.id == orig.id) = true := by
          have h := List.find?_some hfind
          simpa using h
        have hbxEq : (bx.id = orig.id) := beq_iff_eq.mp hbxId
        have huniq := r8aC8a_eq_of_mem_idBox hidsDumpNodup hmemBox hbxMem
          (by rw [hbxEq])
        rw [← huniq] at hfind
        exact ⟨_, _, hfind⟩
  have hpre : ∀ bx : Box, bx ∈ res.scene.layoutDump.boxes →
      ∃ b : ModelBox, b ∈ eff ∧ b.id = bx.id ∧ b.parent = bx.parent := by
    intro bx hbx
    rw [hboxesEq] at hbx
    obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hbx
    have hk : inp.boxes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
    cases hin : inp.boxes[q.2]? with
    | none => rw [hin] at hk; exact absurd hk (by simp)
    | some s =>
      rw [hin] at hk
      have hsq : s = q.1 := Option.some.inj hk
      subst hsq
      have hkIn : eff[q.2]? = some
          (if inp.fixedSizes.any (fun fixed => fixed.1 == q.1.id) then
            { q.1 with role := .node } else q.1) := by
        rw [heffGet, hin, Option.map_some]
      refine ⟨_, List.mem_of_getElem? hkIn, ?_, ?_⟩
      · have hbx : bx.id = q.1.id := by rw [← hqeq]
        rw [hbx]
        exact (r8aC8a_demote_id_parent inp q.1).1
      · have hbx : bx.parent = q.1.parent := by rw [← hqeq]
        rw [hbx]
        exact (r8aC8a_demote_id_parent inp q.1).2
  have hdlen : res.scene.layoutDump.boxes.length = inp.boxes.length := by
    rw [hboxesEq, List.length_map, List.length_zipIdx]
  have hdlen' : res.scene.layoutDump.boxes.length = eff.length := by
    rw [heffLen]
    exact hdlen
  intro g hgMem hrole b hbMem hbId hgAnc hbAnc
  have hgMemDump := hgMem
  have hbMemDump := hbMem
  have hgAncDump := hgAnc
  have hbAncDump := hbAnc
  obtain ⟨sg, bi, hbi, hgeq⟩ : ∃ (s : ModelBox) (k : Nat), inp.boxes[k]? = some s ∧
      g = Box.mk s.id s.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD k default)))
        s.parent s.exclusive := by
    rw [hboxesEq] at hgMem
    obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hgMem
    exact ⟨q.1, q.2, List.mem_zipIdx_iff_getElem?.mp hq, hqeq.symm⟩
  obtain ⟨sb, bk, hbk, hbeq⟩ : ∃ (s : ModelBox) (k : Nat), inp.boxes[k]? = some s ∧
      b = Box.mk s.id s.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD k default)))
        s.parent s.exclusive := by
    rw [hboxesEq] at hbMem
    obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hbMem
    exact ⟨q.1, q.2, List.mem_zipIdx_iff_getElem?.mp hq, hqeq.symm⟩
  have hgId : g.id = sg.id := by rw [hgeq]
  have hbIdEq : b.id = sb.id := by rw [hbeq]
  have hgRect : g.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD bi default)) := by rw [hgeq]
  have hbRect : b.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD bk default)) := by rw [hbeq]
  have hbid : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hbi).1
  have hbkBound : bk < inp.boxes.length := (List.getElem?_eq_some_iff.mp hbk).1
  have hbik : bi ≠ bk := by
    intro heq
    rw [heq] at hbi
    exact hbId (by rw [hbIdEq, hgId, ← Option.some.inj (hbi.symm.trans hbk)])
  rw [hgId, hbIdEq] at hgAnc hbAnc
  have heffIdOf : ∀ (k : Nat) (s : ModelBox), inp.boxes[k]? = some s →
      (eff[k]?.getD default).id = s.id ∧ (eff[k]?.getD default).parent = s.parent := by
    intro k s hk
    rw [heffGet, hk]
    simp only [Option.map_some, Option.getD_some]
    exact r8aC8a_demote_id_parent inp s
  have hrootT1 : ∃ (role : String) (rect : Rect) (excl : Bool),
      res.scene.layoutDump.box? sb.id =
        some (Box.mk sb.id role rect sb.parent excl) := by
    obtain ⟨rect, role, hx⟩ := himg bk
      (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
        { sb with role := .node } else sb)
      (by rw [heffGet, hbk, Option.map_some])
    obtain ⟨h1, h2⟩ := r8aC8a_demote_id_parent inp sb
    rw [h1, h2] at hx
    exact ⟨role, rect, _, hx⟩
  have hrootT2 : ∃ (role : String) (rect : Rect) (excl : Bool),
      res.scene.layoutDump.box? sg.id =
        some (Box.mk sg.id role rect sg.parent excl) := by
    obtain ⟨rect, role, hx⟩ := himg bi
      (if inp.fixedSizes.any (fun fixed => fixed.1 == sg.id) then
        { sg with role := .node } else sg)
      (by rw [heffGet, hbi, Option.map_some])
    obtain ⟨h1, h2⟩ := r8aC8a_demote_id_parent inp sg
    rw [h1, h2] at hx
    exact ⟨role, rect, _, hx⟩
  have hnotInPathB : bi ∉ Compound.path eff
      (if inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) then
        { sb with role := .node } else sb) := by
    intro hmem
    have hmemA : bi ∈ Compound.ancestors eff eff.length sb.parent := by
      unfold Compound.path at hmem
      split at hmem <;> exact hmem
    exact hgAnc (r8aC8a_anc_of_path_mem himg hpre heffUnique hdlen' hrootT1
      (by rw [heffLen]; exact hbid) (heffIdOf bi sg hbi).1 hmemA)
  have hnotInPathG : bk ∉ Compound.path eff
      (if inp.fixedSizes.any (fun fixed => fixed.1 == sg.id) then
        { sg with role := .node } else sg) := by
    intro hmem
    have hmemA : bk ∈ Compound.ancestors eff eff.length sg.parent := by
      unfold Compound.path at hmem
      split at hmem <;> exact hmem
    exact hbAnc (r8aC8a_anc_of_path_mem himg hpre heffUnique hdlen' hrootT2
      (by rw [heffLen]; exact hbkBound) (heffIdOf bk sb hbk).1 hmemA)
  obtain ⟨gnode, hgn, hgnDecl, hgnCase⟩ :=
    r8aC8a_measuredGraphNodeX execution.graph0_eq execution.graph_eq hlen heff hbi
      (by rw [heffGet, hbi, Option.map_some])
  obtain ⟨bnode, hbn, hbnDecl, hbnCase⟩ :=
    r8aC8a_measuredGraphNodeX execution.graph0_eq execution.graph_eq hlen heff hbk
      (by rw [heffGet, hbk, Option.map_some])
  obtain ⟨partG, hpartGMem, entryG, hentryGMem, hentryGKey⟩ :=
    sceneExecutionR_parts_entryR execution hbid
  obtain ⟨partB, hpartBMem, entryB, hentryBMem, hentryBKey⟩ :=
    sceneExecutionR_parts_entryR execution hbkBound
  obtain ⟨ig, hzipG⟩ := List.mem_iff_getElem?.mp hentryGMem
  obtain ⟨ib, hzipB⟩ := List.mem_iff_getElem?.mp hentryBMem
  have higB : partG.1[ig]? = some bi := by
    have h := (List.getElem?_zip_eq_some.mp hzipG).1
    rw [hentryGKey] at h
    exact h
  have hibB : partB.1[ib]? = some bk := by
    have h := (List.getElem?_zip_eq_some.mp hzipB).1
    rw [hentryBKey] at h
    exact h
  have hcompMem : partG.1 ∈ components execution.graph := by
    rw [← hpartsMap]
    exact List.mem_map_of_mem hpartGMem
  obtain ⟨packed, hpack, -⟩ := packAcc_components_disjoint execution.packed_eq
  have hpackLen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack]
    simp
  by_cases hsame : partG = partB
  · rw [← hsame] at hibB
    obtain ⟨c, hcsel⟩ := List.mem_iff_getElem?.mp hpartGMem
    have hcbound : c < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hcsel).1
    have hcpacked : c < packed.boxes.length := by rw [hpackLen]; exact hcbound
    obtain ⟨selected, _, hlookup₀⟩ :=
      r8aC8a_partPackedFrameR execution packed hpack hcsel hcpacked
    have hrectGval := hlookup₀ ig bi higB hbid
    have hrectBval := hlookup₀ ib bk hibB hbkBound
    have higne : ig ≠ ib := by
      intro heq
      rw [heq] at higB
      exact hbik (Option.some.inj (higB.symm.trans hibB))
    have hgnLookup : (componentCandidateR selected.spec execution.graph
        partG.1 selected.candidate).nodes[ig]? =
        some gnode :=
      component_node_lookupR higB hgn
    have hbnLookup : (componentCandidateR selected.spec execution.graph
        partG.1 selected.candidate).nodes[ib]? =
        some bnode := by
      exact component_node_lookupR hibB hbn
    have hcbFalse : bnode.clusterPath.contains gnode.decl = false := by
      cases hc : bnode.clusterPath.contains gnode.decl with
      | false => rfl
      | true =>
        simp only [List.contains_iff_mem] at hc
        rw [hgnDecl] at hc
        have hbc := hbnCase
        rcases hbc with ⟨_, hbPath⟩ | ⟨_, hbPath, _⟩
        · rw [hbPath] at hc
          rcases List.mem_append.mp hc with hmem | hmem
          · exact False.elim (hnotInPathB hmem)
          · exact False.elim (hbik (List.mem_singleton.mp hmem))
        · rw [hbPath] at hc
          exact False.elim (hnotInPathB hc)
    have hcgFalse : gnode.clusterPath.contains bnode.decl = false := by
      cases hc : gnode.clusterPath.contains bnode.decl with
      | false => rfl
      | true =>
        simp only [List.contains_iff_mem] at hc
        rw [hbnDecl] at hc
        have hgc := hgnCase
        rcases hgc with ⟨_, hgPath⟩ | ⟨_, hgPath, _⟩
        · rw [hgPath] at hc
          rcases List.mem_append.mp hc with hmem | hmem
          · exact False.elim (hnotInPathG hmem)
          · exact False.elim (hbik.symm (List.mem_singleton.mp hmem))
        · rw [hgPath] at hc
          exact False.elim (hnotInPathG hc)
    have hnodes : selected.cg.nodes =
        (componentCandidateR selected.spec execution.graph partG.1 selected.candidate).nodes :=
      r8aC8a_run_nodesR selected.run_eq
    have hgnLookup' : selected.cg.nodes[ig]? = some gnode := by
      rw [hnodes]; exact hgnLookup
    have hbnLookup' : selected.cg.nodes[ib]? = some bnode := by
      rw [hnodes]; exact hbnLookup
    have hdeclNe : gnode.decl ≠ bnode.decl := by rw [hgnDecl, hbnDecl]; exact hbik
    have hsp : Disjoint (frameRect execution.params selected.cg selected.run ig)
        (frameRect execution.params selected.cg selected.run ib) := by
      cases hspec : selected.spec with
      | none =>
        have hrunNone := selected.run_eq
        rw [hspec, componentCandidateR_none] at hrunNone
        obtain ⟨hX, hcg⟩ := r8aC8a_runX_of_none hrunNone
        have hu := hgnLookup'
        have hw := hbnLookup'
        rw [hcg] at hu hw
        rcases hgnCase with ⟨hgBorder, -⟩ | ⟨hgBorder, -, -⟩
        · rw [hcg]
          exact r8aC8a_clear_none execution.graph0_eq execution.graph_eq hlen hwf hfp
            hcompMem hX hu hw hgBorder hdeclNe hcbFalse hcgFalse
        · rcases hbnCase with ⟨hbBorder, -⟩ | ⟨hbBorder, -, -⟩
          · rw [hcg]
            exact (Disjoint.comm _ _).mp (r8aC8a_clear_none execution.graph0_eq
              execution.graph_eq hlen hwf hfp hcompMem hX
              hw hu hbBorder hdeclNe.symm hcgFalse hcbFalse)
          · exact componentRunR_positions_disjointR_none execution.graph0_eq execution.graph_eq
              hcompMem hrunNone hgnLookup' hbnLookup' hgBorder hbBorder higne
      | some s =>
        have hsourceGroup : sg.role = .group := by
          have hid : sg.role.id = "group" := by simpa only [hgeq] using hrole
          cases hs : sg.role with
          | node => simp [hs, BoxRole.id] at hid
          | group => rfl
        let pair : R8a_SelectedPair execution g b :=
          { part := partG
            selected := selected
            packed := packed
            shelfIndex := c
            shelf := packed.boxes[c]
            spec := s
            u := ig
            w := ib
            uNode := gnode
            wNode := bnode
            sourceGroup := sg
            sourcePeer := sb
            pack_eq := hpack
            shelf_eq := List.getElem?_zip_eq_some.mpr ⟨hcsel, List.getElem?_eq_getElem hcpacked⟩
            active := hspec
            group_pos := by rwa [hgnDecl]
            peer_pos := by rwa [hbnDecl]
            group_node := hgnLookup'
            peer_node := hbnLookup'
            group_source := by rwa [hgnDecl]
            peer_source := by rwa [hbnDecl]
            group_role := hsourceGroup
            group_emit := by rw [hgeq, hrectGval] <;> rfl
            peer_emit := by rw [hbeq, hrectBval] <;> rfl
            group_mem := hgMemDump
            peer_mem := hbMemDump
            foreign_id := hbId
            group_not_ancestor := hgAncDump
            peer_not_ancestor := hbAncDump
            decl_ne := hdeclNe
            group_not_in_path := hcbFalse
            peer_not_in_path := hcgFalse }
        have hlocal (hc : R8a_SelectedOpenCase pair) :
            Disjoint (frameRect execution.params selected.cg selected.run ig)
              (frameRect execution.params selected.cg selected.run ib) :=
          (r8aGap_iff_disjoint _ _).mp (clearance g b pair hc)
        rcases hgnCase with ⟨hgBorder, -⟩ | ⟨hgBorder, -, hdemote⟩
        · rcases hbnCase with ⟨hbBorder, -⟩ | ⟨hbBorder, -, -⟩
          · exact hlocal (.groups hgBorder hbBorder)
          · exact hlocal (.groupPlain (Or.inl ⟨hgBorder, hbBorder⟩))
        · rcases hbnCase with ⟨hbBorder, -⟩ | ⟨hbBorder, -, -⟩
          · exact hlocal (.groupPlain (Or.inr ⟨hgBorder, hbBorder⟩))
          · have hrunSome := selected.run_eq
            rw [hspec] at hrunSome
            by_cases hrank : (rk selected.run.proper.rank ig).toNat =
                (rk selected.run.proper.rank ib).toNat
            · by_cases hparent : sg.parent = sb.parent
              · exact componentRunR_region_siblings_disjoint execution.graph0_eq
                  execution.graph_eq hrunSome higne higB hibB hgn hbn hbi hbk
                  hgBorder hbBorder hparent
              · exact hlocal (.demotedCrossParent hgBorder hbBorder
                  (hdemote hsourceGroup) hrank hparent)
            · exact componentRunR_positions_disjointR_different_rank (exactIds := exactIds)
                hrunSome hgnLookup' hbnLookup' hgBorder hbBorder hrank
    rw [hgRect, hrectGval, hbRect, hrectBval]
    exact r8aC8a_shiftRect_disjoint (r8aC8a_orientRect_disjoint
      (r8aC8a_shiftRect_disjoint (r8aC8a_shiftRect_disjoint hsp)))
  · obtain ⟨cG, hcselG⟩ := List.mem_iff_getElem?.mp hpartGMem
    obtain ⟨cB, hcselB⟩ := List.mem_iff_getElem?.mp hpartBMem
    have hcGbound : cG < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hcselG).1
    have hcBbound : cB < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hcselB).1
    obtain ⟨_, hcontainB, hlookupB⟩ :=
      r8aC8a_partPackedFrameR execution packed hpack hcselB
        (by rw [hpackLen]; exact hcBbound)
    obtain ⟨_, hcontainG, hlookupG⟩ :=
      r8aC8a_partPackedFrameR execution packed hpack hcselG
        (by rw [hpackLen]; exact hcGbound)
    have hcpboxG : packed.boxes[cG]? = some packed.boxes[cG] :=
      List.getElem?_eq_getElem (by rw [hpackLen]; exact hcGbound)
    have hcpboxB : packed.boxes[cB]? = some packed.boxes[cB] :=
      List.getElem?_eq_getElem (by rw [hpackLen]; exact hcBbound)
    have hcne : cG ≠ cB := by
      intro heq
      apply hsame
      have h1 : (execution.componentsAcc.parts.zip packed.boxes)[cG]? =
          some (partG, packed.boxes[cG]) := List.getElem?_zip_eq_some.mpr ⟨hcselG, hcpboxG⟩
      have h2 : (execution.componentsAcc.parts.zip packed.boxes)[cB]? =
          some (partB, packed.boxes[cB]) := List.getElem?_zip_eq_some.mpr ⟨hcselB, hcpboxB⟩
      have hsel1 := zip_getElem?_left h1
      have hsel2 := zip_getElem?_left h2
      rw [heq] at hsel1
      exact Option.some.inj (hsel1.symm.trans hsel2)
    have hdisjRects : Disjoint packed.boxes[cG] packed.boxes[cB] :=
      Pack.pack_boxes_disjoint hpack cG cB
        (by rw [hpackLen]; exact hcGbound) (by rw [hpackLen]; exact hcBbound) hcne
    have hvalG := hlookupG ig bi higB hbid
    have hvalB := hlookupB ib bk hibB hbkBound
    have hconG := hcontainG ig bi higB hbid
    have hconB := hcontainB ib bk hibB hbkBound
    rw [hgRect, hvalG, hbRect, hvalB]
    intro hmeet
    exact hdisjRects (meetsInterior_contained_mono
      (meetsInterior_of_orientRect (meetsInterior_of_shiftRect hmeet)) hconG hconB)

theorem flatC8aB_layoutRIds_reindex_of_selected (exactIds : List String)
    (idSets : List (String × List String))
    (hselected : R8a_ReindexedSelectedClearance exactIds idSets) :
    FlatC8aB (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) := by
  intro inp o res hwf hfp hok
  obtain ⟨execution⟩ := layoutRIds_sceneExecution hok
  exact r8a_c8a_of_selectedClearance execution hwf hfp
    (hselected inp o res hwf hfp hok execution)

theorem flatC8aB_layoutRIds_reindex_iff_selected (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC8aB (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) ↔
      R8a_ReindexedSelectedClearance exactIds idSets := by
  constructor
  · intro hflat inp o res hwf hfp hok execution
    exact r8a_selectedClearance_of_c8a execution (hflat inp o res hwf hfp hok)
  · exact flatC8aB_layoutRIds_reindex_of_selected exactIds idSets

/-- The reindexed base's flat C8a clause, conditional only on the two
active group-clearance facts and the cross-parent demoted-group case. -/
theorem flatC8aB_rsmBase_W (exactIds : List String)
    (idSets : List (String × List String))
    (hSep : R8a_Separated exactIds) (hNonGroup : R8a_NonGroupClear exactIds)
    (hDifferentParent : R8a_DemotedGroupPlainCrossParent exactIds idSets) :
    FlatC8aB (fun sub o' =>
      layoutRIds exactIds (reindexRegionSets idSets sub) sub o') := by
  refine flatC8aB_layoutRIds_reindex_of_selected exactIds idSets ?_
  intro inp o res hwf hfp _ execution g b pair hcase
  apply (r8aGap_iff_disjoint _ _).mpr
  have hpartMem := List.mem_of_getElem? (List.getElem?_zip_eq_some.mp pair.shelf_eq).1
  have hparts := (actual_components_parts_geometryR (by rfl) execution.components_eq).1
  have hcomp : pair.part.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hpartMem
  have hlen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    simp only [boxLines] at hl
    have h2 := (mapM_getElem? _ _ _ hl).1
    have hzip : inp.boxes.zipIdx.length = inp.boxes.length := List.length_zipIdx
    omega
  have hrun := pair.selected.run_eq
  rw [pair.active] at hrun
  have hregions : newComponentRegions pair.selected.spec execution.params inp
      (componentCandidateR pair.selected.spec execution.graph pair.part.1
        pair.selected.candidate) = .ok pair.selected.regions := by
    rw [pair.selected.effective_eq]
    exact componentTrialR_selected_regions _ pair.selected.regions_eq
  rw [pair.active] at hregions
  have hsome : ∃ rm, pair.selected.regions = some rm := by
    cases hr : pair.selected.regions with
    | none =>
      have heff := pair.selected.effective_eq
      rw [pair.active, hr] at heff
      simp at heff
    | some rm => exact ⟨rm, rfl⟩
  obtain ⟨rm, hrm⟩ := hsome
  rw [hrm] at hregions
  have hnodes := r8aC8a_run_nodesR hrun
  have hu := pair.group_node
  have hw := pair.peer_node
  rw [hnodes] at hu hw
  cases hcase with
  | groups hg _ =>
    rw [r8aC8a_frameRect_congr (i := pair.u) hnodes,
      r8aC8a_frameRect_congr (i := pair.w) hnodes]
    exact r8aC8a_clear_some hSep hNonGroup execution.graph0_eq execution.graph_eq
      hlen hwf hfp hcomp hregions hrun hu hw hg pair.decl_ne
      pair.group_not_in_path pair.peer_not_in_path
  | groupPlain hb =>
    rw [r8aC8a_frameRect_congr (i := pair.u) hnodes,
      r8aC8a_frameRect_congr (i := pair.w) hnodes]
    rcases hb with ⟨hg, _⟩ | ⟨_, hwGroup⟩
    · exact r8aC8a_clear_some hSep hNonGroup execution.graph0_eq execution.graph_eq
        hlen hwf hfp hcomp hregions hrun hu hw hg pair.decl_ne
        pair.group_not_in_path pair.peer_not_in_path
    · exact (Disjoint.comm _ _).mp
        (r8aC8a_clear_some hSep hNonGroup execution.graph0_eq execution.graph_eq
          hlen hwf hfp hcomp hregions hrun hw hu hwGroup pair.decl_ne.symm
          pair.peer_not_in_path pair.group_not_in_path)
  | demotedCrossParent hg hb hfixed hrank hparent =>
    exact hDifferentParent execution hwf hfp hpartMem
      (s := pair.spec) (rm := rm) (candidate := pair.selected.candidate)
      (loops := pair.selected.loops) (area := pair.selected.area)
      hregions hrun pair.selected.loops_eq pair.selected.part_eq
      pair.group_pos pair.peer_pos pair.group_source pair.peer_source pair.group_role hfixed
      pair.group_node pair.peer_node hg hb pair.decl_ne pair.group_not_in_path
      pair.peer_not_in_path hrank hparent

end PipelineImpl
end Layered
end Elegant

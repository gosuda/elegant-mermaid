import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionFlatInset
import Elegant.Layered.RegionPartSizing
import Elegant.Layered.RegionFoundation
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.RankSiblingDisjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region flat C3 (`layoutRIds`).

Packet P6 of the region tower: `flatC3B_layoutRIds`, the region analogue of
`flatC3B_layoutX` (`ExactFlatC3Closure.lean:37-39`) via `layoutRIds_c3` and
`layoutRIds_c3'`. The placement premise `ExactComponentPlacementR` mirrors
`ExactComponentPlacement` (`ExactFlatFacts.lean:765-793`) with `SceneExecutionR`
in place of `SceneExecutionX`, `componentCandidateR` in place of
`componentCandidate`, and `componentRunR` (returning the rewritten graph `cg'`
with the run) in place of `componentRunX`. The some-spec candidate takes the
raw component graph without cycle breaking (`RegionPlacement.lean:382-396`),
and `crossCoordsR` allocates region frames (`RegionPlacement.lean:294-377`).

Truth note (probe `proofs/wip/Probe/RegionFlatC3Probe.lean`, plus the R2/R4
rows of `RegionFitTruthProbes.lean`): the base-level C3 claim is false without
the `framedParents` premise. When `exactIds`/`fixedSizes` names a region
parent that still has children in the base input (R2: G1 fixed 10x10, R4: G1
fixed 800x600), `layoutRIds` succeeds, keeps the fixed rect verbatim (shared
`measuredGraph` sizing, `Pipeline.lean:240-244`), the children spill, and the
validator fails C3. The family entry rejects those inputs with a domain error
at the `!framedParents inp` guard (`ExactPipeline.lean:196`), which checks
that every non-root box parents to a group box not named in `fixedSizes`
(`Pipeline.lean:1068-1073`); family success implies the guard by
`layoutFamilyB_framed_parents`. The exact twin escapes the same input the
same way: `exactDecls` (`ExactPipeline.lean:93-96`) does not restrict to
leaves (it keeps `exactIds` names and fixed-size groups), so `flatC3B_layoutX`
relies on the identical `framedParents` premise. Accordingly every statement
below carries `WellFormed`/`framedParents` locally on the executed scene, and
the two unproved conjuncts stay as single named residuals that are vacuous on
the R2/R4 counterexamples and true on the probe scenes.
-/

/-- Region member-frame nesting over one executed scene: member frames nest in
their group frame for every executed region run. Local `WellFormed` and
`framedParents` premises mirror `exactMemberInFrame'`
(`ExactRunFrameNestingProof.lean:3266`); without them the R2/R4 fixed-parent
inputs are counterexamples. Replaying `exactMemberInFrame'` needs the region
frame geometry of `crossCoordsR` (`RegionPlacement.lean:294-377`), so this
stays open. -/
def R_MemberFramesNestR (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec) (cg' : Graph)
    (run : Run) (orderOptions : OrderOptions),
    comp ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      orderOptions = .ok (cg', run) →
    ∀ (memberIndex key parentKey parentIndex : Nat) (member : Node),
      comp[memberIndex]? = some key → key < inp.boxes.length →
      (componentCandidateR spec' execution.graph comp candidate).nodes[memberIndex]? =
        some member →
      ∀ (childBox : ModelBox), inp.boxes[key]? = some childBox →
      ∀ (parentBox : ModelBox), inp.boxes[parentKey]? = some parentBox →
      childBox.parent = parentBox.id → childBox.parent ≠ "" →
      comp[parentIndex]? = some parentKey →
      (frameRect execution.params (componentCandidateR spec' execution.graph comp candidate)
        run parentIndex).Contained
        (frameRect execution.params (componentCandidateR spec' execution.graph comp candidate)
          run memberIndex)

/-- Region parent-in-component over one executed scene: a referenced parent
key lies in the same component. Local premises mirror `exactParentInComponent`
(`ExactParentInComponent.lean:157`); without `framedParents` the R2/R4 inputs
are counterexamples. The X proof reads only the shared measured/exact graph
construction, so this is a replay obligation, still open. -/
def R_ParentInComponentR (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (comp : List Nat) (_hcomp : comp ∈ components execution.graph)
    (key parentKey : Nat) (_hkeyLen : key < inp.boxes.length) (_hkeyIn : key ∈ comp)
    (member : Node) (_hmemberGraph : execution.graph.nodes[key]? = some member)
    (childBox : ModelBox) (_hchildBox : inp.boxes[key]? = some childBox)
    (parentBox : ModelBox) (_hparentBox : inp.boxes[parentKey]? = some parentBox)
    (_hparentRef : childBox.parent = parentBox.id) (_hparentNe : childBox.parent ≠ ""),
    parentKey ∈ comp

/-- The region pipeline satisfies the shared `ExactComponentPlacement`
hypothesis shape: parts are bounded, member frames nest, and parents stay in
the same component. Twin of `ExactComponentPlacement`
(`ExactFlatFacts.lean:765-793`). -/
def ExactComponentPlacementR (exactIds : List String)
    (idSets : List (String × List String)) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  WellFormed (inputModel inp o) → framedParents inp = true →
  ∀ (execution : SceneExecutionR exactIds idSets inp o res),
    (∀ q ∈ execution.componentsAcc.parts, PartBounded q.2) ∧
    (∀ (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec) (cg' : Graph)
      (run : Run) (orderOptions : OrderOptions),
      comp ∈ components execution.graph →
      componentRunR execution.params (exactDecls exactIds inp) spec' inp
        (componentCandidateR spec' execution.graph comp candidate) execution.measured
        orderOptions = .ok (cg', run) →
      ∀ (memberIndex key parentKey parentIndex : Nat) (member : Node),
        comp[memberIndex]? = some key → key < inp.boxes.length →
        (componentCandidateR spec' execution.graph comp candidate).nodes[memberIndex]? =
          some member →
        ∀ (childBox : ModelBox), inp.boxes[key]? = some childBox →
        ∀ (parentBox : ModelBox), inp.boxes[parentKey]? = some parentBox →
        childBox.parent = parentBox.id → childBox.parent ≠ "" →
        comp[parentIndex]? = some parentKey →
        (frameRect execution.params (componentCandidateR spec' execution.graph comp candidate)
          run parentIndex).Contained
          (frameRect execution.params (componentCandidateR spec' execution.graph comp candidate)
            run memberIndex)) ∧
    (∀ (comp : List Nat) (_hcomp : comp ∈ components execution.graph)
      (key parentKey : Nat) (_hkeyLen : key < inp.boxes.length) (_hkeyIn : key ∈ comp)
      (member : Node) (_hmemberGraph : execution.graph.nodes[key]? = some member)
      (childBox : ModelBox) (_hchildBox : inp.boxes[key]? = some childBox)
      (parentBox : ModelBox) (_hparentBox : inp.boxes[parentKey]? = some parentBox)
      (_hparentRef : childBox.parent = parentBox.id) (_hparentNe : childBox.parent ≠ ""),
      parentKey ∈ comp)

/-- Assemble the placement premise from the bounded conjunct (closed from the
chosen-run residual) and the two open residuals. -/
theorem exactComponentPlacementR_of {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (hres : R_PartSizingRResidual exactIds idSets)
    (hnest : R_MemberFramesNestR exactIds idSets)
    (hpar : R_ParentInComponentR exactIds idSets) :
    ExactComponentPlacementR exactIds idSets inp o res := by
  intro hwf hframed execution
  refine ⟨?_, ?_, ?_⟩
  · exact exactComponentPlacementR_bounded_of_residual execution hres
  · intro comp candidate spec' cg' run orderOptions hcomp hrun
    exact hnest execution hwf hframed comp candidate spec' cg' run orderOptions
      hcomp hrun
  · intro comp hcomp key parentKey hkeyLen hkeyIn member hmemberGraph childBox
      hchildBox parentBox hparentBox hparentRef hparentNe
    exact hpar execution hwf hframed comp hcomp key parentKey hkeyLen hkeyIn
      member hmemberGraph childBox hchildBox parentBox hparentBox hparentRef
      hparentNe

/-- Region scene boxes read back their source box (replay of
`sceneBox_source_rectX`, `ExactFlatFacts.lean:1557`, via `boxes_eq_mapR`). -/
private theorem rfcSceneBoxSourceRectR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {bi : Nat} {b : Box} (hb : res.scene.boxes[bi]? = some b) :
    ∃ source : ModelBox, inp.boxes[bi]? = some source ∧
      b.id = source.id ∧ b.parent = source.parent ∧ b.exclusive = source.exclusive ∧
      b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD bi default)) := by
  have hbiLT : bi < inp.boxes.length := by
    have h := (List.getElem?_eq_some_iff.mp hb).1
    rw [execution.boxes_eq_mapR] at h
    simpa only [List.length_map, List.length_zipIdx] using h
  have hbox : res.scene.boxes[bi]? = some
      (Box.mk inp.boxes[bi].id inp.boxes[bi].role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD bi default)))
        inp.boxes[bi].parent inp.boxes[bi].exclusive) := by
    rw [execution.boxes_eq_mapR]
    simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hbiLT,
      Option.map_some, Nat.zero_add]
  have hbeq : b = Box.mk inp.boxes[bi].id inp.boxes[bi].role.id
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD bi default)))
      inp.boxes[bi].parent inp.boxes[bi].exclusive :=
    Option.some.inj (hb.symm.trans hbox)
  refine ⟨inp.boxes[bi], List.getElem?_eq_getElem hbiLT, ?_, ?_, ?_, ?_⟩ <;>
    rw [hbeq]

/-- Region packed boxes cover the component positions (replay of
`part_packed_box_lenX`, `ExactFlatFacts.lean:1521`). -/
private theorem rfcPartPackedBoxLenR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {part : List Nat × Part}
    (hk : execution.componentsAcc.parts[k]? = some part) :
    k < packed.boxes.length := by
  have hkbl : k < execution.componentsAcc.parts.length :=
    (List.getElem?_eq_some_iff.mp hk).1
  have hcount := Pack.pack_count hpacked
  rw [hcount, List.length_map]
  exact hkbl

/-- Exact placement writes one rectangle per region candidate node (copy of
`rapPlacedRects_getR`, private to `RegionActualParts.lean`). -/
private theorem rfcPlacedRectsGetR {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {cursor : Int} {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- The region candidate keeps the component nodes (copy of
`rapCandidateR_nodes_lengthR`, private to `RegionActualParts.lean`). -/
private theorem rfcCandidateRLengthR (spec' : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec' g comp index).nodes.length = comp.length := by
  cases spec' with
  | none =>
    show (componentCandidate g comp index).nodes.length = comp.length
    rw [componentCandidate_nodes]
    show (comp.map fun v => g.nodes.getD v default).length = comp.length
    exact List.length_map ..
  | some _ =>
    unfold componentCandidateR componentGraph
    dsimp only
    show (comp.map fun v => g.nodes.getD v default).length = comp.length
    exact List.length_map ..

private theorem rfcPlacedRectsLengthR (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).rects.length = cg.nodes.length := by
  unfold placeComponentExact
  simp [List.length_map, List.length_range]

private theorem rfcRunNodesEq {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    cg'.nodes = cg.nodes := by
  unfold componentRunR at h
  obtain ⟨rs, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨rr, _, h⟩ := bind_ok h
    obtain ⟨ranked, hranked, h⟩ := bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := bind_ok h
        obtain ⟨p, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨ord, _, h⟩ := bind_ok h
        obtain ⟨xs, _, h⟩ := bind_ok h
        obtain ⟨placed, _, h⟩ := bind_ok h
        obtain ⟨routed, _, h⟩ := bind_ok h
        split at h
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          have he := Except.ok.inj h
          have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
          have h1 : cg = cg1 :=
            congrArg (fun q : List Int × Graph × Bool => q.2.1) (Except.ok.inj hranked)
          rw [hfst, ← h1]
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          have he := Except.ok.inj h
          have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
          have h1 : cg = cg1 :=
            congrArg (fun q : List Int × Graph × Bool => q.2.1) (Except.ok.inj hranked)
          rw [hfst, ← h1]
  · obtain ⟨ranked, hranked, h⟩ := bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := bind_ok h
        obtain ⟨p, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨ord, _, h⟩ := bind_ok h
        split at h
        · simp only [bind, Except.bind] at h
          exact absurd h (by simp)
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨placed, _, h⟩ := bind_ok h
          obtain ⟨routed, _, h⟩ := bind_ok h
          split at h
          · obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            have he := Except.ok.inj h
            have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
            have hnodes := rankEquivalentR_nodes_eq hranked
            rw [hfst, hnodes]
          · obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            have he := Except.ok.inj h
            have hfst : cg' = cg1 := (congrArg Prod.fst he).symm
            have hnodes := rankEquivalentR_nodes_eq hranked
            rw [hfst, hnodes]

def SceneExecutionR.regionSpec {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
    Option RegionSpec :=
  if idSets.isEmpty then none
  else some (RegionSpec.mk idSets (execution.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * execution.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)))

/-- The successful trial resolves the component before selecting its run spec. -/
def R_ComponentSpecSelection {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (comp : List Nat) (spec' : Option RegionSpec) : Prop :=
  ∃ regions, newComponentRegions execution.regionSpec execution.params inp
    (componentGraph execution.graph comp) = .ok regions ∧
    spec' = if regions.isSome then execution.regionSpec else none

/-- Region packed frames read back through the executed run (replay of
`part_frame_lookupX`, `ExactFlatFacts.lean:1588`, via
`actual_components_packed_frame_sourceR`). -/
private theorem rfcPartFrameLookupR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {entry : List Nat × Part} {box : Rect}
    (hentry : execution.componentsAcc.parts[k]? = some entry)
    (hbox : packed.boxes[k]? = some box) :
    ∃ index cg run loops area spec',
      R_ComponentSpecSelection execution entry.1 spec' ∧
      componentRunR execution.params (exactDecls exactIds inp) spec' inp
        (componentCandidateR spec' execution.graph entry.1 index) execution.measured
        (candidateOrder index) = .ok (cg, run) ∧
      componentLoops execution.params cg run execution.measured = .ok loops ∧
      entry.2 = { placeComponentExact execution.params cg run 0 execution.measured loops
        with area := area } ∧
      ∀ (i key : Nat), entry.1[i]? = some key → key < inp.boxes.length →
        execution.packedAcc.rects.getD key default =
          shiftRect box.x box.y
            (shiftRect (0 - (placeBoundsX execution.params cg run execution.measured loops).minX)
              (-(placeBoundsX execution.params cg run execution.measured loops).minY)
              (frameRect execution.params cg run i)) := by
  have hmem : entry ∈ execution.componentsAcc.parts := List.mem_of_getElem? hentry
  obtain ⟨index, chosen, cg, run, loops, area, spec', _, _, _, hselected, hrun, hloops,
    hpartdef⟩ :=
    (actual_components_parts_geometryR (by rfl) execution.components_eq).2 entry hmem
  have hcgLen : cg.nodes.length = entry.1.length := by
    have hnodes := componentRunR_nodes_eq hrun
    have hcand := rfcCandidateRLengthR spec' execution.graph entry.1 index
    simp_all
  have hrectlen : entry.2.rects.length = entry.1.length := by
    rw [hpartdef]
    have hl : (placeComponentExact execution.params cg run 0 execution.measured
        loops).rects.length = entry.1.length := by
      rw [rfcPlacedRectsLengthR]
      exact hcgLen
    simpa using hl
  refine ⟨index, cg, run, loops, area, spec', hselected, hrun, hloops, hpartdef, ?_⟩
  intro i key hkey hkeyBound
  have hi : i < entry.1.length := (List.getElem?_eq_some_iff.mp hkey).1
  have hilen : i < entry.2.rects.length := by omega
  have hsize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_sizeR]
    exact hkeyBound
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? =
      some ((entry, box) : (List Nat × Part) × Rect) :=
    List.getElem?_zip_eq_some.mpr ⟨hentry, hbox⟩
  obtain ⟨index', cg', run', loops', area', spec'', hrun', hloops', hpartdef', hrect⟩ :=
    actual_components_packed_frame_sourceR (by rfl) execution.components_eq
      execution.packed_eq packed hpacked hselected hkey hsize default
  have hrectlen' : entry.2.rects.length = cg'.nodes.length := by
    rw [hpartdef']
    exact rfcPlacedRectsLengthR _ _ _ _ _
  have hiCG' : i < cg'.nodes.length := by omega
  have hiCG : i < cg.nodes.length := by
    rw [hcgLen]
    exact hi
  have hB : entry.2.rects[i]? = some
      (shiftRect (0 - (placeBoundsX execution.params cg' run' execution.measured loops').minX)
        (-(placeBoundsX execution.params cg' run' execution.measured loops').minY)
        (frameRect execution.params cg' run' i)) := by
    rw [hpartdef']
    exact rfcPlacedRectsGetR hiCG'
  rw [hrect, Option.some.inj (hB.symm.trans (by
    rw [hpartdef]
    exact rfcPlacedRectsGetR hiCG))]

set_option maxHeartbeats 2000000

/-- Rectangle relation on the two declarations of an emitted direct parent link,
before the component, shelf, orientation, and canvas transforms. -/
def R_SelectedDirectFrameRelation {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (rel : Rect → Rect → Prop) : Prop :=
  ∀ (part : List Nat × Part) (candidate : Nat) (spec' : Option RegionSpec)
    (cg : Graph) (run : Run) (loops : List (Nat × LoopPlacement)) (area : Int),
    part ∈ execution.componentsAcc.parts →
    part.1 ∈ components execution.graph →
    R_ComponentSpecSelection execution part.1 spec' →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph part.1 candidate) execution.measured
      (candidateOrder candidate) = .ok (cg, run) →
    componentLoops execution.params cg run execution.measured = .ok loops →
    part.2 = { placeComponentExact execution.params cg run 0 execution.measured loops
      with area := area } →
    ∀ (memberIndex key parentKey parentIndex : Nat) (member : Node),
      part.1[memberIndex]? = some key → key < inp.boxes.length →
      (componentCandidateR spec' execution.graph part.1 candidate).nodes[memberIndex]? =
        some member →
      ∀ (childBox : ModelBox), inp.boxes[key]? = some childBox →
      ∀ (parentBox : ModelBox), inp.boxes[parentKey]? = some parentBox →
      childBox.parent = parentBox.id → childBox.parent ≠ "" →
      part.1[parentIndex]? = some parentKey →
      rel (frameRect execution.params cg run parentIndex)
        (frameRect execution.params cg run memberIndex)

/-- The selected part and shared geometric transforms for one admitted
emitted parent link. Applies to both inclusive and strict containment. -/
theorem sceneExecutionR_directFrameRelation {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hparentInComponent : ∀ (comp : List Nat), comp ∈ components execution.graph →
      ∀ (key parentKey : Nat), key < inp.boxes.length → key ∈ comp →
      ∀ (member : Node), execution.graph.nodes[key]? = some member →
      ∀ (childBox : ModelBox), inp.boxes[key]? = some childBox →
      ∀ (parentBox : ModelBox), inp.boxes[parentKey]? = some parentBox →
      childBox.parent = parentBox.id → childBox.parent ≠ "" → parentKey ∈ comp)
    {rel : Rect → Rect → Prop}
    (hshift : ∀ (dx dy : Int) {a b : Rect}, rel a b →
      rel (shiftRect dx dy a) (shiftRect dx dy b))
    (horient : ∀ (direction : Direction) (h : Int) {a b : Rect}, rel a b →
      rel (orientRect direction h a) (orientRect direction h b))
    (hraw : R_SelectedDirectFrameRelation execution rel) :
    ∀ b ∈ res.scene.layoutDump.boxes, b.parent ≠ "" →
      ∀ p : Box, res.scene.layoutDump.box? b.parent = some p → rel p.rect b.rect := by
  have hpackedEq := execution.packed_eq
  unfold packAcc at hpackedEq
  obtain ⟨packed, hpack, -⟩ := bind_ok hpackedEq
  have hcompMap := (actual_components_parts_geometryR (by rfl) execution.components_eq).1
  intro b hb hbparent p hpLookup
  simp only [Scene.layoutDump] at hb
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨childBox, hchildBoxMem, -, hbpar, -, hbrect⟩ :=
    rfcSceneBoxSourceRectR execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hchildBoxMem).1
  have hparentNe : childBox.parent ≠ "" := by rw [← hbpar]; exact hbparent
  obtain ⟨parent, hparentMem, hpid, -, -⟩ :=
    framedParents_parent hframed (List.mem_of_getElem? hchildBoxMem) hparentNe
  obtain ⟨piIdx, hpi⟩ := List.mem_iff_getElem?.mp hparentMem
  have hfind : res.scene.layoutDump.boxes.find? (fun x : Box => x.id == b.parent) =
      some p := hpLookup
  have hpMemDump : p ∈ res.scene.layoutDump.boxes := List.mem_of_find?_eq_some hfind
  have hpMem : p ∈ res.scene.boxes := by
    simpa only [Scene.layoutDump] using hpMemDump
  have hpId : p.id = b.parent := by
    have hsome := List.find?_some hfind
    simpa using hsome
  obtain ⟨pj, hpj⟩ := List.mem_iff_getElem?.mp hpMem
  obtain ⟨pbox, hsp, hspid, -, -, hprect⟩ := rfcSceneBoxSourceRectR execution hpj
  have hjLen : pj < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsp).1
  have hmapLen2 : piIdx < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hpi).1
  have hid : (inp.boxes.map (·.id))[piIdx]? = (inp.boxes.map (·.id))[pj]? := by
    rw [List.getElem?_map, hpi, List.getElem?_map, hsp]
    simp only [Option.map_some]
    rw [hpid.trans (hbpar.symm.trans (hpId.symm.trans hspid))]
  have hpe : piIdx = pj := (Model.boxIds_nodup hwf).getElem?_inj hmapLen2 |>.mp hid
  have hpiP : inp.boxes[pj]? = some parent := by rw [← hpe]; exact hpi
  obtain ⟨part, posB, k, hpart, hk, hposB⟩ := key_part_positionR execution hbiLen
  have hkLen := rfcPartPackedBoxLenR execution packed hpack hk
  have hbox : packed.boxes[k]? = some packed.boxes[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
  obtain ⟨cand, cg, run, loops, area, spec', hselected, hrun, hloops, hplaced, hlookup⟩ :=
    rfcPartFrameLookupR execution packed hpack hk hbox
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hcompMap]
    exact List.mem_map.mpr ⟨part, List.mem_of_getElem? hk, rfl⟩
  have hgl : bi < execution.graph.nodes.length :=
    sceneExecutionR_graph_lenR execution hbiLen
  have hmemberGraph : execution.graph.nodes[bi]? = some execution.graph.nodes[bi] :=
    List.getElem?_eq_some_iff.mpr ⟨hgl, rfl⟩
  have hmemberLookup :
      (componentCandidateR spec' execution.graph part.1 cand).nodes[posB]? =
        some execution.graph.nodes[bi] :=
    component_node_lookupR hposB hmemberGraph
  have hkeyIn : bi ∈ part.1 := List.mem_of_getElem? hposB
  have hparentIn : pj ∈ part.1 :=
    hparentInComponent part.1 hcomp bi pj hbiLen hkeyIn
      _ hmemberGraph _ hchildBoxMem _ hpiP hpid.symm hparentNe
  obtain ⟨parentIndex, hpIdx⟩ := List.getElem?_of_mem hparentIn
  have hframes :=
    hraw part cand spec' cg run loops area hpart hcomp hselected hrun hloops hplaced
      posB bi pj parentIndex _ hposB hbiLen hmemberLookup _ hchildBoxMem _ hpiP
      hpid.symm hparentNe hpIdx
  have hchildRect := hlookup posB bi hposB hbiLen
  have hparentRect := hlookup parentIndex pj hpIdx hjLen
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  have hcomponent := hshift (0 - bounds.minX) (-bounds.minY) hframes
  have hshelf := hshift packed.boxes[k].x packed.boxes[k].y hcomponent
  have horiented := horient o.direction execution.packedAcc.canvasH hshelf
  have hmargins := hshift execution.params.canvasMargin execution.params.canvasMargin horiented
  rw [hprect, hbrect, hchildRect, hparentRect]
  exact hmargins

/-- Clause C3 for `layoutRIds`, with the placement hypothesis. -/
theorem layoutRIds_c3 {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutRIds exactIds idSets inp o = .ok res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hR : ExactComponentPlacementR exactIds idSets inp o res) :
    Validator.C3 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hRexec := hR hwf hframed execution
  apply sceneExecutionR_directFrameRelation execution hwf hframed hRexec.2.2
    (rel := Rect.Contained)
    (by
      intro dx dy parent child hrect
      exact contained_shiftRect_imp (dx := dx) (dy := dy) hrect)
    (by
      intro direction height parent child hrect
      exact contained_orientRect (d := direction) (h := height) hrect)
  intro part cand spec' cg run loops area _ hcomp _ hrun _ _
    memberIndex key parentKey parentIndex member hkey hkeyLen hnode child hchild
    parent hparent href hne hparentIndex
  have hframe (j : Nat) : frameRect execution.params cg run j =
      frameRect execution.params
        (componentCandidateR spec' execution.graph part.1 cand) run j := by
    simp only [frameRect, nodeRect, rfcRunNodesEq hrun]
  rw [hframe parentIndex, hframe memberIndex]
  exact hRexec.2.1 part.1 cand spec' cg run (candidateOrder cand) hcomp hrun
    memberIndex key parentKey parentIndex member hkey hkeyLen hnode child hchild
    parent hparent href hne hparentIndex

/-- Clause C3 for `layoutRIds`, with no placement hypothesis. -/
theorem layoutRIds_c3' {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutRIds exactIds idSets inp o = .ok res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hR : ExactComponentPlacementR exactIds idSets inp o res) :
    Validator.C3 res.scene.layoutDump :=
  layoutRIds_c3 h hwf hframed hR

/-- The region pipeline discharges the base-parametric flat C3 fact. -/
theorem flatC3B_layoutRIds (exactIds : List String)
    (idSets : List (String × List String))
    (hplace : ∀ {inp : Input} {o : Options} {res : FamilyResult},
      ExactComponentPlacementR exactIds idSets inp o res) :
    FlatC3B (layoutRIds exactIds idSets) :=
  fun inp o res hwf hframed hok =>
    layoutRIds_c3' (exactIds := exactIds) (idSets := idSets) (inp := inp) (o := o)
      (res := res) hok hwf hframed hplace

end PipelineImpl
end Layered
end Elegant

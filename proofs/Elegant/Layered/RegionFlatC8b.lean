import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionFlatInset
import Elegant.Layered.RegionFoundation
import Elegant.Layered.LabelsC8b
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.LabelsClearance
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.Pack
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! Region flat C8b: `FlatC8bB (layoutRIds exactIds idSets)` (packet P8).

Twin of `ExactFlatC8b.lean` replayed over `SceneExecutionR`
(`RegionFoundation.lean:118-152`; extraction at `:208`, scene boxes at
`SceneExecutionR.boxes_eq_mapR`). `packAcc` is shared with the exact
pipeline, so the packed transport replays with the region part family
(`actual_components_parts_geometryR`, `actual_components_packed_rect_valueR`,
`actual_components_packed_frame_sourceR` in `RegionActualParts.lean`).

The packed transport is proved outright except for two narrow per-execution
residuals: the sizing residual `R_PartSizingR` (public in
`RegionFlatInset.lean`, discharged later from `componentRunR` equations) and
the caption-fit residual `R_ExactTitleCaptionFitB8` below (twin of
`X_ExactTitleCaptionFit`; needs the region title-reservation transfer of
packet P6). The core and fallback residuals stay open exactly as in the
exact tower (`ExactSeams.partFrameCores`, `ExactSeams.fallbackCaption`). -/

/-- R core residual: twin of `X_ExecutedPartFrameCoresB8`
(`ExactFlatC8b.lean:38-45`) over `SceneExecutionR`. -/
def R_ExecutedPartFrameCoresB8 (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part

/-- R transport residual: twin of `X_PackedPartTransportBoundedB8`
(`ExactFlatC8b.lean:49-94`) over `SceneExecutionR`. -/
def R_PackedPartTransportBoundedB8 (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    ∃ packed : Pack.State,
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (∀ (k : Nat), k < execution.packedAcc.rects.size → ∀ (r : Rect),
        execution.packedAcc.rects.getD k default = r →
        ∃ (pk : Nat) (part : List Nat × Part) (pos : Nat) (r0 box : Rect),
          execution.componentsAcc.parts[pk]? = some part ∧ part.1[pos]? = some k ∧
          part.2.rects[pos]? = some r0 ∧
          packed.boxes[pk]? = some box ∧
          r = shiftRect box.x box.y r0 ∧
          box.Contained r) ∧
      (∀ (index : Nat) (r : Rect), execution.packedAcc.labels.getD index default = r →
        (∃ (pl : Nat) (part : List Nat × Part) (r0 box : Rect),
          execution.componentsAcc.parts[pl]? = some part ∧
          (index, r0) ∈ part.2.labels ∧
          packed.boxes[pl]? = some box ∧
          r = shiftRect box.x box.y r0 ∧
          box.Contained r) ∨
        r = default) ∧
      (∀ (key : Nat) (stored : Rect), (key, stored) ∈ execution.packedAcc.titles →
        ∃ (pl : Nat) (part : List Nat × Part) (i : Nat) (stored0 box : Rect),
          execution.componentsAcc.parts[pl]? = some part ∧ part.1[i]? = some key ∧
          (i, stored0) ∈ part.2.titles ∧
          packed.boxes[pl]? = some box ∧
          stored = shiftRect box.x box.y stored0 ∧
          box.Contained
            (shiftRect box.x box.y
              { stored0 with
                w := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).w
                h := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).h })) ∧
      (∀ (k : Nat) (r : Rect), execution.packedAcc.rects.getD k default = r → 0 ≤ r.x)

/-- R fallback residual: twin of `X_FallbackCaptionClearB8`
(`ExactFlatC8b.lean:96-117`) over `SceneExecutionR`. -/
def R_FallbackCaptionClearB8 (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    InputFixedFit inp o →
    ∀ (source : ModelLabel) (index ownerIndex : Nat) (g : Box),
      inp.labels[index]? = some source →
      inp.boxes.findIdx? (fun box : ModelBox =>
        box.id == source.owner && !box.exclusive) = some ownerIndex →
      (sceneTitlesExpr execution.params inp o execution.lines
          execution.packedAcc).find? (fun t => t.1 == source.owner) = none →
      g ∈ res.scene.boxes → g.role = "group" →
      let l := ownedTextRect execution.params
        ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
          ownerIndex ⟨"", "", default, "", false⟩)
        (execution.lines.getD ownerIndex [])
      Disjoint g.rect l ∨ g.rect.StrictInside l

/-- R stored-title caption-fit residual: twin of `X_ExactTitleCaptionFit`
(`ExactPackedTransportProof.lean:91-105`) over `SceneExecutionR`. Every
stored title of an executed part covers its measured caption size. This is
the single new narrow residual of the packet (region title reservations
give titles their own height, so the exact border transfer of packet P6 is
needed to discharge it). -/
def R_ExactTitleCaptionFitB8 (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {part : List Nat × Part} (_hpart : part ∈ execution.componentsAcc.parts)
    {title : Nat × Rect} (_htitle : title ∈ part.2.titles),
    let lines := execution.lines.getD (part.1.getD title.1 0) []
    let width := lines.foldl (fun value line => max value line.width) 0
    let height := (max 1 lines.length : Int) * execution.params.lineH
    let size := match o.direction with
      | .LR | .RL => Size.mk height width
      | .TB | .BT => Size.mk width height
    0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ title.2.w ∧ size.h ≤ title.2.h

/-! ## Probe evidence (two-region witness of `RegionActualParts.lean:49-102`). -/

/-- Two-region probe input (copy of `rapProbeInp`, private there). -/
private def r8bProbeInp : Input :=
  { kind := "state"
    boxes := [{ id := "G1", role := .group, parent := "", exclusive := false },
      { id := "A", role := .group, parent := "G1", exclusive := false },
      { id := "B", role := .group, parent := "G1", exclusive := false },
      { id := "G2", role := .group, parent := "", exclusive := false },
      { id := "C", role := .group, parent := "G2", exclusive := false },
      { id := "D", role := .group, parent := "G2", exclusive := false },
      { id := "a1", parent := "A", exclusive := false },
      { id := "b1", parent := "B", exclusive := false },
      { id := "c1", parent := "C", exclusive := false },
      { id := "d1", parent := "D", exclusive := false }]
    routes := [{ id := "e1", fromId := "a1", toId := "c1" },
      { id := "e2", fromId := "b1", toId := "d1" },
      { id := "e3", fromId := "c1", toId := "b1" }]
    texts := ["G1", "A", "B", "G2", "C", "D", "a1", "b1", "c1", "d1"]
    edges := [.plain, .plain, .plain]
    labels := [] }

/-- The two region sets of the probe (copy of `rapProbeSets`). -/
private def r8bProbeIdSets : List (String × List String) :=
  [("G1", ["A", "B"]), ("G2", ["C", "D"])]

/-- The probe layouts succeed. -/
private def r8bProbeOk : Bool :=
  match layoutRIds [] r8bProbeIdSets r8bProbeInp { profile := .vector, direction := .TB } with
  | .ok _ => true
  | .error _ => false

#eval r8bProbeOk

/-- Bool mirror of the caption-fit conclusion on one placed part. -/
private def r8bCaptionFitPartB (P : Params) (o : Options)
    (lines : List (List Measure.Line)) (comp : List Nat) (part : Part) : Bool :=
  part.titles.all fun title =>
    let size := titleCaptionSize P o (lines.getD (comp.getD title.1 0) [])
    decide (0 ≤ size.w) && decide (0 ≤ size.h) &&
      decide (size.w ≤ title.2.w) && decide (size.h ≤ title.2.h)

/-- Bool mirror of both core clearances on one placed part. -/
private def r8bCoresPartB (inp : Input) (comp : List Nat) (part : Part) : Bool :=
  part.labels.all fun l =>
    (List.range comp.length).all fun pos =>
      match comp[pos]?, part.rects[pos]? with
      | some key, some g =>
        match inp.boxes[key]? with
        | some src =>
          if src.role == BoxRole.group then
            decide (Disjoint g l.2) || decide (g.StrictInside l.2)
          else true
        | none => true
      | _, _ => true
/-- Run every component of the probe and check caption fit plus cores. -/
private def r8bProbeC8bB (inp : Input) (sets : List ModelRegionSet) :
    Except LayoutError (List (Bool × Bool)) := do
  let P ← checkedParams .vector inp.kind
  let m ← metricOf .vector
  let target := Measure.wrapTarget m.profile P.wrapWidth 0
  let lines ← boxLines m target inp
  let measured ← measureLabels P m target inp .TB
  let g0 ← measuredGraph P inp {} lines
  let g ← exactGraph P [] inp {} measured g0
  let idSets ← graphRegions inp sets
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    (width, height)
  let spec := RegionSpec.mk idSets titles
  (components g).mapM fun comp => do
    let (cg, run) ← componentRunR P [] (some spec) inp (componentGraph g comp) [] {}
    let loops ← componentLoops P cg run []
    let placed := placeComponentExact P cg run 0 [] loops
    pure (r8bCaptionFitPartB P {} lines comp placed,
      r8bCoresPartB inp comp placed)

#eval r8bProbeC8bB r8bProbeInp [{ parent := 0, regions := [1, 2] },
  { parent := 3, regions := [4, 5] }]

/-- Title counts per probe component: caption-fit evidence is non-vacuous. -/
private def r8bProbeTitleCount (inp : Input) (sets : List ModelRegionSet) :
    Except LayoutError (List Nat) := do
  let P ← checkedParams .vector inp.kind
  let m ← metricOf .vector
  let target := Measure.wrapTarget m.profile P.wrapWidth 0
  let lines ← boxLines m target inp
  let measured ← measureLabels P m target inp .TB
  let g0 ← measuredGraph P inp {} lines
  let g ← exactGraph P [] inp {} measured g0
  let idSets ← graphRegions inp sets
  let titles := lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    (width, height)
  let spec := RegionSpec.mk idSets titles
  (components g).mapM fun comp => do
    let (cg, run) ← componentRunR P [] (some spec) inp (componentGraph g comp) [] {}
    let loops ← componentLoops P cg run []
    pure (placeComponentExact P cg run 0 [] loops).titles.length

#eval r8bProbeTitleCount r8bProbeInp [{ parent := 0, regions := [1, 2] },
  { parent := 3, regions := [4, 5] }]

/-! ## Packed transport intermediates (closed in-file). -/

/-- R packed-label provenance: twin of `X_PackedLabelsTransport`
(`ExactPackedTransportProof.lean:45-65`) over `SceneExecutionR`. -/
private def r8b_PackedLabelsTransport (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    ∃ packed : Pack.State,
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      ∀ (index : Nat) (r : Rect), execution.packedAcc.labels.getD index default = r →
        (∃ (pl : Nat) (part : List Nat × Part) (r0 box : Rect),
          execution.componentsAcc.parts[pl]? = some part ∧
          (index, r0) ∈ part.2.labels ∧
          packed.boxes[pl]? = some box ∧
          r = shiftRect box.x box.y r0) ∨
        r = default

/-- R packed-title membership: twin of `X_PackedTitlesMemSource`
(`ExactPackedTransportProof.lean:67-89`) over `SceneExecutionR`. -/
private def r8b_PackedTitlesMemSource (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {packed : Pack.State}
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {key : Nat} {stored : Rect}
    (_hmem : (key, stored) ∈ execution.packedAcc.titles),
    ∃ (pl : Nat) (part : List Nat × Part) (i : Nat) (stored0 box : Rect),
      execution.componentsAcc.parts[pl]? = some part ∧
      part.1[i]? = some key ∧
      (i, stored0) ∈ part.2.titles ∧
      packed.boxes[pl]? = some box ∧
      stored = shiftRect box.x box.y stored0

/-! ## Small pack helpers (prefixed copies of exact twins). -/

/-- The packing fold preserves the rect array size (copy of the private
`b8_packFold_rects_sizeX` in `ExactFlatC8b.lean`). -/
private theorem r8b_packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

/-- Region packed rect array size (copy of the private
`b8_packedAcc_rects_sizeX` in `ExactFlatC8b.lean`, via
`SceneExecutionR.components_rects_sizeR`). -/
private theorem r8b_packedAcc_rects_sizeR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have hout := Except.ok.inj h
  rw [← hout]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep
    { execution.componentsAcc with
      canvasW := packed.width
      canvasH := packed.height
      titles := [] }).rects.size = inp.boxes.length
  rw [r8b_packFold_rects_size]
  exact execution.components_rects_sizeR

/-- Pack existence over the region execution (copy of the private
`xpptb_packedShelfExistence_of_execution` in `ExactPackedTransportProof.lean`). -/
private theorem r8b_packedShelfExistence_of_execution {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    ∃ packed : Pack.State,
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed ∧
      packed.boxes.length = execution.componentsAcc.parts.length := by
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, hpacked, _⟩ := bind_ok hpack
  refine ⟨packed, hpacked, ?_⟩
  rw [Pack.pack_count hpacked, List.length_map]


/-- Shelf dimensions match the part dimensions at every packed position
(copy of the private `xpptb_shelfDims_of_mem` in
`ExactPackedTransportProof.lean`; shared `Pack` geometry). -/
private theorem r8b_shelfDims_of_mem {inp : Input} {o : Options} {res : FamilyResult}
    {exactIds : List String} {idSets : List (String × List String)}
    {execution : SceneExecutionR exactIds idSets inp o res}
    {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    {pl : Nat} {part : List Nat × Part} {box : Rect}
    (hparts : execution.componentsAcc.parts[pl]? = some part)
    (hboxes : packed.boxes[pl]? = some box) :
    box.w = part.2.width ∧ box.h = part.2.height := by
  have hdim' := Pack.pack_dimensions hpacked
  simp only [Pack.dimensions, List.map_map, Function.comp_def] at hdim'
  have hdim := congrArg (fun l : List (Int × Int) => l[pl]?) hdim'
  rw [List.getElem?_map, hboxes, List.getElem?_map, hparts] at hdim
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdim
  exact hdim

/-- Exact placement writes one rectangle per component-graph node (copy of the
private `xpptb_placeComponentExact_rects_length` in
`ExactPackedTransportProof.lean`; shared `placeComponentExact`). -/
private theorem r8b_placeComponentExact_rects_length (P : Params) (cg : Graph)
    (run : Run) (cursor : Int) (labels : List MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run cursor labels loops).rects.length = cg.nodes.length := by
  unfold placeComponentExact
  simp [List.length_map, List.length_range]

/-- The region candidate keeps the component nodes (copy of the private
`rapCandidateR_nodes_lengthR` in `RegionActualParts.lean`). -/
private theorem r8b_candidateR_nodes_lengthR (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec g comp index).nodes.length = comp.length := by
  cases spec with
  | none =>
    show (componentCandidate g comp index).nodes.length = comp.length
    rw [componentCandidate_nodes]
    show (comp.map fun v => g.nodes.getD v default).length = comp.length
    exact List.length_map ..
  | some _ =>
    show (componentGraph g comp).nodes.length = comp.length
    unfold componentGraph
    dsimp only
    exact List.length_map ..

/-- Rect-value source over the region execution (copy of the private
`xpptb_rect_value_source` in `ExactPackedTransportProof.lean`, via
`SceneExecutionR.parts_coverageR`, `actual_components_parts_geometryR`, and
`actual_components_packed_rect_valueR`). -/
private theorem r8b_rect_value_sourceR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {packed : Pack.State}
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    {k : Nat} (hk : k < execution.packedAcc.rects.size) {r : Rect}
    (hget : execution.packedAcc.rects.getD k default = r) :
    ∃ (pk : Nat) (part : List Nat × Part) (pos : Nat) (r0 box : Rect),
      execution.componentsAcc.parts[pk]? = some part ∧ part.1[pos]? = some k ∧
      part.2.rects[pos]? = some r0 ∧
      packed.boxes[pk]? = some box ∧
      r = shiftRect box.x box.y r0 := by
  have hsz : execution.componentsAcc.rects.size = inp.boxes.length :=
    execution.components_rects_sizeR
  have hpsz : execution.packedAcc.rects.size = inp.boxes.length :=
    r8b_packedAcc_rects_sizeR execution
  have hilt : k < execution.componentsAcc.rects.size := by omega
  have hrC : ∃ rC : Rect, execution.componentsAcc.rects[k]? = some rC :=
    ⟨_, Array.getElem?_eq_some_iff.mpr ⟨hilt, rfl⟩⟩
  obtain ⟨rC, hrC⟩ := hrC
  obtain ⟨part, hpartmem, entry, hentrymem, hentryfst⟩ :=
    execution.parts_coverageR k rC hrC
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨index, chosen, cg, run, loops, area, spec', _, _, _, _, hrun, _, hpartdef⟩ :=
    (actual_components_parts_geometryR hempty execution.components_eq).2 part hpartmem
  have hrectlen : part.2.rects.length = part.1.length := by
    rw [hpartdef]
    change (placeComponentExact execution.params cg run 0
      execution.measured loops).rects.length = part.1.length
    rw [r8b_placeComponentExact_rects_length, componentRunR_nodes_eq hrun,
      r8b_candidateR_nodes_lengthR]
  obtain ⟨pos, hpos1, hpos2⟩ := mem_zip_pairing hrectlen.symm entry hentrymem
  rw [hentryfst] at hpos1
  have hentry : (part.1.zip part.2.rects)[pos]? = some (k, entry.2) :=
    List.getElem?_zip_eq_some.mpr ⟨hpos1, hpos2⟩
  obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpartmem
  have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpacked, List.length_map]
  have hclen : c < execution.componentsAcc.parts.length :=
    (List.getElem?_eq_some_iff.mp hc).1
  have hcbox : c < packed.boxes.length := by
    rw [hlen]
    exact hclen
  have hboxget : packed.boxes[c]? = some packed.boxes[c] :=
    List.getElem?_eq_getElem hcbox
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
      some (part, packed.boxes[c]) :=
    List.getElem?_zip_eq_some.mpr ⟨hc, hboxget⟩
  have hsize : k < execution.componentsAcc.rects.size := by
    rw [hsz, ← hpsz]
    exact hk
  have hval := actual_components_packed_rect_valueR hempty execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hsize default
  rw [hval] at hget
  exact ⟨c, part, pos, entry.2, packed.boxes[c], hc, hpos1, hpos2, hboxget, hget.symm⟩

/-- The region component fold preserves the label array size (twin of
`X_components_fold_labels_size` in `ExactFlatC7.lean`, via
`layoutComponentR_sizes`). -/
private theorem r8b_components_fold_labels_sizeR (P : Params) (exactIds : List String)
    (spec : Option RegionSpec) (inp : Input) (o : Options) (g : Graph)
    (measured : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp measured)
        start = .ok out → out.labels.size = start.labels.size
  | [], start, out, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok h
    rw [r8b_components_fold_labels_sizeR P exactIds spec inp o g measured comps mid out hrest]
    exact (layoutComponentR_sizes hmid).2.2.symm

/-- The pack-step label fold preserves the array size (copy of the private
`xpr_packFold_labels_size_hold` in `ExactPackedTransportResidualsProof.lean`;
shared `packStep` geometry). -/
private theorem r8b_packFold_labels_size_hold
    (qs : List ((List Nat × Part) × Rect)) (arr : Array Rect) :
    (qs.foldl (fun a q => q.1.2.labels.foldl
      (fun a r => a.set! r.1 (shiftRect q.2.x q.2.y r.2)) a) arr).size =
      arr.size := by
  revert arr
  induction qs with
  | nil => intro arr; rfl
  | cons q rest ih =>
    intro arr
    rw [List.foldl_cons, ih]
    exact size_keyFold_rects_eq _ _ _

/-- If no region part of the executed fold carries a key, the fold leaves
that label entry at its starting (default) value. Specialization of the
shared `foldlM_labels_uncovered` to the region step, with the start
defaults from `layout_startAcc_defaults`. -/
private theorem r8b_execution_labels_default_of_no_carry
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {i : Nat}
    (hno : ∀ p ∈ execution.componentsAcc.parts, ∀ r0 : Rect,
      (i, r0) ∉ p.2.labels) :
    execution.componentsAcc.labels.getD i default = default := by
  have hcov := foldlM_labels_uncovered
    (fun acc comp => layoutComponentR execution.params exactIds _ inp o
      execution.graph acc comp execution.measured)
    (fun start comp acc' hc => layoutComponentR_labels_cover hc)
    (fun start comp acc' hc => layoutComponentR_parts_mono hc)
    (components execution.graph)
    _ _ execution.components_eq
    (fun j rr hj _ => (layout_startAcc_defaults inp).2.2 j rr hj)
  by_cases hsome : ∃ r, execution.componentsAcc.labels[i]? = some r
  · obtain ⟨r, hr⟩ := hsome
    have hnc : (∀ q ∈ execution.componentsAcc.parts,
          ¬ LabelCovered q.2.labels i) ∨
        i ≥ execution.componentsAcc.labels.size := by
      left
      intro q hq hcv
      obtain ⟨⟨a1, a2⟩, hmem, heq⟩ := hcv
      simp only at heq
      subst heq
      exact hno q hq a2 hmem
    have hdef : r = default := hcov i r hr hnc
    have hget : execution.componentsAcc.labels.getD i default = r := by
      simp [Array.getD_eq_getD_getElem?, hr]
    rw [hget, hdef]

  · have hnone : execution.componentsAcc.labels[i]? = none := by
      cases h : execution.componentsAcc.labels[i]? with
      | none => rfl
      | some r => exact absurd ⟨r, h⟩ hsome
    simp [Array.getD_eq_getD_getElem?, hnone]

/-- Region packed-label provenance holds outright: replay of
`X_packedLabelsTransport_closed` over `SceneExecutionR`. -/
private theorem r8b_packedLabelsTransport_closed (exactIds : List String)
    (idSets : List (String × List String)) :
    r8b_PackedLabelsTransport exactIds idSets := by
  intro inp o res execution
  obtain ⟨packed, hpackE, hlenE⟩ := r8b_packedShelfExistence_of_execution execution
  refine ⟨packed, hpackE, ?_⟩
  intro index r hget
  have hpackeq := execution.packed_eq
  unfold packAcc at hpackeq
  obtain ⟨packed', hpacked', hfold⟩ := bind_ok hpackeq
  have heq : packed = packed' := Except.ok.inj (hpackE.symm.trans hpacked')
  subst heq
  have hout : execution.packedAcc =
      (execution.componentsAcc.parts.zip packed.boxes).foldl packStep
        { execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] } := by
    have he := Except.ok.inj hfold
    rw [inlineFold_eq_packStep] at he
    exact he.symm
  have hlen : execution.componentsAcc.parts.length = packed.boxes.length := by
    rw [Pack.pack_count hpackE, List.length_map]
  have hcomplabelssize : execution.componentsAcc.labels.size = inp.labels.length := by
    have h := r8b_components_fold_labels_sizeR execution.params exactIds _
      inp o execution.graph execution.measured (components execution.graph) _ _
      execution.components_eq
    rw [h]
    simp
  by_cases hi : index < execution.componentsAcc.labels.size
  · have hprov := packFold_labels_provenance
      (execution.componentsAcc.parts.zip packed.boxes)
      { execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] }
      index r
      (by change index < execution.componentsAcc.labels.size; exact hi)
      (by rwa [← hout])
    rcases hprov with ⟨q, hqzip, r0, hmem, hr⟩ | ⟨hno, hst⟩
    · obtain ⟨pl, hplpart, hplbox⟩ := mem_zip_pairing hlen q hqzip
      exact Or.inl ⟨pl, q.1, r0, q.2, hplpart, hmem, hplbox, hr⟩
    · have hnoparts : ∀ p ∈ execution.componentsAcc.parts, ∀ r0 : Rect,
          (index, r0) ∉ p.2.labels := by
        intro p hpmem r0 hmem
        obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpmem
        have hcbox : c < packed.boxes.length := by
          rw [← hlen]
          exact (List.getElem?_eq_some_iff.mp hc).1
        have hboxget : packed.boxes[c]? = some packed.boxes[c] :=
          List.getElem?_eq_getElem hcbox
        have hqzip : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
            some (p, packed.boxes[c]) :=
          List.getElem?_zip_eq_some.mpr ⟨hc, hboxget⟩
        exact hno (p, packed.boxes[c]) (List.mem_of_getElem? hqzip) r0 hmem
      have hcomp := r8b_execution_labels_default_of_no_carry execution hnoparts
      have hst2 : execution.componentsAcc.labels.getD index default = r := hst
      rw [hcomp] at hst2
      exact Or.inr hst2.symm
  · have hle : execution.componentsAcc.labels.size ≤ index := by omega
    have hpacksize : execution.packedAcc.labels.size =
        execution.componentsAcc.labels.size := by
      rw [hout, pack_labels_eq_fold, r8b_packFold_labels_size_hold]
    have hle' : execution.packedAcc.labels.size ≤ index := by
      rw [hpacksize]; exact hle
    have hdef : execution.packedAcc.labels.getD index default = default :=
      array_getD_of_size_le hle'
    exact Or.inr (hget.symm.trans hdef)
/-- Pack titles fold (copy of the private `xpr_pack_titles_fold` in
`ExactPackedTransportResidualsProof.lean`; shared `packAcc` titles). -/
private theorem r8b_pack_titles_fold (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) :
    (pairs.foldl packStep start).titles =
      start.titles ++
        pairs.flatMap (fun pair => pair.1.2.titles.map
          (fun title => (pair.1.1.getD title.1 0,
            shiftRect pair.2.x pair.2.y title.2))) := by
  induction pairs generalizing start with
  | nil => simp
  | cons pair rest ih =>
    simp [List.foldl_cons, ih, packStep, List.append_assoc]

/-- Placed-component titles are the shared `componentTitles` shifted by the
exact placement bounds (copy of the private
`xpr_placeComponentExact_titles_eq` in
`ExactPackedTransportResidualsProof.lean`; shared `placeComponentExact`). -/
private theorem r8b_placeComponentExact_titles_eq (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).titles =
      (componentTitles P cg run).map (fun q =>
        (q.1, shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
          (-(placeBoundsX P cg run labels loops).minY) q.2)) := by
  simp only [placeComponentExact, placeBoundsX]



/-- Region packed-title membership holds outright: replay of
`X_packedTitlesMemSource_closed` over `SceneExecutionR`. -/
private theorem r8b_packedTitlesMemSource_closed (exactIds : List String)
    (idSets : List (String × List String)) :
    r8b_PackedTitlesMemSource exactIds idSets := by
  intro inp o res execution packed hpacked key stored hmem
  have hpackeq := execution.packed_eq
  unfold packAcc at hpackeq
  obtain ⟨packed', hpacked', hfold⟩ := bind_ok hpackeq
  have heqpacked : packed = packed' := Except.ok.inj (hpacked.symm.trans hpacked')
  subst heqpacked
  have hout : execution.packedAcc =
      (execution.componentsAcc.parts.zip packed.boxes).foldl packStep
        { execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] } :=
    (Except.ok.inj hfold).symm
  rw [hout, r8b_pack_titles_fold] at hmem
  have hstart : ({ execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] }).titles = [] := rfl
  rw [hstart, List.nil_append] at hmem
  obtain ⟨pair, hpair, htitle⟩ := List.mem_flatMap.mp hmem
  obtain ⟨⟨i, stored0⟩, ht, hteq⟩ := List.mem_map.mp htitle
  have hlen : execution.componentsAcc.parts.length = packed.boxes.length := by
    rw [Pack.pack_count hpacked, List.length_map]
  obtain ⟨pl, hplpart, hplbox⟩ := mem_zip_pairing hlen pair hpair
  have hkeyeq : pair.1.1.getD i 0 = key := congrArg Prod.fst hteq
  have hstoreq : shiftRect pair.2.x pair.2.y stored0 = stored := congrArg Prod.snd hteq
  have hpartmem : pair.1 ∈ execution.componentsAcc.parts := List.mem_of_getElem? hplpart
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨index, chosen, cg, run, loops, area, spec', _, _, _, _, hrun, _, hpartdef⟩ :=
    (actual_components_parts_geometryR hempty execution.components_eq).2 pair.1 hpartmem
  have ht2 : (i, stored0) ∈ (placeComponentExact execution.params cg run 0
      execution.measured loops).titles := by
    have h2 := ht
    rw [hpartdef] at h2
    exact h2
  rw [r8b_placeComponentExact_titles_eq] at ht2
  obtain ⟨raw, hraw, hreq⟩ := List.mem_map.mp ht2
  obtain ⟨top, htop, _, hindex, _, _⟩ := componentTitles_dimension_source
    execution.params cg run hraw
  have hi := (List.getElem?_eq_some_iff.mp
    (List.mem_zipIdx_iff_getElem?.mp htop)).1
  have hlen2 : cg.nodes.length = pair.1.1.length := by
    rw [componentRunR_nodes_eq hrun, r8b_candidateR_nodes_lengthR]
  have hkey : raw.1 = i := congrArg Prod.fst hreq
  have hi2 : i = top.2 := hkey.symm.trans hindex
  have hrange : i < pair.1.1.length := by
    rw [hi2, ← hlen2]
    exact hi
  have hgetElem : pair.1.1[i]? = some pair.1.1[i] :=
    List.getElem?_eq_getElem hrange
  have hgetD : pair.1.1.getD i 0 = pair.1.1[i] := by
    rw [List.getD_eq_getElem?_getD, hgetElem, Option.getD_some]
  have hget : pair.1.1[i]? = some key := by
    rw [← hkeyeq, hgetD]
    exact List.getElem?_eq_getElem hrange
  exact ⟨pl, pair.1, i, stored0, pair.2, hplpart, hget, ht, hplbox, hstoreq.symm⟩

/-- The caption resize commutes with the shelf translation (copy of the
private `b8_caption_shift_comm` in `ExactFlatC8b.lean`). -/
private theorem r8b_caption_shift_comm {stored : Rect} {dx dy w h : Int} :
    ({ shiftRect dx dy stored with w := w, h := h } : Rect) =
      shiftRect dx dy { stored with w := w, h := h } := rfl

/-- Two positions of a box list whose boxes share an id are equal (copy of
the private `b8_index_eq_of_id_eq` in `ExactFlatC8b.lean`). -/
private theorem r8b_index_eq_of_id_eq {l : List ModelBox}
    (hn : (l.map (·.id)).Nodup) {i j : Nat} {a b : ModelBox}
    (hi : l[i]? = some a) (hj : l[j]? = some b) (hid : a.id = b.id) : i = j := by
  have hin : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjn : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hil : i < (l.map (·.id)).length := by rw [List.length_map]; exact hin
  have hjl : j < (l.map (·.id)).length := by rw [List.length_map]; exact hjn
  have hget : (l.map (·.id))[i]? = (l.map (·.id))[j]? := by
    rw [List.getElem?_map, hi, List.getElem?_map, hj]
    simp only [Option.map_some]
    exact congrArg Option.some hid
  have hv : (l.map (·.id))[i] = (l.map (·.id))[j] := by
    have e1 : (l.map (·.id))[i]? = some ((l.map (·.id))[i]) :=
      List.getElem?_eq_getElem hil
    have e2 : (l.map (·.id))[j]? = some ((l.map (·.id))[j]) :=
      List.getElem?_eq_getElem hjl
    exact Option.some.inj (e1.symm.trans (hget.trans e2))
  have hp := List.pairwise_iff_getElem.mp hn
  by_cases hlt : i < j
  · exact absurd hv (hp i j hil hjl hlt)
  · by_cases hjt : j < i
    · exact absurd hv.symm (hp j i hjl hil hjt)
    · omega

/-- The region packed-part transport holds modulo the two narrow residuals:
replay of `X_packedPartTransportBounded_holds` over `SceneExecutionR`.
Shelf containment in every clause comes from the tracked `exactPartsBoundedR`
plus the base-independent shelf dimensions; the title clause additionally
consumes the title-membership and caption-fit residuals, and the label
clause consumes the label-provenance residual. -/
private theorem r8b_packedPartTransportBounded_holds
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hsize : R_PartSizingR execution)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets)
    (hlab : r8b_PackedLabelsTransport exactIds idSets)
    (htit : r8b_PackedTitlesMemSource exactIds idSets) :
    ∃ packed : Pack.State,
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (∀ (k : Nat), k < execution.packedAcc.rects.size → ∀ (r : Rect),
        execution.packedAcc.rects.getD k default = r →
        ∃ (pk : Nat) (part : List Nat × Part) (pos : Nat) (r0 box : Rect),
          execution.componentsAcc.parts[pk]? = some part ∧ part.1[pos]? = some k ∧
          part.2.rects[pos]? = some r0 ∧
          packed.boxes[pk]? = some box ∧
          r = shiftRect box.x box.y r0 ∧
          box.Contained r) ∧
      (∀ (index : Nat) (r : Rect), execution.packedAcc.labels.getD index default = r →
        (∃ (pl : Nat) (part : List Nat × Part) (r0 box : Rect),
          execution.componentsAcc.parts[pl]? = some part ∧
          (index, r0) ∈ part.2.labels ∧
          packed.boxes[pl]? = some box ∧
          r = shiftRect box.x box.y r0 ∧
          box.Contained r) ∨
        r = default) ∧
      (∀ (key : Nat) (stored : Rect), (key, stored) ∈ execution.packedAcc.titles →
        ∃ (pl : Nat) (part : List Nat × Part) (i : Nat) (stored0 box : Rect),
          execution.componentsAcc.parts[pl]? = some part ∧ part.1[i]? = some key ∧
          (i, stored0) ∈ part.2.titles ∧
          packed.boxes[pl]? = some box ∧
          stored = shiftRect box.x box.y stored0 ∧
          box.Contained
            (shiftRect box.x box.y
              { stored0 with
                w := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).w
                h := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).h })) ∧
      (∀ (k : Nat) (r : Rect), execution.packedAcc.rects.getD k default = r → 0 ≤ r.x) := by
  obtain ⟨packed, hpackE, hlabcl⟩ := hlab execution
  refine ⟨packed, hpackE, ?_, ?_, ?_, ?_⟩
  · intro k hk r hget
    obtain ⟨pk, part, pos, r0, box, hparts, hpos1, hpos2, hboxes, hreq⟩ :=
      r8b_rect_value_sourceR execution hpackE hk hget
    refine ⟨pk, part, pos, r0, box, hparts, hpos1, hpos2, hboxes, hreq, ?_⟩
    have hbnd := exactPartsBoundedR execution hsize part (List.mem_of_getElem? hparts)
    have hr0 := hbnd.2.2.1 r0 (List.mem_of_getElem? hpos2)
    have hdim := r8b_shelfDims_of_mem hpackE hparts hboxes
    unfold Rect.Contained
    rw [hreq]
    dsimp only [shiftRect]
    omega
  · intro index r hget
    rcases hlabcl index r hget with
      ⟨pl, part, r0, box, hparts, hmem, hboxes, hreq⟩ | hdef
    · refine Or.inl ⟨pl, part, r0, box, hparts, hmem, hboxes, hreq, ?_⟩
      have hbnd := exactPartsBoundedR execution hsize part (List.mem_of_getElem? hparts)
      have hr0 := hbnd.2.2.2.2.2 (index, r0) hmem
      have hr0' : 0 ≤ r0.x ∧ r0.x + r0.w ≤ part.2.width ∧
          0 ≤ r0.y ∧ r0.y + r0.h ≤ part.2.height :=
        ⟨hr0.1, hr0.2.1, hr0.2.2.1, hr0.2.2.2.1⟩
      have hdim := r8b_shelfDims_of_mem hpackE hparts hboxes
      unfold Rect.Contained
      rw [hreq]
      dsimp only [shiftRect]
      omega
    · exact Or.inr hdef
  · intro key stored hmem
    obtain ⟨pl, part, i, stored0, box, hparts, hkey, htmem, hboxes, hstored⟩ :=
      htit execution hpackE hmem
    refine ⟨pl, part, i, stored0, box, hparts, hkey, htmem, hboxes, hstored, ?_⟩
    have hpartmem := List.mem_of_getElem? hparts
    have hbnd := exactPartsBoundedR execution hsize part hpartmem
    have htB := hbnd.2.2.2.1 (i, stored0) htmem
    have htB' : 0 ≤ stored0.x ∧ stored0.x + stored0.w ≤ part.2.width ∧
        0 ≤ stored0.y ∧ stored0.y + stored0.h ≤ part.2.height :=
      ⟨htB.1, htB.2.1, htB.2.2.1, htB.2.2.2.1⟩
    have hfitX := hcap execution hpartmem htmem
    have hgetD : part.1.getD i 0 = key := by
      rw [List.getD_eq_getElem?_getD, hkey, Option.getD_some]
    dsimp only at hfitX
    rw [hgetD] at hfitX
    have hdim := r8b_shelfDims_of_mem hpackE hparts hboxes
    have hfitW : (titleCaptionSize execution.params o
        (execution.lines.getD key [])).w ≤ stored0.w := hfitX.2.2.1
    have hfitH : (titleCaptionSize execution.params o
        (execution.lines.getD key [])).h ≤ stored0.h := hfitX.2.2.2
    have hfitW0 : 0 ≤ (titleCaptionSize execution.params o
        (execution.lines.getD key [])).w := hfitX.1
    have hfitH0 : 0 ≤ (titleCaptionSize execution.params o
        (execution.lines.getD key [])).h := hfitX.2.1
    unfold Rect.Contained
    dsimp only [shiftRect]
    omega
  · intro k r hget
    by_cases hk : k < execution.packedAcc.rects.size
    · obtain ⟨pk, part, pos, r0, box, hparts, _, hpos2, hboxes, hreq⟩ :=
        r8b_rect_value_sourceR execution hpackE hk hget
      have hb := Pack.pack_bounds hpackE
      have hbx := (hb.2 box (List.mem_of_getElem? hboxes)).1
      have hbnd := exactPartsBoundedR execution hsize part (List.mem_of_getElem? hparts)
      have hr0 := hbnd.2.2.1 r0 (List.mem_of_getElem? hpos2)
      rw [hreq]
      dsimp only [shiftRect]
      omega
    · have hle : execution.packedAcc.rects.size ≤ k := by omega
      have h0 : r = default := by
        rw [← hget]
        exact array_getD_of_size_le hle
      have hdx : (default : Rect).x = 0 := rfl
      rw [h0]
      omega

/-! ## Packed transport, closed modulo the two narrow residuals. -/

/-- The region packed-part transport holds modulo the sizing and caption-fit
residuals: pack existence and the rect/label/title sources are proved
outright in-file (`r8b_packedLabelsTransport_closed`,
`r8b_packedTitlesMemSource_closed`); only the two narrow per-execution
residuals stay open. Twin of `X_packedPartTransportBounded_closed`. -/
theorem R_packedPartTransportBounded_closed (exactIds : List String)
    (idSets : List (String × List String))
    (hsize : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionR exactIds idSets inp o res),
      R_PartSizingR execution)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    R_PackedPartTransportBoundedB8 exactIds idSets := by
  intro inp o res execution
  exact r8b_packedPartTransportBounded_holds execution (hsize execution)
    hcap (r8b_packedLabelsTransport_closed exactIds idSets)
    (r8b_packedTitlesMemSource_closed exactIds idSets)

set_option maxHeartbeats 800000 in
/-- The packed-coordinate C8b core over the region execution: the R component
cores plus the R transport give `LabelFramePackedClear`. Replay of
`b8_labelFramePackedClear_of_bounded` in `ExactFlatC8b.lean`; every step is
generic shelf geometry once the transport supplies the part correspondence. -/
private theorem r8b_labelFramePackedClear_of_bounded {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hcores : R_ExecutedPartFrameCoresB8 exactIds idSets)
    (htransport : R_PackedPartTransportBoundedB8 exactIds idSets) :
    LabelFramePackedClear execution.params inp o execution.lines
      execution.packedAcc := by
  obtain ⟨packed, hpack, hrects, hlabels, htitles, hnonneg⟩ := htransport execution
  refine ⟨?_, ?_⟩
  · intro index k gBox hbox hrole
    dsimp only
    have hksize : k < execution.packedAcc.rects.size := by
      rw [r8b_packedAcc_rects_sizeR execution]
      exact (List.getElem?_eq_some_iff.mp hbox).1
    obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
      hrects k hksize (execution.packedAcc.rects.getD k default) rfl
    rw [hreq] at hboxk
    rcases hlabels index (execution.packedAcc.labels.getD index default) rfl with
      ⟨pl, partl, r0l, bl, hpartl, hmeml, hbl, hreql, hboxl⟩ | hdef
    · rw [hreql] at hboxl
      by_cases hpk : pk = pl
      · subst hpk
        obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
        obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
        obtain ⟨hcore, -⟩ := (hcores execution) partk (List.mem_of_getElem? hpartk)
        have hclr := hcore index r0l posk k gBox r0 hmeml hkeyk hbox hrole hr0
        rw [hreq, hreql]
        rcases hclr with h | h
        · exact Or.inl (disjoint_shiftRect h)
        · exact Or.inr (strictInside_shiftRect h)
      · have hpkL : pk < execution.componentsAcc.parts.length :=
          (List.getElem?_eq_some_iff.mp hpartk).1
        have hplL : pl < execution.componentsAcc.parts.length :=
          (List.getElem?_eq_some_iff.mp hpartl).1
        have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
          rw [Pack.pack_count hpack, List.length_map]
        have hpkBox : pk < packed.boxes.length := by omega
        have hplBox : pl < packed.boxes.length := by omega
        have hd : Disjoint bk bl := by
          have hd0 : Disjoint packed.boxes[pk] packed.boxes[pl] :=
            Pack.pack_boxes_disjoint hpack pk pl hpkBox hplBox hpk
          have hbk' : packed.boxes[pk] = bk := (List.getElem?_eq_some_iff.mp hbk).2
          have hbl' : packed.boxes[pl] = bl := (List.getElem?_eq_some_iff.mp hbl).2
          rw [hbk', hbl'] at hd0
          exact hd0
        rw [hreq, hreql]
        exact Or.inl (disjoint_of_contained_disjoint hboxk hboxl hd)
    · rw [hreq, hdef]
      exact Or.inl (disjoint_default_of_nonneg (by
        rw [← hreq]
        exact hnonneg k (execution.packedAcc.rects.getD k default) rfl))
  · intro key stored htitle k gBox hbox hrole
    dsimp only
    have hksize : k < execution.packedAcc.rects.size := by
      rw [r8b_packedAcc_rects_sizeR execution]
      exact (List.getElem?_eq_some_iff.mp hbox).1
    obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
      hrects k hksize (execution.packedAcc.rects.getD k default) rfl
    rw [hreq] at hboxk
    obtain ⟨pl, partl, i, stored0, bl, hpartl, hkeyi, hmeml, hbl, hstored, hboxCap⟩ :=
      htitles key stored htitle
    by_cases hpk : pk = pl
    · subst hpk
      obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
      obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
      obtain ⟨-, hcore⟩ := (hcores execution) partk (List.mem_of_getElem? hpartk)
      have hgetD : partk.1.getD i 0 = key := by
        simp only [List.getD, hkeyi, Option.getD_some]
      have hclr := hcore i stored0 posk k gBox r0 hmeml hkeyk hbox hrole hr0
      simp only [hgetD] at hclr
      rw [hreq, hstored, r8b_caption_shift_comm]
      rcases hclr with h | h
      · exact Or.inl (disjoint_shiftRect h)
      · exact Or.inr (strictInside_shiftRect h)
    · have hpkL : pk < execution.componentsAcc.parts.length :=
          (List.getElem?_eq_some_iff.mp hpartk).1
      have hplL : pl < execution.componentsAcc.parts.length :=
          (List.getElem?_eq_some_iff.mp hpartl).1
      have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
        rw [Pack.pack_count hpack, List.length_map]
      have hpkBox : pk < packed.boxes.length := by omega
      have hplBox : pl < packed.boxes.length := by omega
      have hd : Disjoint bk bl := by
        have hd0 : Disjoint packed.boxes[pk] packed.boxes[pl] :=
          Pack.pack_boxes_disjoint hpack pk pl hpkBox hplBox hpk
        have hbk' : packed.boxes[pk] = bk := (List.getElem?_eq_some_iff.mp hbk).2
        have hbl' : packed.boxes[pl] = bl := (List.getElem?_eq_some_iff.mp hbl).2
        rw [hbk', hbl'] at hd0
        exact hd0
      rw [hreq, hstored, r8b_caption_shift_comm]
      exact Or.inl (disjoint_of_contained_disjoint hboxk hboxCap hd)

set_option maxHeartbeats 1000000 in
/-- Clause 8, condition 2 of the layout validator for a successful region
`layoutRIds`: replay of `b8_layout_c8b` in `ExactFlatC8b.lean` over
`SceneExecutionR`, with `SceneExecutionR.boxes_eq_mapR` for the scene-box
lookup and the copied id-equality lemma. -/
private theorem r8b_layout_c8b {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hpack : LabelFramePackedClear execution.params inp o execution.lines
      execution.packedAcc)
    (hfall : R_FallbackCaptionClearB8 exactIds idSets)
    (hfit : InputFixedFit inp o)
    (hwf : WellFormed (inputModel inp o)) :
    Validator.C8b res.scene.layoutDump := by
  have hfallApp := hfall execution hfit
  obtain ⟨hpackLabels, hpackTitles⟩ := hpack
  have hidsNodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  intro g hgMem hgRole l hlMem
  simp only [Scene.layoutDump] at hgMem hlMem
  obtain ⟨sl, hsl, hlEq⟩ := List.mem_map.mp hlMem
  rw [execution.scene_eq] at hsl
  obtain ⟨qL, hqL, hemitted⟩ := List.mem_filterMap.mp hsl
  obtain ⟨source, indexL⟩ := qL
  have hsrcL : inp.labels[indexL]? = some source :=
    List.mem_zipIdx_iff_getElem?.mp hqL
  have hslRect : l.rect = sl.rect := by rw [← hlEq]
  rw [execution.boxes_eq_mapR] at hgMem
  obtain ⟨q, hq, hgeq⟩ := List.mem_map.mp hgMem
  obtain ⟨hgBox, hKey⟩ := q
  dsimp only [Prod.fst, Prod.snd] at hgeq hq
  have hk : inp.boxes[hKey]? = some hgBox := List.mem_zipIdx_iff_getElem?.mp hq
  have hgRole0 : g.role = hgBox.role.id := by
    rw [← hgeq]
  have hgroupRole : hgBox.role = BoxRole.group := by
    have hgid : hgBox.role.id = "group" := hgRole0.symm.trans hgRole
    cases hrole : hgBox.role with
    | node =>
      rw [hrole] at hgid
      simp only [BoxRole.id] at hgid
      exact absurd hgid (by decide)
    | group => rfl
  have hgRect : g.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin (orientRect o.direction
        execution.packedAcc.canvasH (execution.packedAcc.rects.getD hKey default)) := by
    rw [← hgeq]
  cases hexcl : inp.boxes.any (fun box : ModelBox =>
      box.id == source.owner && box.exclusive) with
  | true =>
    simp only [hexcl, ↓reduceIte] at hemitted
    cases hemitted
  | false =>
    simp only [hexcl] at hemitted
    cases hm : execution.measured.find?
        (fun item : MeasuredLabel => item.index == indexL) with
    | some measured =>
      have hpm := List.find?_some hm
      have hmIdx : measured.index = indexL := by simpa using hpm
      have hrel := hpackLabels indexL hKey hgBox hk hgroupRole
      simp only [hm] at hemitted
      have hlrect : sl.rect = shiftRect execution.params.canvasMargin
          execution.params.canvasMargin (orientRect o.direction
            execution.packedAcc.canvasH
            (execution.packedAcc.labels.getD indexL default)) := by
        have heq' := Option.some.inj hemitted
        have hrr := (congrArg (fun s : SceneLabel => s.rect) heq').symm
        dsimp only at hrr
        rw [hrr, hmIdx]
      rw [hslRect, hgRect, hlrect]
      cases hrel with
      | inl h => exact Or.inl (disjoint_sceneTransport h)
      | inr h => exact Or.inr (strictInside_sceneTransport h)
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx? (fun box : ModelBox =>
          box.id == source.owner && !box.exclusive) with
      | none =>
        simp only [ho] at hemitted
        cases hemitted
      | some ownerIndex =>
        simp only [ho] at hemitted
        obtain ⟨hb, hownerPred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp ho
        have hobGet : inp.boxes[ownerIndex]? = some inp.boxes[ownerIndex] :=
          List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩
        have hownerId : inp.boxes[ownerIndex].id = source.owner := by
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hownerPred
          exact hownerPred.1
        have heq := hemitted
        have hselD : (sceneTitlesExpr execution.params inp o execution.lines
            execution.packedAcc).find? (fun t => t.1 == source.owner) = none ∨
            ∃ t : String × Rect,
              (sceneTitlesExpr execution.params inp o execution.lines
                execution.packedAcc).find? (fun t => t.1 == source.owner) = some t := by
          cases h : (sceneTitlesExpr execution.params inp o execution.lines
              execution.packedAcc).find? (fun t => t.1 == source.owner) with
          | none => exact Or.inl rfl
          | some t => exact Or.inr ⟨t, rfl⟩
        cases hselD with
        | inl hsel =>
          have hgMemScene : g ∈ res.scene.boxes := by
            rw [execution.scene_eq]
            exact List.mem_map.mpr ⟨(hgBox, hKey), hq, hgeq⟩
          have hlrect : sl.rect = ownedTextRect execution.params
              ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                ownerIndex ⟨"", "", default, "", false⟩)
              (execution.lines.getD ownerIndex []) := by
            have heq' := Option.some.inj heq
            have hrr := (congrArg (fun s : SceneLabel => s.rect) heq').symm
            dsimp only at hrr
            rw [hrr]
            show (Option.map (fun x => x.snd)
                ((sceneTitlesExpr execution.params inp o execution.lines
                  execution.packedAcc).find? (fun t => t.1 == source.owner))).getD
                (ownedTextRect execution.params
                  ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                    ownerIndex ⟨"", "", default, "", false⟩)
                  (execution.lines.getD ownerIndex [])) =
              ownedTextRect execution.params
                ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                  ownerIndex ⟨"", "", default, "", false⟩)
                (execution.lines.getD ownerIndex [])
            rw [hsel]
            rfl
          rw [hslRect, hlrect]
          exact hfallApp source indexL ownerIndex g hsrcL ho hsel hgMemScene hgRole
        | inr hts =>
          have hts' : ∃ t : String × Rect,
              (sceneTitlesExpr execution.params inp o execution.lines
                execution.packedAcc).find? (fun t => t.1 == source.owner) = some t := hts
          obtain ⟨tsel, hsel⟩ := hts'
          have hselMem := List.mem_of_find?_eq_some hsel
          obtain ⟨stored, hstoredMem, hfeq⟩ := List.mem_filterMap.mp hselMem
          cases hbx : inp.boxes[stored.1]? with
          | none => simp only [hbx] at hfeq; cases hfeq
          | some box0 =>
            simp only [hbx] at hfeq
            have hpair := Option.some.inj hfeq
            have htid : box0.id = tsel.1 := congrArg Prod.fst hpair
            have htrect : shiftRect execution.params.canvasMargin
                execution.params.canvasMargin (orientRect o.direction
                  execution.packedAcc.canvasH
                  { stored.2 with
                    w := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).w
                    h := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).h }) = tsel.2 :=
              congrArg Prod.snd hpair
            have hselKey : tsel.1 = source.owner := by
              simpa using List.find?_some hsel
            have hid' : box0.id = inp.boxes[ownerIndex].id :=
              htid.trans (hselKey.trans hownerId.symm)
            have hkeyEq : stored.1 = ownerIndex :=
              r8b_index_eq_of_id_eq hidsNodup hbx hobGet hid'
            have hrel := hpackTitles stored.1 stored.2 hstoredMem hKey hgBox hk hgroupRole
            have hlrect : sl.rect = shiftRect execution.params.canvasMargin
                execution.params.canvasMargin (orientRect o.direction
                  execution.packedAcc.canvasH
                  { stored.2 with
                    w := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).w
                    h := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).h }) := by
              have heq' := Option.some.inj heq
              have hrr := (congrArg (fun s : SceneLabel => s.rect) heq').symm
              dsimp only at hrr
              rw [hrr]
              show (Option.map (fun x => x.snd)
                  ((sceneTitlesExpr execution.params inp o execution.lines
                    execution.packedAcc).find? (fun t => t.1 == source.owner))).getD
                (ownedTextRect execution.params
                  ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                    ownerIndex ⟨"", "", default, "", false⟩)
                  (execution.lines.getD ownerIndex [])) =
                shiftRect execution.params.canvasMargin
                  execution.params.canvasMargin (orientRect o.direction
                    execution.packedAcc.canvasH
                    { stored.2 with
                      w := (titleCaptionSize execution.params o
                        (execution.lines.getD stored.1 [])).w
                      h := (titleCaptionSize execution.params o
                        (execution.lines.getD stored.1 [])).h })
              rw [hsel]
              show tsel.2 = _
              rw [← htrect]
            rw [hslRect, hgRect, hlrect]
            cases hrel with
            | inl h => exact Or.inl (disjoint_sceneTransport h)
            | inr h => exact Or.inr (strictInside_sceneTransport h)

/-- Flat C8b for the region pipeline: every successful `layoutRIds` keeps
every group frame disjoint from every scene label or strictly containing it,
modulo the core, fallback, sizing, and caption-fit residuals. -/
theorem flatC8bB_layoutRIds (exactIds : List String)
    (idSets : List (String × List String))
    (hcores : R_ExecutedPartFrameCoresB8 exactIds idSets)
    (hfall : R_FallbackCaptionClearB8 exactIds idSets)
    (hsize : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionR exactIds idSets inp o res),
      R_PartSizingR execution)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    FlatC8bB (PipelineImpl.layoutRIds exactIds idSets) := by
  intro inp o res hwf _hfp hfit h
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hpack := r8b_labelFramePackedClear_of_bounded execution hcores
    (R_packedPartTransportBounded_closed exactIds idSets hsize hcap)
  exact r8b_layout_c8b execution hpack hfall hfit hwf

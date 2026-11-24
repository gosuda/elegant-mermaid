import Elegant.Layered.CaptionResidualsProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.SizingCoverageBridge
import Elegant.Layered.RecursiveC2
import Elegant.Layered.LabelsC8b
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.CaptionOwnerScopeFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Same-part title clearance

`TitleExclusiveSamePart` (`Layered/CaptionResidualsProof.lean`) is the
same-part caption residual: the packed title caption of a group misses the
packed rect of every exclusive box in its own part. It follows from one
executed band fact, transported without new geometry: the title band is
part-local (`layoutComponent` output, before packing); the same shelf shift
applies to both rects, so `shiftRect_disjoint_of` lifts it to the packed
accumulator. (`DescendantFallbackClear`, the fallback-caption residual,
holds vacuously by `descendantFallbackClear_vacuous` in
`CaptionFallbackOwnerProof.lean` and is not transported here.)
-/

/-- Part-local title band: within one executed part, the substituted title
caption (the exact `titleCaptionSize` substitution `sceneOf` performs) is
disjoint from the part rect of every exclusive model box. This is strictly
simpler than `TitleExclusiveSamePart`: no `Pack.pack` shelf, no packed
accumulator, no part-index equality — one `layoutComponent` phase, pinned
by the `SceneExecution`. It is true on executed layouts: the probe
`proofs/wip/Probe/CaptionSamePartProbe.lean` checks the part-local (and
packed) disjointness on a titled group with one exclusive member, a group
whose title is wider than its members, nested titled groups, sibling
wide-titled groups (vector `TB`/`LR` and cell profiles), and a
two-component input — zero violations. -/
def TitleSamePartBand (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res)
    (c : Nat) (part : List Nat × Part),
    execution.componentsAcc.parts[c]? = some part →
    ∀ (title : Nat × Rect), title ∈ part.2.titles →
      ∀ (posB : Nat) (k : Nat) (rect : Rect),
        part.1[posB]? = some k →
        part.2.rects[posB]? = some rect →
        ∀ (fBox : ModelBox), inp.boxes[k]? = some fBox →
          fBox.exclusive = true →
          Disjoint rect
            { title.2 with
              w := (titleCaptionSize execution.params o
                (execution.lines.getD (part.1.getD title.1 0) [])).w
              h := (titleCaptionSize execution.params o
                (execution.lines.getD (part.1.getD title.1 0) [])).h }

/-- Same-part title clearance from the part-local band: equal part indices
give equal parts and shelves, so both packed rects are the same shelf
shift of the part rects and the shift preserves the band disjointness.
No `WellFormed` or `framedParents` premise is needed. -/
theorem titleExclusiveSamePart {inp : Input} {o : Options} {res : FamilyResult}
    (hband : TitleSamePartBand inp o res) :
    TitleExclusiveSamePart inp o res := by
  intro _hwf execution _key _stored _hmem _k _fBox hbox hex _packed hpack
    _cT _partT _boxT _title hzipT htitleMem hkeyEq hstoredEq
    _cB _partB _posB hcB hposB _heq
  subst _heq
  have hzipParts : execution.componentsAcc.parts[_cT]? = some _partT :=
    (List.getElem?_zip_eq_some.mp hzipT).1
  have hpartEq : _partT = _partB := Option.some.inj (hzipParts.symm.trans hcB)
  subst hpartEq
  have hpartmem : _partT ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? hcB
  obtain ⟨_, _, _, _, _, _, heqPart, _, _, _, _⟩ :=
    execution.actual_component_sizing hpartmem
  have hrectlen : _partT.2.rects.length = _partT.1.length := by
    rw [heqPart]
    simp [placeComponent, componentCandidate_nodes, componentGraph]
  have hposLen : _posB < _partT.1.length :=
    (List.getElem?_eq_some_iff.mp hposB).1
  have hrectLen : _posB < _partT.2.rects.length := by omega
  obtain ⟨rect, hrect⟩ : ∃ rect, _partT.2.rects[_posB]? = some rect :=
    ⟨_, List.getElem?_eq_getElem hrectLen⟩
  have hband' := hband execution _cT _partT hcB _title htitleMem
    _posB _k rect hposB hrect _fBox hbox hex
  rw [← hkeyEq] at hband'
  have hkLen : _k < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hbox).1
  have hsize : _k < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkLen
  have hentry : (_partT.1.zip _partT.2.rects)[_posB]? = some (_k, rect) :=
    List.getElem?_zip_eq_some.mpr ⟨hposB, hrect⟩
  have hrectEq := actual_components_packed_rect_value
    (by rfl : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [],
      Array.replicate inp.labels.length default, false, [], []⟩ : Acc).parts = [])
    execution.components_eq execution.packed_eq _packed hpack
    hzipT hentry hsize default
  have hshiftUpd : ({shiftRect _boxT.x _boxT.y _title.2 with
      w := (titleCaptionSize execution.params o (execution.lines.getD _key [])).w
      h := (titleCaptionSize execution.params o (execution.lines.getD _key [])).h}) =
      shiftRect _boxT.x _boxT.y {_title.2 with
      w := (titleCaptionSize execution.params o (execution.lines.getD _key [])).w
      h := (titleCaptionSize execution.params o (execution.lines.getD _key [])).h} := by
    cases _title.2 with
    | mk x y w h => rfl
  rw [hrectEq, hstoredEq, hshiftUpd]
  exact shiftRect_disjoint_of _ _ hband'

/-! ### Run-level title-band residual and the band theorem -/

/-- Run-level title-band residual: the geometric core behind the same-part
title band. The stored title caption misses every exclusive plain frame of
the same run (no containment or scope condition — the probe finds zero
violations for members and unrelated boxes alike, including sibling
wide-titled groups and both profiles). It is strictly simpler than the
part-level band (run geometry, pinned by the `SceneExecution`); the missing
proof is the oriented title-band separation inside `componentRun` (rank
bands for members, caption containment plus foreign span separation for
non-members). The fallback conjunct is redundant: `DescendantFallbackClear`
holds vacuously by `descendantFallbackClear_vacuous`. -/
def RunTitleBandClear (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  (∀ (execution : SceneExecution inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {ord : OrderOptions},
    componentRun execution.params
      (componentCandidate execution.graph comp candidate)
      execution.measured ord = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate execution.graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    ∀ (raw : Nat × Rect),
    raw ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run →
    raw.1 = v →
    ∀ {w : Nat} {nodeW : Node} {k : Nat} {fBox : ModelBox},
    (componentCandidate execution.graph comp candidate).nodes[w]? = some nodeW →
    nodeW.border = 0 →
    comp[w]? = some k →
    inp.boxes[k]? = some fBox →
    fBox.exclusive = true →
    Disjoint (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run w)
      { raw.2 with
        w := (titleCaptionSize execution.params o
          (execution.lines.getD (comp.getD raw.1 0) [])).w
        h := (titleCaptionSize execution.params o
          (execution.lines.getD (comp.getD raw.1 0) [])).h })

/-- An exclusive source box of a successful execution is a border-0 node of
the measured graph at the same index (local copy of the private `FlatC2`
helper). -/
private theorem samePart_member_border_zero {inp : Input} {o : Options} {res : FamilyResult} (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hlinesLen : execution.lines.length = inp.boxes.length)
    {k : Nat} {fBox : ModelBox} (hbox : inp.boxes[k]? = some fBox)
    (hex : fBox.exclusive = true) :
    ∃ node, execution.graph.nodes[k]? = some node ∧ node.border = 0 := by
  have hrole : fBox.role ≠ .group :=
    wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hbox) hex
  have hkeyLen : k < execution.lines.length := by
    rw [hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hbox).1
  have hline : execution.lines[k]? = some execution.lines[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hkeyLen, rfl⟩
  exact measuredGraph_exclusive_node_border_zero execution.checked
    execution.graph_eq hline hbox hrole

/-- The placed rect of component position `i` is the run's frame rectangle
shifted by the placement origin (local copy of the private `RankSiblingDisjoint`
helper, cursor fixed to `0` as in `placePart`). -/
private theorem samePart_place_rects_get (P : Params) (cg : Graph)
    (run : Run) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponent P cg run 0 labels loops).rects[i]? =
      some (shiftRect (0 - (placeBounds P cg run labels loops).minX)
        (0 - (placeBounds P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponent placeBounds
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- The same-part title band from the run-level band: equal part indices give
one run, so both part rects are the same placement shift of the run-level
rects and the shift preserves the residual disjointness. No `Pack` shelf
reasoning is needed. -/
theorem titleSamePartBand_of_runBand {inp : Input} {o : Options} {res : FamilyResult}
    (hrun : RunTitleBandClear inp o res)
    (hwf : WellFormed (inputModel inp o)) :
    TitleSamePartBand inp o res := by
  intro execution c part hpart title htitle posB k rect hpos hrect fBox hbox hex
  have hpartmem : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hpart
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    unfold boxLines at hl
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (mapM_getElem? _ _ _ hl).1
      _ = inp.boxes.length := List.length_zipIdx
  obtain ⟨hmap, _⟩ := actual_components_parts_geometry (by rfl : (⟨0, 0, 0, Array.replicate inp.boxes.length default, Array.replicate inp.routes.length [], Array.replicate inp.labels.length default, false, [], []⟩ : Acc).parts = []) execution.components_eq
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨part, hpartmem, rfl⟩
  obtain ⟨index, run, loops, area, hrunEx, _, heqPart, _, _, _, _⟩ :=
    execution.actual_component_sizing hpartmem
  rw [heqPart] at htitle
  change title ∈ (componentTitles execution.params (componentCandidate execution.graph part.1 index) run).map (fun q => (q.1, shiftRect (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minX) (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minY) q.2)) at htitle
  obtain ⟨raw, hraw, heTitle⟩ := List.mem_map.mp htitle
  have htitle1 : raw.1 = title.1 := by rw [← heTitle]
  have htitle2 : shiftRect (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minX) (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minY) raw.2 = title.2 := by rw [← heTitle]
  obtain ⟨top, htopmem, htopborder, htopidx, _, _⟩ :=
    componentTitles_dimension_source execution.params _ _ hraw
  have htopnode : (componentCandidate execution.graph part.1 index).nodes[top.2]? = some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp htopmem
  have hcgLen : (componentCandidate execution.graph part.1 index).nodes.length = part.1.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have hposLen : posB < part.1.length := (List.getElem?_eq_some_iff.mp hpos).1
  have hwLen : posB < (componentCandidate execution.graph part.1 index).nodes.length := by omega
  obtain ⟨nodeW, hnodeW⟩ : ∃ nodeW, (componentCandidate execution.graph part.1 index).nodes[posB]? = some nodeW :=
    ⟨_, List.getElem?_eq_getElem hwLen⟩
  obtain ⟨gnode, hgnode, hb0⟩ := samePart_member_border_zero execution hwf hlinesLen hbox hex
  have hcglookup : (componentCandidate execution.graph part.1 index).nodes[posB]? =
      some (execution.graph.nodes.getD k default) := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.getElem?_map, hpos, Option.map_some]
  have hgetD : execution.graph.nodes.getD k default = gnode := by
    rw [List.getD_eq_getElem?_getD, hgnode]
    rfl
  have hnodeWg : nodeW = gnode := by
    have heq2 : nodeW = execution.graph.nodes.getD k default :=
      Option.some.inj (hnodeW.symm.trans hcglookup)
    rw [hgetD] at heq2
    exact heq2
  have hnodeW0 : nodeW.border = 0 := by rw [hnodeWg]; exact hb0
  have hband := hrun execution hcomp hrunEx htopnode htopborder raw hraw htopidx hnodeW hnodeW0 hpos hbox hex
  rw [htitle1] at hband
  have hframeEq := samePart_place_rects_get execution.params
    (componentCandidate execution.graph part.1 index) run execution.measured loops hwLen
  have hupd : ({placeComponent execution.params (componentCandidate execution.graph part.1 index) run 0 execution.measured loops with area := area} : Part).rects = (placeComponent execution.params (componentCandidate execution.graph part.1 index) run 0 execution.measured loops).rects := rfl
  have hpartRect : part.2.rects[posB]? = some (shiftRect (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minX) (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minY) (frameRect execution.params (componentCandidate execution.graph part.1 index) run posB)) := by
    rw [heqPart, hupd]
    exact hframeEq
  have hrectEq : rect = shiftRect (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minX) (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minY) (frameRect execution.params (componentCandidate execution.graph part.1 index) run posB) :=
    Option.some.inj (hrect.symm.trans hpartRect)
  have hshiftUpd : ({shiftRect (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minX) (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minY) raw.2 with w := (titleCaptionSize execution.params o (execution.lines.getD (part.1.getD title.1 0) [])).w, h := (titleCaptionSize execution.params o (execution.lines.getD (part.1.getD title.1 0) [])).h}) = shiftRect (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minX) (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index) run execution.measured loops).minY) {raw.2 with w := (titleCaptionSize execution.params o (execution.lines.getD (part.1.getD title.1 0) [])).w, h := (titleCaptionSize execution.params o (execution.lines.getD (part.1.getD title.1 0) [])).h} := by
    cases raw.2 with
    | mk x y w h => rfl
  rw [hrectEq, ← htitle2, hshiftUpd]
  exact shiftRect_disjoint_of _ _ hband


end Elegant.Layered.PipelineImpl

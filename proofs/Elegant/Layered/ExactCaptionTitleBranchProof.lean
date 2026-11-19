import Elegant.Layered.ExactCaptionFitFactsProof
import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.ExactPackedTransportResidualsProof
import Elegant.Layered.ExactPackedTransportProof
import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.InputFixedFit
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.LabelsC8b
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.PartSeparation
import Elegant.Layered.Pack
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.SizingFacts
import Elegant.Layered.PlainNodeSizingFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.SceneBounds
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExactPipeline
import Elegant.Model

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact caption title branch and fallback containment (`capTitle`, `capContainW`).

Leaf defs (in `ExactFlatC7CaptionScope.lean:139` and
`ExactCaptionFitFactsProof.lean:256`):

* `X_CaptionTitleBranchClear exactIds` (field `capTitle`): the installed-title
  branch of the caption scope clearance.
* `X_OwnerCaptionContainFallbackFitW exactIds` (field `capContainW`): the
  fallback caption containment under the local `InputFixedFit` premise.

Probe evidence (`proofs/wip/Probe/ExactCaptionTitleBranchTProbe.lean`,
vector profile, `layoutX [] inp tOpts` recompute; owner box `box=(w,h)`,
fallback caption `cap=(w,h)`):

* `fb-fit-5000` (fixed `5000x5000`): contained `true` (fit holds);
* `fb-fixed-0x0` (fixed `0x0`): contained `false`, caption `(0,1280)`
  (bare fit is FALSE; the `W` form is vacuous here since `InputFixedFit`
  fails the `0 <= size` side);
* `fb-wide-short` (`5000x200`): contained `false`, caption `(2952,1280)`;
* `fb-narrow-tall` (`300x5000`): contained `false`, caption `(0,1280)`;
* `fb-nest-fit` (nested fixed `5000x5000`): contained `true`;
* `fb-empty-title`, `fb-nofix` (installed title): contained `true`;
* `fb-self-loop` (self-loop route on `a`): contained `true`;
* `fb-dup-id` (duplicate box id, ill-formed): contained `true`;
* `caps-empty-title`, `caps-nofix` (installed title, exclusive `x`):
  `hit=false`;
* `caps-self-loop`, `caps-nest-fit`, `caps-fit-5000`: no outside-scope
  exclusive hit.

What closes here: the ordinary node sizing (`X_OrdinaryBoxLineHeightX`), the
fixed-owner fit (`X_FixedOwnerFitX`), and the cross-part title disjointness
(`X_TitleExclusiveCrossPartX`) replay their plain twins over
`SceneExecutionX` with shared measured-graph lemmas. The installed-title
band (`X_TitleSamePartBandX`) and the fallback-owner cases
(`X_FallbackOwnerCasesX`) stay open: each is one strictly narrower named
residual (part-level band geometry, resp. owner role classification), true
on every probe row above.
-/

/-- `xctb_` copy of the private `X_packFold_rects_size`
(`ExactFitClosure.lean:772`): packing preserves the rect array size. -/
private theorem xctb_packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

/-- Exact packed rect array size (copy of the private `X_packed_rects_size`
(`ExactFitClosure.lean:783`) with the exact components fold). -/
private theorem xctb_packed_rects_size {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
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
  rw [xctb_packFold_rects_size]
  exact execution.components_rects_size

/-- Exact packed rect existence (copy of the private `X_packed_rect_exists`
(`ExactFitClosure.lean:800`)). -/
private theorem xctb_packed_rect_exists {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {i : Nat} (hi : i < inp.boxes.length) :
    ∃ rect, execution.packedAcc.rects[i]? = some rect := by
  have hsize : i < execution.packedAcc.rects.size := by
    rw [xctb_packed_rects_size execution]
    exact hi
  exact ⟨execution.packedAcc.rects[i],
    Array.getElem?_eq_some_iff.mpr ⟨hsize, rfl⟩⟩

/-- `xctb_` copy of `xcf_box_index_origin`
(`ExactCaptionFitFactsProof.lean:92`) over `SceneExecutionX`: the scene box
at `index` comes from the input box at the same index. -/
private theorem xctb_box_index_origin {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {index : Nat} {box : Box}
    (hbox : res.scene.boxes[index]? = some box) :
    ∃ source, inp.boxes[index]? = some source ∧
      box = Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD index default)))
        source.parent source.exclusive := by
  rw [execution.boxes_eq_mapX] at hbox
  cases hs : inp.boxes[index]? with
  | none => simp [hs] at hbox
  | some source =>
    refine ⟨source, rfl, ?_⟩
    simpa [hs] using hbox.symm

/-- `xctb_` lines-length fact (copy of `xcf_lines_length`,
`ExactCaptionFitFactsProof.lean:152`): the exact execution lines align with
the model boxes. -/
private theorem xctb_lines_length {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have hl := execution.lines_eq
  unfold boxLines at hl
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
      (mapM_getElem? _ _ _ hl).1
    _ = inp.boxes.length := List.length_zipIdx

/-- Part rects of an exact component are shifted `frameRect`s (copy of the
private `X_placeComponentExact_rects_get`, `ExactFitClosure.lean:882`). -/
private theorem xctb_placeComponentExact_rects_get {P : Params} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {cursor : Int} {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Coordinate construction through `coordinateGraphX` preserves the anchor
node dimensions (copy of `X_coordinateGraphX_plain_anchor_dims`,
`ExactFitClosure.lean:895`). -/
private theorem xctb_coordinateGraphX_plain_anchor_dims (P : Params)
    {exact : List Nat} {p : Proper} {i : Nat} {nd : ProperNode}
    (hp : p.nodes[i]? = some nd) (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
  obtain ⟨sized, hs, he, hb', hw, hh⟩ :
      ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
        sized.edge = nd.edge ∧ sized.node.border = 0 ∧
        nd.node.w ≤ sized.node.w ∧ sized.node.h = nd.node.h := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, rfl, hb, Int.le_refl _, rfl⟩
    · refine ⟨_, rfl, rfl, hb, ?_, rfl⟩
      exact Int.le_max_left _ _
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? =
      some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? =
        some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split <;> exact ⟨_, rfl, he, hb', hw, hh⟩

/-- Proxy materialization keeps the X coordinate anchor (copy of
`X_componentRun_plain_node_dims`, `ExactFitClosure.lean:934`). -/
private theorem xctb_componentRun_plain_node_dims {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode}
    (hnode : run.coordinateProper.nodes[i]? = some nd)
    (hborder : nd.node.border = 0) :
    run.proper.nodes[i]? = some nd := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have hprojected := proxyWidths_plain_node hproxy hnode hborder
  rw [← hdrop]
  exact hprojected

/-- Coordinate anchor dimensions through the exact run (copy of
`X_componentRun_coordinateGraph_plain_node_dims`,
`ExactFitClosure.lean:948`). -/
private theorem xctb_componentRun_coordinateGraph_plain_node_dims {P : Params}
    {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {p : Proper} (hcoordinate : coordinateGraphX P exact p = run.coordinateProper)
    {i : Nat} {nd : ProperNode}
    (hnode : p.nodes[i]? = some nd) (hborder : nd.node.border = 0) :
    ∃ out, run.proper.nodes[i]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
  obtain ⟨out, hout, hedge, hplain, hw, hh⟩ :=
    xctb_coordinateGraphX_plain_anchor_dims P hnode hborder
  rw [hcoordinate] at hout
  exact ⟨out, xctb_componentRun_plain_node_dims h hout hplain, hedge,
    hplain, hw, hh⟩

/-- Exact run proper nodes dominate the source graph nodes (copy of
`X_componentRun_original_node_dims`, `ExactFitClosure.lean:965`). -/
private theorem xctb_componentRun_original_node_dims {P : Params}
    {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node)
    (hb : node.border = 0) :
    ∃ out, run.proper.nodes[i]? = some out ∧ out.edge = none ∧
      out.node.border = 0 ∧ node.w ≤ out.node.w ∧ out.node.h = node.h := by
  obtain ⟨_, _, _, _, hnormalize, hlabels, hcoordinate, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec h
  have hp := normalize_node_record hnormalize hn
  have hl := addLabelNodes_untouched_node hlabels hp rfl
  exact xctb_componentRun_coordinateGraph_plain_node_dims h hcoordinate hl hb

/-- Exact `frameRect` dimensions dominate the source node dimensions (copy of
`X_componentRun_original_frame_minimum_dims`,
`ExactFitClosure.lean:980`). -/
private theorem xctb_componentRun_original_frame_minimum_dims {P : Params}
    {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node)
    (hb : node.border = 0) :
    node.w ≤ (frameRect P cg run i).w ∧ node.h ≤ (frameRect P cg run i).h := by
  obtain ⟨out, hout, _, _, hw, hh⟩ :=
    xctb_componentRun_original_node_dims h hn hb
  have hget : cg.nodes.getD i default = node := by
    simp only [List.getD_eq_getElem?_getD, hn, Option.getD_some]
  have hplain : (cg.nodes.getD i default).border ≠ -2 := by
    rw [hget, hb]
    decide
  have hdims := frameRect_plain_dims P cg run i out hplain hout
  refine ⟨hdims.1.symm ▸ hw, ?_⟩
  rw [hdims.2, hh]
  exact Int.le_refl _

/-- Exact part rects dominate the source graph node dimensions (copy of
`X_component_rect_minimum_dims`, `ExactFitClosure.lean:999`). -/
private theorem xctb_component_rect_minimum_dims {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {i key : Nat} (hkey : part.1[i]? = some key)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = 0)
    {rect : Rect} (hrect : part.2.rects[i]? = some rect) :
    node.w ≤ rect.w ∧ node.h ≤ rect.h := by
  obtain ⟨index, _chosen, run, loops, _area, _, _, _, hrun, _hloops, hpartdef⟩ :=
    (actual_components_parts_geometryX (rfl : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = []) execution.components_eq).2 part hpart
  have hnodes : (componentCandidate execution.graph part.1 index).nodes =
      part.1.map (fun key => execution.graph.nodes.getD key default) := by
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  have hlocal : (componentCandidate execution.graph part.1 index).nodes[i]? =
      some node := by
    rw [hnodes]
    simp only [List.getElem?_map, hkey, Option.map_some,
      List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hminimum :=
    xctb_componentRun_original_frame_minimum_dims hrun hlocal hborder
  have hi : i < (componentCandidate execution.graph part.1 index).nodes.length :=
    (List.getElem?_eq_some_iff.mp hlocal).1
  have hrectEq : part.2.rects[i]? =
      some (shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
        (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
        (frameRect execution.params
          (componentCandidate execution.graph part.1 index) run i)) := by
    rw [hpartdef]
    exact xctb_placeComponentExact_rects_get hi
  have heq : rect = shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i) :=
    Option.some.inj (hrect.symm.trans hrectEq)
  have hwS : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i)).w =
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i).w := rfl
  have hhS : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i)).h =
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i).h := rfl
  rw [heq, hwS, hhS]
  exact hminimum

/-- Packed rects dominate node dimensions over the exact execution (copy of
`SceneExecution.packed_rect_minimum_dims_of_coverage`,
`SizingFacts.lean:775`, with the exact part geometry). -/
private theorem xctb_packed_rect_minimum_dims_of_coverage
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hcoverage : ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      ∃ part ∈ execution.componentsAcc.parts,
        ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i)
    {key : Nat} {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = 0)
    {rect : Rect} (hrect : execution.packedAcc.rects[key]? = some rect) :
    node.w ≤ rect.w ∧ node.h ≤ rect.h := by
  let minimum : Nat → Size := fun i =>
    match execution.graph.nodes[i]? with
    | some n => if n.border = 0 then ⟨n.w, n.h⟩ else ⟨0, 0⟩
    | none => ⟨0, 0⟩
  have hparts : ∀ part ∈ execution.componentsAcc.parts,
      ∀ entry ∈ part.1.zip part.2.rects,
      (minimum entry.1).w ≤ entry.2.w ∧ (minimum entry.1).h ≤ entry.2.h := by
    intro part hpart entry hentry
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hentry
    simp only [List.length_zip] at hi
    have hil : i < part.1.length := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hir : i < part.2.rects.length :=
      Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have hpair : (part.1[i], part.2.rects[i]) = entry := by
      simpa only [List.getElem_zip] using heq
    have hkey : part.1[i]? = some entry.1 := by
      rw [List.getElem?_eq_getElem hil, ← hpair]
    have hget : part.2.rects[i]? = some entry.2 := by
      rw [List.getElem?_eq_getElem hir, ← hpair]
    have hn : 0 ≤ entry.2.w ∧ 0 ≤ entry.2.h := by
      have hb := exactPartsBounded execution
        (exactBorder2Unchanged_discharge execution) part hpart
      have hm := (List.of_mem_zip hentry).2
      exact ⟨(hb.2.2.1 entry.2 hm).2.2.2.2.1,
        (hb.2.2.1 entry.2 hm).2.2.2.2.2⟩
    dsimp only [minimum]
    cases hlookup : execution.graph.nodes[entry.1]? with
    | none => exact hn
    | some n =>
      by_cases hb : n.border = 0
      · simp only [hb, ↓reduceIte]
        exact xctb_component_rect_minimum_dims execution hpart hkey hlookup hb
          hget
      · simpa only [hb, ↓reduceIte] using hn
  have hfit := packAcc_rect_minimum_dimensions_of_coverage minimum
    execution.packed_eq
    (fun i r hr => Or.inr (hcoverage i r hr)) hparts key rect hrect
  simpa only [minimum, hnode, hborder, ↓reduceIte] using hfit

/-- The exact graph keeps an ordinary node: for a non-fixed `.node` box,
`exactGraph` maps the measured node to itself (the `exactIds`/fixed-group
branch would throw `.domain` on a missing fixed entry, contradicting the
successful run). -/
private theorem xctb_exactGraph_node_ordinary {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (hg : exactGraph P exactIds inp o measured g0 = .ok g)
    {i : Nat} {box : ModelBox} (hbox : inp.boxes[i]? = some box)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false)
    {n0 : Node} (hn0 : g0.nodes[i]? = some n0) (hdecl : n0.decl = i) :
    g.nodes[i]? = some n0 := by
  unfold exactGraph at hg
  obtain ⟨nodes, hnodes, h⟩ := bind_ok hg
  have he := Except.ok.inj h
  have hgnodes : g.nodes = nodes := by
    simpa using (congrArg Graph.nodes he).symm
  obtain ⟨_, hmapGet⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨nodeX, hfX, hmem⟩ := hmapGet i n0 hn0
  have hbx : inp.boxes[n0.decl]? = some box := by rw [hdecl]; exact hbox
  rw [hbx] at hfX
  dsimp only at hfX
  split at hfX
  · simp only [pure, Except.pure] at hfX
    have hred : nodeX = n0 := Except.ok.inj hfX.symm
    rw [← hgnodes, hred] at hmem
    exact hmem
  · have hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
      List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
    simp only [hfind, throw, throwThe, MonadExceptOf.throw] at hfX
    cases hfX
/-- Ordinary non-fixed node text fit over the exact execution (copy of
`SceneExecution.ordinary_node_packed_text_fit`,
`PlainNodeSizingFacts.lean:97`, with the exact coverage and minimum dims). -/
private theorem xctb_ordinary_node_packed_text_fit {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {i : Nat} {ls : List Measure.Line} {box : ModelBox} {node : Node}
    {rect : Rect}
    (hline : execution.lines[i]? = some ls)
    (hbox : inp.boxes[i]? = some box) (hrole : box.role = .node)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false)
    (hnode : execution.graph.nodes[i]? = some node)
    (hrect : execution.packedAcc.rects[i]? = some rect) :
    (ls.foldl (fun w line => max w line.width) 0) ≤
        (orientRect o.direction execution.packedAcc.canvasH rect).w ∧
      ((ls.length : Int) * execution.params.lineH) ≤
        (orientRect o.direction execution.packedAcc.canvasH rect).h := by
  obtain ⟨n0, hnode0, hdecl0, hb0⟩ := measuredGraph_node_border_zero
    execution.checked execution.graph0_eq hline hbox hrole hfixed
  have hpres := xctb_exactGraph_node_ordinary execution.graph_eq hbox hfixed
    hnode0 hdecl0
  have hnode_eq : node = n0 := Option.some.inj (hnode.symm.trans hpres)
  subst node
  obtain ⟨n1, hn1, _, hw, hh⟩ := measuredGraph_node_text_fit
    execution.checked execution.graph0_eq hline hbox hrole hfixed
  have hn1_eq : n1 = n0 := Option.some.inj (hn1.symm.trans hnode0)
  subst n1
  have hfit := xctb_packed_rect_minimum_dims_of_coverage execution
    execution.parts_coverage hpres hb0 hrect
  refine ⟨?_, ?_⟩
  all_goals
    cases hd : o.direction <;>
      simp only [hd, orientRect] at hw hh hfit ⊢ <;> omega

/-- Exact ordinary box line height holds outright: replay of
`SceneExecution.ordinary_box_line_height` (`SizingCoverageBridge.lean:139`)
over `SceneExecutionX`. -/
theorem xctb_ordinaryBoxLineHeightX_holds (exactIds : List String) :
    X_OrdinaryBoxLineHeightX exactIds := by
  intro inp o res execution index box hbox source hsource hrole hfixed ls hline
  obtain ⟨rect, hrect⟩ := xctb_packed_rect_exists execution
    (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨actual, hactual, hboxeq⟩ := xctb_box_index_origin execution hbox
  rw [hsource] at hactual
  cases Option.some.inj hactual
  obtain ⟨n0, hnode0, hdecl0, hb0⟩ := measuredGraph_node_border_zero
    execution.checked execution.graph0_eq hline hsource hrole hfixed
  have hpres := xctb_exactGraph_node_ordinary execution.graph_eq hsource hfixed
    hnode0 hdecl0
  have hfit := xctb_ordinary_node_packed_text_fit execution hline hsource hrole
    hfixed hpres hrect
  have hget : execution.packedAcc.rects.getD index default = rect := by
    obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrect
    simpa [Array.getD, hi] using heq
  rw [hboxeq, hget]
  dsimp only [shiftRect]
  exact ⟨by omega, by omega⟩

/-- Exact graph node dimensions respect every fixed-size entry (copy of the
private `X_exactGraph_fixed_node_dims`, `ExactFitClosure.lean:817`). -/
private theorem xctb_exactGraph_fixed_node_dims {exactIds : List String} {P : Params}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hg0 : measuredGraph P inp o lines = .ok graph0)
    (hg : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {i : Nat} {ls : List Measure.Line} (hline : lines[i]? = some ls)
    {box : ModelBox} (hbox : inp.boxes[i]? = some box)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = some entry) :
    ∃ node, graph.nodes[i]? = some node ∧ node.decl = i ∧ node.border = 0 ∧
      (match o.direction with
        | .LR | .RL => entry.2.h
        | .TB | .BT => entry.2.w) ≤ node.w ∧
      (match o.direction with
        | .LR | .RL => entry.2.w
        | .TB | .BT => entry.2.h) ≤ node.h := by
  obtain ⟨node0, hnode0, hdecl0, hborder0, hw0, hh0⟩ :=
    measuredGraph_fixed_node_dims hg0 hline hbox hfixed
  unfold exactGraph at hg
  obtain ⟨nodes, hnodes, h⟩ := bind_ok hg
  have he := Except.ok.inj h
  have hgnodes : graph.nodes = nodes := by
    simpa using (congrArg Graph.nodes he).symm
  obtain ⟨_, hmapGet⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨nodeX, hfX, hmem⟩ := hmapGet i node0 hnode0
  rw [← hgnodes] at hmem
  cases hbox0 : inp.boxes[node0.decl]? with
  | none =>
    simp only [hbox0, pure, Except.pure] at hfX
    have hred : nodeX = node0 := Except.ok.inj hfX.symm
    rw [hred] at hmem
    exact ⟨node0, hmem, hdecl0, hborder0, hw0, hh0⟩
  | some box' =>
    rw [hdecl0] at hbox0
    have hbeq : box' = box := Option.some.inj (hbox0.symm.trans hbox)
    rw [hbeq] at hbox0
    simp only [hdecl0, hbox0] at hfX
    split at hfX
    · simp only [pure, Except.pure] at hfX
      have hred : nodeX = node0 := Except.ok.inj hfX.symm
      rw [hred] at hmem
      exact ⟨node0, hmem, hdecl0, hborder0, hw0, hh0⟩
    · cases hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
      | none =>
        simp only [hfind] at hfX
        cases hfX
      | some fixed =>
        simp only [hfind] at hfX
        have hentry : fixed = entry := Option.some.inj (hfind.symm.trans hfixed)
        rw [hentry] at hfX
        split at hfX
        · simp only [bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at hfX
          cases hfX
        · split at hfX
          · simp only [bind, Except.bind, throw, throwThe,
              MonadExceptOf.throw] at hfX
            cases hfX
          · simp only [pure, Except.pure] at hfX
            obtain rfl := Except.ok.inj hfX
            refine ⟨_, hmem, ?_, ?_, ?_, ?_⟩
            · cases hd : o.direction <;> rfl
            · cases hd : o.direction <;> exact hborder0
            · cases hd : o.direction <;> exact Int.le_refl _
            · cases hd : o.direction <;> exact Int.le_refl _

/-- Fixed-size entries are dominated by the exact output box (copy of
`SceneExecution.fixed_box_dominates`, `FixedOwnerFit.lean:10`). -/
private theorem xctb_fixed_box_dominates {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {i : Nat} {box : Box} {source : ModelBox} {entry : String × Size}
    (hbox : res.scene.boxes[i]? = some box)
    (hsource : inp.boxes[i]? = some source)
    (hfixed : inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry) :
    entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h := by
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (mapM_getElem? _ _ _ h).1
      _ = inp.boxes.length := List.length_zipIdx
  have hi : i < execution.lines.length :=
    hlinesLen ▸ (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨ls, hline⟩ : ∃ ls, execution.lines[i]? = some ls :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨rect, hrect⟩ := xctb_packed_rect_exists execution
    (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨node, hnode, _, hborder, hnw, hnh⟩ :=
    xctb_exactGraph_fixed_node_dims execution.graph0_eq execution.graph_eq
      hline hsource hfixed
  have hfit := xctb_packed_rect_minimum_dims_of_coverage execution
    execution.parts_coverage hnode hborder hrect
  obtain ⟨actual, hactual, hboxeq⟩ := xctb_box_index_origin execution hbox
  rw [hsource] at hactual
  cases Option.some.inj hactual
  have hget : execution.packedAcc.rects.getD i default = rect := by
    obtain ⟨hii, heq⟩ := Array.getElem?_eq_some_iff.mp hrect
    simpa [Array.getD, hii] using heq
  rw [hboxeq, hget]
  dsimp only [shiftRect]
  cases hd : o.direction <;>
    simp only [hd, orientRect] at hnw hnh hfit ⊢ <;> omega

/-- Exact fixed-owner fit holds outright: replay of
`SceneExecution.fixed_owner_fit` (`FixedOwnerFit.lean:45`) over
`SceneExecutionX`. -/
theorem xctb_fixedOwnerFitX_holds (exactIds : List String) :
    X_FixedOwnerFitX exactIds := by
  intro inp o res execution hfit i box source hbox hsource hany hex hown
  obtain ⟨entry, hfixed⟩ :
      ∃ entry, inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry := by
    cases hf : inp.fixedSizes.find? (fun e => e.1 == source.id) with
    | none =>
      obtain ⟨e, hmem, hid⟩ := List.any_eq_true.mp hany
      exact absurd (List.find?_eq_none.mp hf e hmem) (by rw [hid]; decide)
    | some entry => exact ⟨entry, rfl⟩
  have hmem : entry ∈ inp.fixedSizes := List.mem_of_find?_eq_some hfixed
  have hid : entry.1 = source.id := by simpa using List.find?_some hfixed
  have hwrap : StyledMeasure.wrap execution.metric
      (Measure.wrapTarget execution.metric.profile execution.params.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD i source.id).toList =
        .ok (execution.lines.getD i []) := by
    have hlines := execution.lines_eq
    simp only [boxLines] at hlines
    obtain ⟨_, hlookup⟩ := mapM_getElem? _ _ _ hlines
    obtain ⟨measured, hmeasured, hindex⟩ := hlookup i (source, i)
      (by simp only [List.getElem?_zipIdx, hsource, Option.map_some,
        Nat.zero_add])
    dsimp only at hmeasured
    have hget : execution.lines.getD i [] = measured := by
      simp only [List.getD_eq_getElem?_getD, hindex, Option.getD_some]
    rw [hget]
    exact hmeasured
  have hfit' : FixedSizeFit execution.params source.role (execution.lines.getD i [])
      entry.2 :=
    hfit entry hmem i source hsource hid.symm hex hown
      execution.params execution.metric (execution.lines.getD i [])
      execution.checked execution.metric_eq hwrap
  have hdom := xctb_fixed_box_dominates execution hbox hsource hfixed
  exact FixedSizeFit.mono hfit' hdom.1 hdom.2

/-- Title caption fit as `titleCaptionSize` bounds over the exact execution:
conversion of the closed `X_ExactTitleCaptionFit` (`Size.mk` bounds) to the
form the cross-part proof consumes. -/
private theorem xctb_titleFit_of_closed {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {partT : List Nat × Part} (hpartTmem : partT ∈ execution.componentsAcc.parts)
    {title : Nat × Rect} (htitleMem : title ∈ partT.2.titles)
    {key : Nat} (hkeyEq : key = partT.1.getD title.1 0) :
    (titleCaptionSize execution.params o
      (execution.lines.getD key [])).w ≤ title.2.w ∧
      (titleCaptionSize execution.params o
        (execution.lines.getD key [])).h ≤ title.2.h := by
  obtain ⟨_, _, hfitW0, hfitH0⟩ :=
    X_exactTitleCaptionFit_closed exactIds execution hpartTmem htitleMem
  rw [← hkeyEq] at hfitW0 hfitH0
  constructor <;>
    (cases hd : o.direction <;>
      simp only [hd, titleCaptionSize] at hfitW0 hfitH0 ⊢ <;>
      assumption)
/-- Exact cross-part title disjointness holds outright: replay of
`titleExclusiveCrossPart` (`CaptionCrossPartProof.lean:39`) over
`SceneExecutionX`. -/
theorem xctb_titleExclusiveCrossPartX_holds (exactIds : List String) :
    X_TitleExclusiveCrossPartX exactIds := by
  intro inp o res execution key stored hstoredMem k fBox hbox hex packed hpack
    cT partT boxT title hzipT htitleMem hkeyEq hstoredEq
    cB partB posB hcB hposB hne
  obtain ⟨hpartT, hboxTmem⟩ := List.getElem?_zip_eq_some.mp hzipT
  have hcTlen : cT < execution.componentsAcc.parts.length :=
    (List.getElem?_eq_some_iff.mp hpartT).1
  have hboxesLen : packed.boxes.length =
      execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hcTbox : cT < packed.boxes.length := by omega
  have hcBlen : cB < execution.componentsAcc.parts.length :=
    (List.getElem?_eq_some_iff.mp hcB).1
  have hcBbox : cB < packed.boxes.length := by omega
  have hboxTeq : packed.boxes[cT] = boxT :=
    (List.getElem?_eq_some_iff.mp hboxTmem).2
  have hboxBget : packed.boxes[cB]? = some packed.boxes[cB] :=
    List.getElem?_eq_getElem hcBbox
  have hitemsLenT : cT < (execution.componentsAcc.parts.map fun q =>
      Pack.Item.mk q.2.width q.2.height q.2.area).length := by
    rw [List.length_map]; exact hcTlen
  have hitemsLenB : cB < (execution.componentsAcc.parts.map fun q =>
      Pack.Item.mk q.2.width q.2.height q.2.area).length := by
    rw [List.length_map]; exact hcBlen
  have hitemT : (execution.componentsAcc.parts.map fun q =>
      Pack.Item.mk q.2.width q.2.height q.2.area)[cT] =
      Pack.Item.mk partT.2.width partT.2.height partT.2.area := by
    rw [List.getElem_map, (List.getElem?_eq_some_iff.mp hpartT).2]
  have hitemB : (execution.componentsAcc.parts.map fun q =>
      Pack.Item.mk q.2.width q.2.height q.2.area)[cB] =
      Pack.Item.mk partB.2.width partB.2.height partB.2.area := by
    rw [List.getElem_map, (List.getElem?_eq_some_iff.mp hcB).2]
  have hdimT : boxT.w = partT.2.width ∧ boxT.h = partT.2.height := by
    have h := packShelfDims hpack hcTbox hitemsLenT
    rw [hboxTeq, hitemT] at h
    exact h
  have hdimBw : packed.boxes[cB].w = partB.2.width := by
    have h := packShelfDims hpack hcBbox hitemsLenB
    rw [hitemB] at h
    exact h.1
  have hdimBh : packed.boxes[cB].h = partB.2.height := by
    have h := packShelfDims hpack hcBbox hitemsLenB
    rw [hitemB] at h
    exact h.2
  obtain ⟨candB, runB, loopsB, areaB, _hrunB, _hloopsB, hpartdefB,
      hlookupB⟩ :=
    part_frame_lookupX execution packed hpack hcB hboxBget
  have hkLen : k < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hbox).1
  have hrectEq := hlookupB posB k hposB hkLen
  have hpartBmem : partB ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? hcB
  have hbndB := exactPartsBounded execution
    (exactBorder2Unchanged_discharge execution) partB hpartBmem
  have hiBlen : posB <
      (componentCandidate execution.graph partB.1 candB).nodes.length := by
    have hpos : posB < partB.1.length :=
      (List.getElem?_eq_some_iff.mp hposB).1
    rw [componentCandidate_nodes]
    simpa [componentGraph] using hpos
  have hfBget := xctb_placeComponentExact_rects_get (P := execution.params)
    (cg := componentCandidate execution.graph partB.1 candB) (run := runB)
    (labels := execution.measured) (loops := loopsB) (cursor := 0) hiBlen
  have hfBmem : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph partB.1 candB) runB execution.measured
        loopsB).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph partB.1 candB) runB
          execution.measured loopsB).minY)
      (frameRect execution.params
        (componentCandidate execution.graph partB.1 candB) runB posB)) ∈
      partB.2.rects := by
    rw [hpartdefB]
    exact List.mem_of_getElem? hfBget
  have hr0B := hbndB.2.2.1 _ hfBmem
  have hpartTmem : partT ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? hpartT
  have hbndT := exactPartsBounded execution
    (exactBorder2Unchanged_discharge execution) partT hpartTmem
  have htT := hbndT.2.2.2.1 title htitleMem
  have hfit := xctb_titleFit_of_closed execution hpartTmem htitleMem hkeyEq
  have hcontB : (packed.boxes[cB]).Contained
      (execution.packedAcc.rects.getD k default) := by
    rw [hrectEq]
    unfold Rect.Contained
    dsimp only [shiftRect] at hr0B ⊢
    omega
  have hcontT : boxT.Contained (shiftRect boxT.x boxT.y
      { title.2 with
        w := (titleCaptionSize execution.params o
          (execution.lines.getD key [])).w
        h := (titleCaptionSize execution.params o
          (execution.lines.getD key [])).h }) := by
    unfold Rect.Contained
    dsimp only [shiftRect]
    omega
  have hdisj : Disjoint packed.boxes[cB] boxT := by
    have h := Pack.pack_boxes_disjoint hpack cB cT hcBbox hcTbox (Ne.symm hne)
    rwa [hboxTeq] at h
  rw [hstoredEq]
  exact disjoint_of_contained_disjoint hcontB hcontT hdisj

/-- The installed-title branch from its single residual: the part-local band
stays open (`X_TitleSamePartBandX`, true on every installed-title probe
row); the cross-part half closes above and the packed transport closes in
`ExactPackedTransportResidualsProof`. -/
theorem xctb_captionTitleBranchClear_of_band (exactIds : List String)
    (hband : X_TitleSamePartBandX exactIds) :
    X_CaptionTitleBranchClear exactIds :=
  x_captionTitleBranchClear_holds exactIds hband
    (xctb_titleExclusiveCrossPartX_holds exactIds)
    (X_packedPartTransportBounded_closed exactIds)

/-- The fallback containment from its single residual: the owner-role
classification stays open (`X_FallbackOwnerCasesX`, true on every probe
row); the fixed-owner fit and the ordinary line height close above. -/
theorem xctb_ownerCaptionContainFallbackFitW_of_cases (exactIds : List String)
    (hcases : X_FallbackOwnerCasesX exactIds) :
    X_OwnerCaptionContainFallbackFitW exactIds :=
  x_ownerCaptionContainFallbackFitW_holds exactIds
    (xctb_fixedOwnerFitX_holds exactIds) hcases
    (xctb_ordinaryBoxLineHeightX_holds exactIds)

end PipelineImpl
end Layered
end Elegant

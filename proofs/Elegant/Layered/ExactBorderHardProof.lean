import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.LoopRectRealQProof
import Elegant.Layered.LoopRectCrossPartProof
import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.PartSeparation
import Elegant.Layered.Pack
import Elegant.Layered.CgShape
import Elegant.Layered.ExactFlatC6ShelfBorderProof
import Elegant.Layered.ExactLoopRectTopSamePartProof
import Elegant.Layered.ExactTopOutsideDisjointProof
import Elegant.Layered.ExactTopInRangeProof
import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.ExactPlainNodePathProof
import Elegant.Layered.ExactFlatC7CaptionScope

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact flat C6 border-hard seam, discharged modulo the chain alignment

Seam `X6_BorderHardW` (`ExactFlatC6ShelfBorderProof.lean`): a real run node
behind a positive foreign exclusive scene box cannot be a group top
(`border = -2`). The consumer `X6_borderZeroRealW_holds` feeds it to
`flatC6B_layoutXW` as `hbordW`.

Proof shape (replay of `XL_loopRectTopReal_holds` in `ExactLoopRectProof.lean`
with the run-level same-part residual in its per-execution W form):

* The scene box `b` has a model origin (`xbh_box_origin`). If its key lies
  outside the packed component, the foreign-vehicle argument
  (`xbh_Top_foreign_false`) contradicts shelf disjointness.
* If the key lies inside, `xbh_exclusive_witness` produces a plain run node
  `w` (`border = 0`) whose transported frame equals the group-top frame;
  `XL_TopSamePartW` rules that out.

`XL_TopSamePartW` is closed here from the existing chain-alignment seam
`X_ForeignBorderChainXAligned` (the `c8aChain` field of `ExactSeams`) through
the already-proved W chain: `XN_bracketMarkersAtRank_holds`,
`XN_plainNodePathResidual_holds`, `XN_plainClearOfSideMarker_of_path`,
`XN_sideMarkerSpanAligned_of_chain`, `xlrr_topOutsideDisjointInRangeW_holds`,
`XLrr_topOutsideDisjointW_holds`, `XL_topSamePartW_closed`.

The private `xl_*` helpers of `ExactLoopRectProof.lean` are replayed below as
`xbh_*` (same proofs, `SceneExecutionX` transport); the only change against
`XL_loopRectTopReal_holds` is that the same-part hypothesis is the W form
`XL_TopSamePartW` (which the executed context supplies directly) instead of
the general `XL_TopSamePart`.
-/

/-- X exact-source border-zero (replay of the private `xl_exclusive_source_border_zero`). -/
private theorem xbh_exclusive_source_border_zero {exactIds : List String}
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

/-- X placed-component rect entry (replay of `xl_loopRectCross_rects_get`). -/
private theorem xbh_loopRectCross_rects_get (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) {i : Nat}
    (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run 0 labels loops).rects[i]? =
      some (shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  simp only [placeComponentExact, placeBoundsX, List.getElem?_map, List.getElem?_range hi,
    Option.map_some]

/-- X exclusive witness (replay of `xl_exclusive_witness`). -/
private theorem xbh_exclusive_witness {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run}
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    {key : Nat} {source : ModelBox}
    (hsource : inp.boxes[key]? = some source)
    (hexcl : source.exclusive = true)
    (hmem : key ∈ q.1.1) :
    ∃ w : Nat,
      q.1.1[w]? = some key ∧ source.role = BoxRole.node ∧
      w < (componentCandidate execution.graph q.1.1 candidate).nodes.length ∧
      ((componentCandidate execution.graph q.1.1 candidate).nodes.getD w default).border = 0 ∧
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD key default))) =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run w)))) := by
  obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
  have hvlen : v < (componentCandidate execution.graph q.1.1 candidate).nodes.length := by
    have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length = q.1.1.length := by
      rw [componentCandidate_nodes]
      simp only [componentGraph, List.length_map]
    rw [hlen]
    exact (List.getElem?_eq_some_iff.mp hv).1
  have hkeylen : key < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeylen
  have hentry := X_chosen_part_frame_entry hpart hv
  have hval := actual_components_packed_rect_valueX (by rfl) execution.components_eq
    execution.packed_eq packed hpack hselected hentry hkeysize default
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    exact ((mapM_getElem? _ _ _ h).1).trans List.length_zipIdx
  obtain ⟨gnode, _hgnode, hb0⟩ :=
    xbh_exclusive_source_border_zero execution hwf hlinesLen hsource hexcl
  have hrole : source.role = BoxRole.node := by
    have hnotgroup : source.role ≠ BoxRole.group :=
      wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource) hexcl
    cases hr : source.role with
    | node => rfl
    | group => exact absurd hr hnotgroup
  have hcand : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? =
      some gnode := by
    have hmap : (componentCandidate execution.graph q.1.1 candidate).nodes =
        q.1.1.map fun k => execution.graph.nodes.getD k default := by
      rw [componentCandidate_nodes]
      simp only [componentGraph]
    have hget : execution.graph.nodes.getD key default = gnode := by
      have hmemk : execution.graph.nodes[key]? = some gnode := _hgnode
      rw [List.getD_eq_getElem?_getD, hmemk, Option.getD_some]
    rw [hmap]
    simp only [List.getElem?_map, hv, Option.map_some, hget]
  have hborder : ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v default).border = 0 := by
    have hget : (componentCandidate execution.graph q.1.1 candidate).nodes.getD v default = gnode := by
      rw [List.getD_eq_getElem?_getD, hcand, Option.getD_some]
    rw [hget]
    exact hb0
  refine ⟨v, hv, hrole, hvlen, hborder, ?_⟩
  exact congrArg (fun r => shiftRect execution.params.canvasMargin
    execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH r)) hval

/-- X scene-box origin (replay of `xl_box_origin`). -/
private theorem xbh_box_origin {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {b : Box} (hbmem : b ∈ res.scene.boxes) :
    ∃ key source, inp.boxes[key]? = some source ∧ source.exclusive = b.exclusive ∧
      b.rect =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD key default)) := by
  rw [execution.boxes_eq_mapX] at hbmem
  obtain ⟨pair, hpair, hboxeq⟩ := List.mem_map.mp hbmem
  have hsource : inp.boxes[pair.2]? = some pair.1 :=
    List.mem_zipIdx_iff_getElem?.mp hpair
  refine ⟨pair.2, pair.1, hsource, ?_, ?_⟩
  · exact congrArg Box.exclusive hboxeq
  · exact (congrArg Box.rect hboxeq).symm

/-- X foreign part lookup (replay of `xl_foreignPart`). -/
private theorem xbh_foreignPart {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    {keyB : Nat} (hkeyBlen : keyB < inp.boxes.length) :
    ∃ (partB : List Nat × Part) (cB posB : Nat),
      execution.componentsAcc.parts[cB]? = some partB ∧
      partB.1[posB]? = some keyB ∧ cB < packed.boxes.length := by
  obtain ⟨partB, hpartBmem, entry, hentrymem, hentrykey⟩ :=
    sceneExecutionX_parts_entry execution hkeyBlen
  obtain ⟨cB, hcBget⟩ := List.mem_iff_getElem?.mp hpartBmem
  have hposmem : entry.1 ∈ partB.1 := (List.of_mem_zip hentrymem).1
  obtain ⟨posB, hposB⟩ := List.getElem?_of_mem hposmem
  rw [hentrykey] at hposB
  have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hcBlen : cB < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hcBget).1
    omega
  exact ⟨partB, cB, posB, hcBget, hposB, hcBlen⟩

/-- X transported shelf rect (replay of `xl_shelfRectT`). -/
private def xbh_shelfRectT {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State) (c : Nat) : Rect :=
  shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH
      (packed.boxes[c]?.getD default))

/-- X transport of a part-local rect (replay of `xl_partRectT`). -/
private def xbh_partRectT {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State) (c : Nat) (r : Rect) : Rect :=
  shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH
      (shiftRect (packed.boxes[c]?.getD default).x
        (packed.boxes[c]?.getD default).y r))

/-- X shelf disjointness (replay of `xl_partsShelvesDisjoint_of_pack`). -/
private theorem xbh_partsShelvesDisjoint_of_pack {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionX exactIds inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed) :
    ∀ (c c' : Nat), c < packed.boxes.length → c' < packed.boxes.length → c ≠ c' →
      Disjoint (xbh_shelfRectT execution packed c) (xbh_shelfRectT execution packed c') := by
  intro c c' hc hc' hne
  have hcD : packed.boxes[c]?.getD default = packed.boxes[c] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hc, rfl⟩]
  have hcD' : packed.boxes[c']?.getD default = packed.boxes[c'] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hc', rfl⟩]
  simp only [xbh_shelfRectT]
  rw [hcD, hcD']
  exact orient_transport_disjoint (Pack.pack_boxes_disjoint hpack c c' hc hc' hne)

/-- X rect containment (replay of `xl_part_rects_within_shelf`). -/
private theorem xbh_part_rects_within_shelf {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed)
    {c : Nat} {part : List Nat × Part}
    (hmem : execution.componentsAcc.parts[c]? = some part)
    (hc : c < packed.boxes.length) :
    ∀ r ∈ part.2.rects,
      (xbh_shelfRectT execution packed c).Contained
        (xbh_partRectT execution packed c r) := by
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
  obtain ⟨hsw, hsh⟩ := packShelfDims hpack (by omega : c < packed.boxes.length) hmapLen
  intro r hr
  have hrb := (by obtain ⟨_, _, hrects, _, _, _⟩ := hbounded; exact hrects r hr)
  have hcD : packed.boxes[c]?.getD default = packed.boxes[c] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hc, rfl⟩]
  simp only [xbh_shelfRectT, xbh_partRectT, hcD]
  refine orient_transport_contained ?_
  simp only [shiftRect, Rect.Contained]
  obtain ⟨hr1, hr2, hr3, hr4, _, _⟩ := hrb
  have hwb : packed.boxes[c].w = part.2.width := by rw [hsw, hitem]
  have hhb : packed.boxes[c].h = part.2.height := by rw [hsh, hitem]
  rw [hwb, hhb]
  omega

/-- X top foreign vehicle (replay of `xl_Top_foreign_false`). -/
private theorem xbh_Top_foreign_false {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box)
    (_hreal : RouteImpl.IsReal run.proper v)
    (_hbmem : b ∈ res.scene.boxes) (_hexcl : b.exclusive = true)
    (hrect : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))))
    {node : Node}
    (hnode : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node)
    (_hbord : node.border = -2)
    {keyB : Nat} {sourceB : ModelBox}
    (hsourceB : inp.boxes[keyB]? = some sourceB)
    (hbrectB : b.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default)))
    (hforeign : keyB ∉ q.1.1)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  have hkeyBlen : keyB < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hsourceB).1
  obtain ⟨partB, cB, posB, hkB, hposB, _hcBlen⟩ :=
    xbh_foreignPart execution packed hpack hkeyBlen
  have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
    zip_getElem?_left hselected
  have hne : c ≠ cB := by
    intro heq
    subst heq
    have hqeq : q.1 = partB := Option.some.inj (hmemc.symm.trans hkB)
    have hmem : keyB ∈ q.1.1 := by
      rw [hqeq]
      exact List.mem_of_getElem? hposB
    exact hforeign hmem
  have hvlen : v <
      (componentCandidate execution.graph q.1.1 candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hclen : c < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hmemc).1
    omega
  have hR : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      loops).minX)
    (-(placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      loops).minY)
    (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v)) ∈ q.1.2.rects := by
    rw [hpart]
    exact List.mem_of_getElem?
      (xbh_loopRectCross_rects_get execution.params _ _ _ _ hvlen)
  have hcontR := xbh_part_rects_within_shelf execution packed hpack hmemc hclen _ hR
  have hshelfC : packed.boxes[c]? = some q.2 :=
    (List.getElem?_zip_eq_some.mp hselected).2
  have hL : xbh_partRectT execution packed c
      (shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v)) =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
    unfold xbh_partRectT
    rw [hshelfC, Option.getD_some]
  have hcBlen : cB < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hkB).1
    omega
  obtain ⟨boxB, hboxB⟩ : ∃ boxB, packed.boxes[cB]? = some boxB :=
    ⟨packed.boxes[cB], List.getElem?_eq_getElem hcBlen⟩
  obtain ⟨candB, runB, loopsB, _areaB, _hrunB, _hloopsB, hpartdefB, hlookupB⟩ :=
    part_frame_lookupX execution packed hpack hkB hboxB
  obtain ⟨fB, hfBdef⟩ : ∃ f : Rect, f = shiftRect
      (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minY)
      (frameRect execution.params
        (componentCandidate execution.graph partB.1 candB) runB posB) :=
    ⟨_, rfl⟩
  have hval : execution.packedAcc.rects.getD keyB default =
      shiftRect boxB.x boxB.y fB := by
    rw [hfBdef]
    exact hlookupB posB keyB hposB hkeyBlen
  have hiB : posB <
      (componentCandidate execution.graph partB.1 candB).nodes.length := by
    have hlen : (componentCandidate execution.graph partB.1 candB).nodes.length = partB.1.length := by
      rw [componentCandidate_nodes]
      simp only [componentGraph, List.length_map]
    rw [hlen]
    exact (List.getElem?_eq_some_iff.mp hposB).1
  have hfBmem : fB ∈ partB.2.rects := by
    rw [hfBdef, hpartdefB]
    exact List.mem_of_getElem?
      (xbh_loopRectCross_rects_get execution.params _ _ _ _ hiB)
  have hcontB := xbh_part_rects_within_shelf execution packed hpack hkB hcBlen _ hfBmem
  have hdisjAll := xbh_partsShelvesDisjoint_of_pack hpack
  have hRHS : (shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect boxB.x boxB.y fB))) = xbh_partRectT execution packed cB fB := by
    unfold xbh_partRectT
    rw [hboxB, Option.getD_some]
  have hmiss : ¬ (xbh_partRectT execution packed c
      (shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX)
        (-(placeBoundsX execution.params
          (componentCandidate execution.graph q.1.1 candidate) run execution.measured
          loops).minY)
        (frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v))).meetsInterior
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) := by
    rw [hval, hRHS]
    intro hmeet
    exact hdisjAll c cB hclen hcBlen hne
      (meetsInterior_of_contained_inner hcontB
        (meetsInterior_of_contained_outer hcontR hmeet))
  have hdisL : Disjoint
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run v)))))
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) := by
    rw [← hL]
    exact hmiss
  exact loopRect_crossPart_false hrect hbrectB hdisL hposW hposH

/-- Border-hard from the W-form same-part residual: replay of
`XL_loopRectTopReal_holds` with `XL_TopSamePartW` as the same-part hypothesis.
The seam's rect equation spells the `minY` shift as `0 - minY`; it is
converted once to the canonical `-(minY)` form the transport lemmas use. -/
theorem X6_borderHardW_of_topSameW (exactIds : List String)
    (hsame : XL_TopSamePartW exactIds) : X6_BorderHardW exactIds := by
  intro inp o res execution hwf hfp candidate run packed hpack c q hselected
    area loops hpart hcomp hrun v b hreal hbmem hexcl hw hh heq node hnode hbord
  have hminY : (0 : Int) - (placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      loops).minY =
      -((placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY) := by omega
  have hrect : b.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
    have h' := heq
    rw [hminY] at h'
    exact h'
  obtain ⟨keyB, sourceB, hsourceB, hboxexcl, hbrectB⟩ :=
    xbh_box_origin execution hbmem
  have hexclB : sourceB.exclusive = true := by rw [hboxexcl]; exact hexcl
  by_cases hmem : keyB ∈ q.1.1
  · obtain ⟨w, _hw, _hroleW, hwlen, hbord0, hpackeq⟩ :=
      xbh_exclusive_witness execution hwf packed hpack hselected hpart hsourceB hexclB hmem
    have hnodeW : (componentCandidate execution.graph q.1.1 candidate).nodes[w]? =
        some ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen) :=
      List.getElem?_eq_getElem hwlen
    have hbW : ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen).border
        = 0 := by
      have hget : (componentCandidate execution.graph q.1.1 candidate).nodes.getD w default =
          (componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwlen, Option.getD_some]
      rw [← hget]
      exact hbord0
    have hframe : frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w =
        frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v := by
      have hww : shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y
              (shiftRect (0 - (placeBoundsX execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minX)
                (-(placeBoundsX execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minY)
                (frameRect execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run w)))) =
          shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect q.2.x q.2.y
                (shiftRect (0 - (placeBoundsX execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minX)
                  (-(placeBoundsX execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minY)
                  (frameRect execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
        rw [← hpackeq, ← hbrectB]
        exact hrect
      exact loopTransport_cancel hww
    exact False.elim (hsame execution hwf hfp (comp := q.1.1) hcomp
      (candidate := candidate) (run := run) (orderOptions := candidateOrder candidate) hrun
      hnode hbord hnodeW hbW hframe)
  · exact False.elim (xbh_Top_foreign_false execution hwf candidate run packed hpack c q
      hselected hpart hcomp hrun v b hreal hbmem hexcl hrect (node := node) hnode hbord
      hsourceB hbrectB hmem hw hh)

/-- The W-form same-part residual closes from the chain alignment: the three
side-marker residuals close by the proved `XN_*_holds`/`XN_*_of_path` theorems
(`XN_sideMarkerSpanAligned_of_chain` consumes the chain alignment), the
in-range outsider case closes by `xlrr_topOutsideDisjointInRangeW_holds`, the
band cases by `XLrr_topOutsideDisjointW_holds`, and the skeleton by
`XL_topSamePartW_closed`. -/
theorem X6_topSamePartW_of_chain (exactIds : List String)
    (hchain : X_ForeignBorderChainXAligned exactIds) : XL_TopSamePartW exactIds :=
  XL_topSamePartW_closed exactIds
    (XLrr_topOutsideDisjointW_holds exactIds
      (xlrr_topOutsideDisjointInRangeW_holds exactIds
        (XN_bracketMarkersAtRank_holds exactIds)
        (XN_plainClearOfSideMarker_of_path exactIds (XN_plainNodePathResidual_holds exactIds))
        (XN_sideMarkerSpanAligned_of_chain exactIds hchain)))

/-- Seam `X6_BorderHardW` discharged: a real run node behind a positive foreign
exclusive scene box cannot be a group top, modulo the existing chain-alignment
seam `X_ForeignBorderChainXAligned` (the `c8aChain` field of `ExactSeams`). -/
theorem X6_borderHardW_holds (exactIds : List String)
    (hchain : X_ForeignBorderChainXAligned exactIds) : X6_BorderHardW exactIds :=
  X6_borderHardW_of_topSameW exactIds (X6_topSamePartW_of_chain exactIds hchain)

end PipelineImpl
end Layered
end Elegant

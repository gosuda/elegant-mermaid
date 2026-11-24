import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionRunTruthProbes
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.RankSiblingDisjoint
 import Elegant.Layered.ExactFlatFacts
 import Elegant.Layered.ExactPartBounded

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region flat C2 (`layoutRIds`).

Packet P5 of `local://region-tower-plan.md` (field 3, `flatC2`):
`flatC2B_layoutRIds`, the region analogue of `flatC2B_layoutX`
(`Layered/ExactFlatC2.lean:1604-1607`) via the `X_layoutX_c2_core` assembly,
replayed through `componentRunR_specR` (`RegionRunSpec.lean`).

The packed-shelf half of the assembly (distinct packed boxes are disjoint,
scene boxes sit in their part's shelf box) replays verbatim over the shared
`packAcc`/`sceneOf` equations via `SceneExecutionR`. The same-part half (two
border-0 nodes of one executed run have disjoint frame rects) is the single
open residual `componentRunR_positions_disjointR_fact`
(`RegionRunTruthProbes.lean:109`): the `crossCoordsR` pinned-layer geometry
that the exact `X_componentRun_positions_disjoint` proof consumes does not
exist for region runs, so the run-level separation is assumed and the
`componentRunR_specR` rank disjunction bridges the candidate-graph lookups
of the assembly to the rewritten-graph lookups of the residual
(`rankEquivalentR_nodes_eq` for the `some` case, `cg' = cg` for `none`).

Truth note (probe `proofs/wip/Probe/RegionFlatC2TProbe.lean`): `Validator.c2`
evaluates to `true` on every executed region input there (two-region,
paired-member, nested, back-edge, self-loop, cross-region, long-title,
two-cycle, and the fixed-parent input whose `exactIds` names region parent
`G1` with children still in the base input), and `rrtpDisjointOk` on the
executed first-component runs is `true` on all of them, so the residual is
true on every probe as stated.
-/

 /-- `mapM` preserves length on success (copy of the flat helper). -/
 private theorem rfc2_mapM_ok_len {err α β : Type} (f : α → Except err β) :
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

 /-- A packed shelf box keeps the declaring part's item dimensions at the same index
 (copy of the flat helper). -/
 private theorem rfc2_packBoxDims {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
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

 /-- A scene box at index `bi` is the oriented, margin-shifted packed rect of the source
 model box (region copy of `sceneBox_source_rectX`, via `boxes_eq_mapR`). -/
 private theorem rfc2_sceneBoxSourceRectR {exactIds : List String}
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

 /-- A part index below the executed parts is below the packed shelf boxes
 (copy of the flat helper). -/
 private theorem rfc2_partPackedBoxLenR {exactIds : List String}
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
 private theorem rfc2_candidateRLen (spec : Option RegionSpec) (g : Graph)
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

 /-- For one executed region part: the fixed component run, loops, and placed part
 (run data without pack equations). -/
 private theorem rfc2_partPackedRunR {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     {k : Nat} {part : List Nat × Part}
     (hk : execution.componentsAcc.parts[k]? = some part) :
     ∃ (cand : Nat) (spec' : Option RegionSpec) (cg' : Graph) (run : Run)
       (loops : List (Nat × LoopPlacement)) (area : Int),
       componentRunR execution.params (exactDecls exactIds inp) spec' inp
         (componentCandidateR spec' execution.graph part.1 cand) execution.measured
         (candidateOrder cand) = .ok (cg', run) ∧
       componentLoops execution.params cg' run execution.measured = .ok loops ∧
       part.2 = { placeComponentExact execution.params cg' run 0 execution.measured loops with
         area := area } := by
   have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
       Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
       false, [], []⟩ : Acc).parts = [] := rfl
   obtain ⟨_, hall⟩ := actual_components_parts_geometryR hempty execution.components_eq
   have hmem : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hk
   obtain ⟨index, chosen, cg, run, loops, area, spec', _, _, _, _, hrun, hloops,
     hpartdef⟩ := hall part hmem
   exact ⟨index, spec', cg, run, loops, area, hrun, hloops, hpartdef⟩

 /-- For one executed region part at pack index `k`: every member frame rect of the part
 is contained in the part's packed shelf box, and the packed accumulator stores exactly
 the placed frame (region copy of `X_part_packed_frame`; frames are over the rewritten
 graph `cg` that `componentRunR` returns). -/
 private theorem rfc2_partPackedFrameR {exactIds : List String}
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
     ∃ (cand : Nat) (spec' : Option RegionSpec) (cg' : Graph) (run : Run)
       (loops : List (Nat × LoopPlacement)),
       componentRunR execution.params (exactDecls exactIds inp) spec' inp
         (componentCandidateR spec' execution.graph part.1 cand) execution.measured
         (candidateOrder cand) = .ok (cg', run) ∧
       (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
         packed.boxes[k].Contained (shiftRect packed.boxes[k].x packed.boxes[k].y
           (shiftRect (0 - (placeBoundsX execution.params cg' run execution.measured
               loops).minX)
             (-(placeBoundsX execution.params cg' run execution.measured loops).minY)
             (frameRect execution.params cg' run i)))) ∧
       (∀ (i key : Nat), part.1[i]? = some key → key < inp.boxes.length →
         execution.packedAcc.rects.getD key default =
           shiftRect packed.boxes[k].x packed.boxes[k].y
             (shiftRect (0 - (placeBoundsX execution.params cg' run execution.measured
                 loops).minX)
               (-(placeBoundsX execution.params cg' run execution.measured loops).minY)
               (frameRect execution.params cg' run i))) := by
   obtain ⟨cand, spec', cg, run, loops, area, hrun, hloops, hpartdef⟩ :=
     rfc2_partPackedRunR execution hk
   have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
       Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
       false, [], []⟩ : Acc).parts = [] := rfl
   have hbox : packed.boxes[k]? = some packed.boxes[k] :=
     List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
   have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? =
       some (part, packed.boxes[k]) :=
     List.getElem?_zip_eq_some.mpr ⟨hk, hbox⟩
   have hplacedAt : ∀ (i key : Nat), part.1[i]? = some key →
       (placeComponentExact execution.params cg run 0 execution.measured
         loops).rects[i]? =
       some (shiftRect (0 - (placeBoundsX execution.params cg run execution.measured
           loops).minX)
         (-(placeBoundsX execution.params cg run execution.measured loops).minY)
         (frameRect execution.params cg run i)) := by
     intro i key hkey
     have hilt : i < part.1.length := (List.getElem?_eq_some_iff.mp hkey).1
     have hcl : (componentCandidateR spec' execution.graph part.1 cand).nodes.length =
         part.1.length := rfc2_candidateRLen _ _ _ _
     have hrl : cg.nodes.length =
         (componentCandidateR spec' execution.graph part.1 cand).nodes.length :=
       componentRunR_nodes_eq hrun
     have hi : i < cg.nodes.length := by omega
     unfold placeComponentExact placeBoundsX
     simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
   refine ⟨cand, spec', cg, run, loops, hrun, ?_, ?_⟩
   · intro i key hkey hkeyLen
     have hpartget := (List.getElem?_eq_some_iff.mp hk).2
     have hmapLen : k < (execution.componentsAcc.parts.map
         (fun part => Pack.Item.mk part.2.width part.2.height part.2.area)).length := by
       rw [List.length_map]
       exact (List.getElem?_eq_some_iff.mp hk).1
     obtain ⟨hw0, hh0⟩ := rfc2_packBoxDims hpack hkLen hmapLen
     have hitem : (execution.componentsAcc.parts.map
         (fun part => Pack.Item.mk part.2.width part.2.height part.2.area))[k] =
         Pack.Item.mk part.2.width part.2.height part.2.area := by
       rw [List.getElem_map, hpartget]
     have hwb : packed.boxes[k].w = part.2.width := by
       rw [hw0, hitem]
     have hhb : packed.boxes[k].h = part.2.height := by
       rw [hh0, hitem]
     have hwlink : part.2.width =
         (placeComponentExact execution.params cg run 0 execution.measured loops).width := by
       have hcongr := congrArg Part.width hpartdef
       simpa using hcongr
     have hhlink : part.2.height =
         (placeComponentExact execution.params cg run 0 execution.measured loops).height := by
       have hcongr := congrArg Part.height hpartdef
       simpa using hcongr
     have hplaced := hplacedAt i key hkey
     have hmem := List.mem_of_getElem? hplaced
     have hb := placeComponentExact_rects_bounds execution.params cg run 0
       execution.measured loops _ hmem
     simp only [Rect.Contained, shiftRect] at hb ⊢
     rw [hwb, hhb, hwlink, hhlink]
     omega
   · intro i key hkey hkeyLen
     have hsize : key < execution.componentsAcc.rects.size := by
       rw [execution.components_rects_sizeR]; exact hkeyLen
     have hplaced := hplacedAt i key hkey
     have hrectpart : part.2.rects[i]? =
         some (shiftRect (0 - (placeBoundsX execution.params cg run execution.measured
           loops).minX)
         (-(placeBoundsX execution.params cg run execution.measured loops).minY)
         (frameRect execution.params cg run i)) := by
       rw [hpartdef]; exact hplaced
     have hentry : ((part, packed.boxes[k]).1.1.zip
         (part, packed.boxes[k]).1.2.rects)[i]? =
         some (key, shiftRect (0 - (placeBoundsX execution.params cg run
           execution.measured loops).minX)
         (-(placeBoundsX execution.params cg run execution.measured loops).minY)
         (frameRect execution.params cg run i)) :=
       List.getElem?_zip_eq_some.mpr ⟨hkey, hrectpart⟩
     exact actual_components_packed_rect_valueR hempty execution.components_eq
       execution.packed_eq packed hpack hselected hentry hsize default

 /-- An exclusive source box of a successful region execution is a border-0 node of the
 exact graph at the same index (region copy of `X_exclusive_source_border_zero`). -/
 private theorem rfc2_exclusiveSourceBorderZeroR {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
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

 /-- Clause 2 for one executed region scene: two distinct exclusive scene boxes sharing a
 parent are disjoint. Same-component siblings are separated by the executed region run
 (via the open residual over the rewritten graph); boxes in different components live in
 disjoint packed shelf boxes. Region copy of `X_layoutX_c2_core`. -/
 private theorem rfc2_layoutRIds_c2_core {exactIds : List String}
     {idSets : List (String × List String)} {inp : Input} {o : Options}
     {res : FamilyResult}
     (execution : SceneExecutionR exactIds idSets inp o res)
     (hwf : WellFormed (inputModel inp o))
     (hdisj : componentRunR_positions_disjointR_fact) :
     Validator.C2 res.scene.layoutDump := by
   have hpackedEq := execution.packed_eq
   unfold packAcc at hpackedEq
   obtain ⟨packed, hpack, -⟩ := bind_ok hpackedEq
   have hlinesLen : execution.lines.length = inp.boxes.length := by
     have hl := execution.lines_eq
     simp only [boxLines] at hl
     calc execution.lines.length = (inp.boxes.zipIdx).length :=
         rfc2_mapM_ok_len _ _ _ hl
       _ = inp.boxes.length := List.length_zipIdx
   intro b hb c hc hne hbex hcex _hpar
   simp only [Scene.layoutDump, List.mem_iff_getElem?] at hb hc
   obtain ⟨bi, hbi⟩ := hb
   obtain ⟨ci, hci⟩ := hc
   obtain ⟨sb, hsb, hbid, -, hbexS, hbrect⟩ := rfc2_sceneBoxSourceRectR execution hbi
   obtain ⟨sc, hsc, hcid, -, hcexS, hcrect⟩ := rfc2_sceneBoxSourceRectR execution hci
   have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
   have hciLen : ci < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsc).1
   have hbiNe : bi ≠ ci := by
     intro heq
     subst heq
     have hss : sb = sc := Option.some.inj (hsb.symm.trans hsc)
     exact hne (by rw [hbid, hcid, hss])
   obtain ⟨partB, posB, kB, -, hkB, hposB⟩ :=
     key_part_positionR execution hbiLen
   obtain ⟨partA, posA, kA, -, hkA, hposA⟩ :=
     key_part_positionR execution hciLen
   have hkBlen := rfc2_partPackedBoxLenR execution packed hpack hkB
   have hkAlen := rfc2_partPackedBoxLenR execution packed hpack hkA
   by_cases hksame : kB = kA
   · subst hksame
     have hpartsSame : partA = partB := Option.some.inj (hkA.symm.trans hkB)
     rw [hpartsSame] at hposA
     have hposNe : posB ≠ posA := by
       intro heq
       rw [heq] at hposB
       exact hbiNe (Option.some.inj (hposB.symm.trans hposA))
     obtain ⟨candB, specB, cgB, runB, loopsB, hrunB, -, hlookupB⟩ :=
       rfc2_partPackedFrameR execution packed hpack hkB hkBlen
     obtain ⟨nodeB, hnodeBg, hborderB⟩ :=
       rfc2_exclusiveSourceBorderZeroR execution hwf hlinesLen hsb
         (hbexS.symm.trans hbex)
     obtain ⟨nodeA, hnodeAg, hborderA⟩ :=
       rfc2_exclusiveSourceBorderZeroR execution hwf hlinesLen hsc
         (hcexS.symm.trans hcex)
     have hnodeBlookup : (componentCandidateR specB execution.graph partB.1 candB).nodes[posB]? =
         some nodeB := component_node_lookupR hposB hnodeBg
     have hnodeAlookup : (componentCandidateR specB execution.graph partB.1 candB).nodes[posA]? =
         some nodeA := component_node_lookupR hposA hnodeAg
     obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hRank, _, _, _, _, _, _, _, _,
         _, _, _, _, _, _, _, _, _, _, _⟩ := componentRunR_specR hrunB
     have hnodes : cgB.nodes =
         (componentCandidateR specB execution.graph partB.1 candB).nodes := by
       rcases hRank with ⟨_, _, _, _, heq, _⟩ | ⟨_, _, hranked⟩
       · rw [heq]
       · exact rankEquivalentR_nodes_eq hranked
     have hUB : cgB.nodes[posB]? = some nodeB := by rw [hnodes]; exact hnodeBlookup
     have hUA : cgB.nodes[posA]? = some nodeA := by rw [hnodes]; exact hnodeAlookup
     have hdisjFrames := hdisj hrunB hUB hUA hborderB hborderA hposNe
     rw [hbrect, hcrect, hlookupB posB bi hposB hbiLen, hlookupB posA ci hposA hciLen]
     intro hmeet
     exact hdisjFrames (meetsInterior_of_shiftRect
       (meetsInterior_of_shiftRect (meetsInterior_of_orientRect
         (meetsInterior_of_shiftRect hmeet))))
   · obtain ⟨_, _, _, _, _, _, hcontainB, hlookupB⟩ :=
       rfc2_partPackedFrameR execution packed hpack hkB hkBlen
     obtain ⟨_, _, _, _, _, _, hcontainA, hlookupA⟩ :=
       rfc2_partPackedFrameR execution packed hpack hkA hkAlen
     have hboxesDisj : ¬ (packed.boxes[kB]).meetsInterior (packed.boxes[kA]) :=
       Pack.pack_boxes_disjoint hpack kB kA hkBlen hkAlen hksame
     have hdisjShift := not_meetsInterior_shiftRect
       (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
       (not_meetsInterior_orientRect (d := o.direction)
         (h := execution.packedAcc.canvasH) hboxesDisj)
     have hx := contained_shiftRect_imp
       (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
       (contained_orientRect (d := o.direction)
         (h := execution.packedAcc.canvasH) (hcontainB posB bi hposB hbiLen))
     have hy := contained_shiftRect_imp
       (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin)
       (contained_orientRect (d := o.direction)
         (h := execution.packedAcc.canvasH) (hcontainA posA ci hposA hciLen))
     rw [hbrect, hcrect, hlookupB posB bi hposB hbiLen, hlookupA posA ci hposA hciLen]
     exact not_meetsInterior_of_contained hdisjShift hx hy

 /-- Clause 2 of the layout validator for a successful region flat
 `PipelineImpl.layoutRIds`, conditional on the single open run-separation fact:
 every two distinct exclusive scene boxes sharing a parent are disjoint. -/
 theorem flatC2B_layoutRIds (exactIds : List String)
     (idSets : List (String × List String))
     (hdisj : componentRunR_positions_disjointR_fact) :
     FlatC2B (layoutRIds exactIds idSets) := by
   intro inp o res hwf hok
   obtain ⟨execution⟩ := layoutRIds_sceneExecution hok
   exact rfc2_layoutRIds_c2_core execution hwf hdisj

end PipelineImpl
end Layered
end Elegant

import Elegant.Layered.CaptionResidualsProof
import Elegant.Layered.LabelsC8b
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.PartSeparation
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Cross-part title clearance

`TitleExclusiveCrossPart` (`Layered/CaptionResidualsProof.lean`): the packed
title caption of `key` (located via the title fold in part `cT`) is disjoint
from the packed rect of the exclusive box `k` (located in part `cB`) when the
part indices differ. Both rectangles are transported contents of two distinct
packed shelf rectangles, so the packing separation settles it. -/

/-- The placed rect of component position `i` is the run's frame rectangle
shifted by the placement origin (local copy of the private `FlatC2` helper). -/
private theorem crossPart_part_rects_get (P : Params) (cg : Graph)
    (run : Run) (labels : List MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponent P cg run 0 labels loops).rects[i]? =
      some (shiftRect (0 - (placeBounds P cg run labels loops).minX)
        (0 - (placeBounds P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponent placeBounds
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Cross-part half of `TitleExclusiveFrameDisjoint`: the packed title caption
of `key` and the packed rect of the exclusive box `k` live in distinct packed
shelves. The caption (resized by `titleCaptionSize`, as `sceneOf` substitutes
it) stays inside its shelf by part boundedness plus the executed caption fit;
the exclusive rect stays inside its shelf by part boundedness plus the
run-frame lookup; distinct shelves are disjoint by `Pack.pack_boxes_disjoint`.
No `WellFormed` hypothesis is needed. -/
theorem titleExclusiveCrossPart {inp : Input} {o : Options} {res : FamilyResult} :
    TitleExclusiveCrossPart inp o res := by
  intro _hwf execution key stored _hmem k _fBox hbox _hex packed hpack
    cT partT boxT title hzipT htitleMem hkeyEq hstoredEq
    cB partB posB hcB hposB hne
  obtain ⟨hpartT, hboxTmem⟩ := List.getElem?_zip_eq_some.mp hzipT
  have hcTlen : cT < execution.componentsAcc.parts.length :=
    (List.getElem?_eq_some_iff.mp hpartT).1
  have hboxesLen : packed.boxes.length = execution.componentsAcc.parts.length := by
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
  obtain ⟨candB, runB, loopsB, areaB, _hrunB, _hloopsB, hpartdefB, hlookupB⟩ :=
    part_frame_lookup execution packed hpack hcB hboxBget
  have hkLen : k < inp.boxes.length := (List.getElem?_eq_some_iff.mp hbox).1
  have hrectEq := hlookupB posB k hposB hkLen
  have hpartBmem : partB ∈ execution.componentsAcc.parts := List.mem_of_getElem? hcB
  have hbndB := execution.components_parts_bounded partB hpartBmem
  unfold PartBounded at hbndB
  obtain ⟨_, _, hrectsB, _, _, _⟩ := hbndB
  have hiBlen : posB < (componentCandidate execution.graph partB.1 candB).nodes.length := by
    have hpos : posB < partB.1.length := (List.getElem?_eq_some_iff.mp hposB).1
    rw [componentCandidate_nodes]
    simpa [componentGraph] using hpos
  have hfBget := crossPart_part_rects_get execution.params
    (componentCandidate execution.graph partB.1 candB) runB execution.measured loopsB hiBlen
  have hfBmem : (shiftRect (0 - (placeBounds execution.params
      (componentCandidate execution.graph partB.1 candB) runB execution.measured loopsB).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph partB.1 candB) runB execution.measured loopsB).minY)
      (frameRect execution.params
        (componentCandidate execution.graph partB.1 candB) runB posB)) ∈ partB.2.rects := by
    rw [hpartdefB]
    have hrw : ({placeComponent execution.params
        (componentCandidate execution.graph partB.1 candB) runB 0 execution.measured loopsB
        with area := areaB} : Part).rects =
        (placeComponent execution.params
          (componentCandidate execution.graph partB.1 candB) runB 0 execution.measured loopsB).rects :=
      rfl
    rw [hrw]
    exact List.mem_of_getElem? hfBget
  have hr0B := hrectsB _ hfBmem
  have hpartTmem : partT ∈ execution.componentsAcc.parts := List.mem_of_getElem? hpartT
  have hbndT := execution.components_parts_bounded partT hpartTmem
  unfold PartBounded at hbndT
  obtain ⟨_, _, _, htitlesT, _, _⟩ := hbndT
  have htT := htitlesT title htitleMem
  have hfitW : (titleCaptionSize execution.params o
      (execution.lines.getD key [])).w ≤ title.2.w := by
    have h := (execution.component_title_caption_fit hpartTmem htitleMem).2.2.1
    rwa [← hkeyEq] at h
  have hfitH : (titleCaptionSize execution.params o
      (execution.lines.getD key [])).h ≤ title.2.h := by
    have h := (execution.component_title_caption_fit hpartTmem htitleMem).2.2.2
    rwa [← hkeyEq] at h
  have hcontB : (packed.boxes[cB]).Contained (execution.packedAcc.rects.getD k default) := by
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

end Elegant.Layered.PipelineImpl

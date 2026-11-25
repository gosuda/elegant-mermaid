import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.PartSeparation
import Elegant.Layered.RankSiblingDisjoint

set_option autoImplicit false

/-! # Caption owner-scope clearance: the non-descendant half

`OwnerScopeExclusiveClear` (`Layered/CaptionScopeGeometry.lean`) is residual (b) of
the caption seam: an exclusive dump box that is neither the non-exclusive owner
nor in its validator scope misses the owner scene box rect.  The two box keys of
such a pair live either in distinct packed parts or in one part:

* `ownerScopeExclusiveClear_cross_part` (unconditional): the executed packing
  separates the two part shelves (the containment half of `partsSeparated_holds`
  plus `partsShelvesDisjoint_of_pack`), so the transported rects cannot meet
  (`rect_misses_box_of_distinct_parts`).
* `OwnerScopeSamePartClear` names the remaining same-part obligation: the two
  frame rectangles of one executed run are disjoint.  That premise is exactly
  what `ForeignSpansClear` (mutually unrelated group declarations) or
  `componentRun_positions_disjoint` (border-0 nodes) provide; this file fixes the
  transport plumbing from that frame separation to the scene boxes.

`ownerScopeExclusiveClear_of_same_part` combines both halves into the residual. -/

namespace Elegant.Layered

/-- A part index below the executed parts is below the packed shelf boxes. -/
private theorem ownerScope_part_packed_len {inp : Input} {o : Options}
    {res : FamilyResult} (execution : PipelineImpl.SceneExecution inp o res)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {part : List Nat × PipelineImpl.Part}
    (hk : execution.componentsAcc.parts[k]? = some part) : k < packed.boxes.length := by
  rw [Pack.pack_count hpack, List.length_map]
  exact (List.getElem?_eq_some_iff.mp hk).1

/-- Every model-box key of a successful execution lies in one executed part at a
concrete component position and part index (public restatement of the `FlatC2`
part-position helper). -/
theorem ownerScope_part_position {inp : Input} {o : Options} {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res) {key : Nat}
    (hkey : key < inp.boxes.length) :
    ∃ (part : List Nat × PipelineImpl.Part) (pos k : Nat),
      execution.componentsAcc.parts[k]? = some part ∧
      part.1[pos]? = some key := by
  have hsize : execution.componentsAcc.rects.size = inp.boxes.length :=
    execution.components_rects_size
  have hrect : execution.componentsAcc.rects[key]? = some execution.componentsAcc.rects[key] :=
    Array.getElem?_eq_some_iff.mpr ⟨by rw [hsize]; exact hkey, rfl⟩
  obtain ⟨part, hpart, entry, hentry, hentryKey⟩ := execution.parts_coverage _ _ hrect
  have hkeyIn : key ∈ part.1 := by
    rw [← hentryKey]
    exact (List.of_mem_zip hentry).1
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hkeyIn
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hpart
  exact ⟨part, pos, k, hk, hpos⟩

/-- The placed rect of component position `i` is the run's frame rectangle
shifted by the placement origin (local copy of the private `FlatC2` helper). -/
private theorem ownerScope_part_rects_get (P : PipelineImpl.Params) (cg : Graph)
    (run : PipelineImpl.Run) (labels : List PipelineImpl.MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) {i : Nat} (hi : i < cg.nodes.length) :
    (PipelineImpl.placeComponent P cg run 0 labels loops).rects[i]? =
      some (PipelineImpl.shiftRect (0 - (PipelineImpl.placeBounds P cg run labels loops).minX)
        (0 - (PipelineImpl.placeBounds P cg run labels loops).minY)
        (PipelineImpl.frameRect P cg run i)) := by
  unfold PipelineImpl.placeComponent PipelineImpl.placeBounds
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- A `findIdx?` hit exposes the box at that index and its predicate value
(without the `getD default` restatement, which is not false for a degenerate
default box). -/
private theorem ownerScope_findIdx_lookup {α : Type} {p : α → Bool} {l : List α}
    {n : Nat} (h : l.findIdx? p = some n) :
    n < l.length ∧ ∃ a, l[n]? = some a ∧ p a = true := by
  induction l generalizing n with
  | nil =>
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons a as ih =>
    rw [List.findIdx?_cons] at h
    by_cases hp : p a = true
    · rw [ite_eq_left hp] at h
      have hn : n = 0 := (Option.some.inj h).symm
      subst hn
      exact ⟨Nat.zero_lt_succ _, a, rfl, hp⟩
    · rw [ite_eq_right hp] at h
      obtain ⟨m, hmfind, hmn⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hmlen, x, hxget, hpx⟩ := ih hmfind
      rw [← hmn]
      exact ⟨Nat.succ_lt_succ hmlen, x, (List.getElem?_cons_succ).trans hxget, hpx⟩

/-- Cross-part half of the caption owner-scope clearance, unconditionally: when
the owner key and the foreign exclusive box key are packed into distinct shelf
boxes, the packing separation (`partsSeparated_holds`) plus the transported
shelf disjointness put the two scene rects apart. -/
theorem ownerScopeExclusiveClear_cross_part
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res)
    {ownerIndex bi : Nat} (hOwnerLen : ownerIndex < inp.boxes.length)
    (hBLen : bi < inp.boxes.length)
    {ownerBox b : Box}
    (hownerRect : ownerBox.rect =
      PipelineImpl.shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD ownerIndex default)))
    (hbRect : b.rect =
      PipelineImpl.shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD bi default)))
    {kO kB posO posB : Nat} {partO partB : List Nat × PipelineImpl.Part}
    (hkO : execution.componentsAcc.parts[kO]? = some partO)
    (hkB : execution.componentsAcc.parts[kB]? = some partB)
    (hposO : partO.1[posO]? = some ownerIndex)
    (hposB : partB.1[posB]? = some bi)
    (hne : kO ≠ kB) :
    ¬ b.rect.meetsInterior ownerBox.rect := by
  have hpack := execution.packed_eq
  unfold PipelineImpl.packAcc at hpack
  obtain ⟨packed, hpacked, _hfold⟩ := PipelineImpl.bind_ok hpack
  have hKO : kO < packed.boxes.length := ownerScope_part_packed_len execution packed hpacked hkO
  have hKB : kB < packed.boxes.length := ownerScope_part_packed_len execution packed hpacked hkB
  have hcO : packed.boxes[kO]?.getD default = packed.boxes[kO] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hKO, rfl⟩]
  have hcB : packed.boxes[kB]?.getD default = packed.boxes[kB] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hKB, rfl⟩]
  obtain ⟨candO, runO, loopsO, _areaO, _hrunO, _hloopsO, hpartdefO, hlookupO⟩ :=
    PipelineImpl.part_frame_lookup execution packed hpacked hkO
      (List.getElem?_eq_some_iff.mpr ⟨hKO, rfl⟩)
  obtain ⟨candB, runB, loopsB, _areaB, _hrunB, _hloopsB, hpartdefB, hlookupB⟩ :=
    PipelineImpl.part_frame_lookup execution packed hpacked hkB
      (List.getElem?_eq_some_iff.mpr ⟨hKB, rfl⟩)
  have hiOcand : posO <
      (PipelineImpl.componentCandidate execution.graph partO.1 candO).nodes.length := by
    rw [PipelineImpl.componentCandidate_nodes]
    simp only [PipelineImpl.componentGraph, List.length_map]
    simpa using (List.getElem?_eq_some_iff.mp hposO).1
  have hiBcand : posB <
      (PipelineImpl.componentCandidate execution.graph partB.1 candB).nodes.length := by
    rw [PipelineImpl.componentCandidate_nodes]
    simp only [PipelineImpl.componentGraph, List.length_map]
    simpa using (List.getElem?_eq_some_iff.mp hposB).1
  obtain ⟨fO, hfOdef⟩ : ∃ f : Rect, f = PipelineImpl.shiftRect
      (0 - (PipelineImpl.placeBounds execution.params
        (PipelineImpl.componentCandidate execution.graph partO.1 candO) runO
        execution.measured loopsO).minX)
      (0 - (PipelineImpl.placeBounds execution.params
        (PipelineImpl.componentCandidate execution.graph partO.1 candO) runO
        execution.measured loopsO).minY)
      (PipelineImpl.frameRect execution.params
        (PipelineImpl.componentCandidate execution.graph partO.1 candO) runO posO) :=
    ⟨_, rfl⟩
  obtain ⟨fB, hfBdef⟩ : ∃ f : Rect, f = PipelineImpl.shiftRect
      (0 - (PipelineImpl.placeBounds execution.params
        (PipelineImpl.componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minX)
      (0 - (PipelineImpl.placeBounds execution.params
        (PipelineImpl.componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minY)
      (PipelineImpl.frameRect execution.params
        (PipelineImpl.componentCandidate execution.graph partB.1 candB) runB posB) :=
    ⟨_, rfl⟩
  have hfOval : execution.packedAcc.rects.getD ownerIndex default =
      PipelineImpl.shiftRect packed.boxes[kO].x packed.boxes[kO].y fO := by
    rw [hfOdef]
    exact hlookupO posO ownerIndex hposO hOwnerLen
  have hfBval : execution.packedAcc.rects.getD bi default =
      PipelineImpl.shiftRect packed.boxes[kB].x packed.boxes[kB].y fB := by
    rw [hfBdef]
    exact hlookupB posB bi hposB hBLen
  have hfOmem : fO ∈ partO.2.rects := by
    rw [hfOdef, hpartdefO]
    exact List.mem_of_getElem? (ownerScope_part_rects_get execution.params
      (PipelineImpl.componentCandidate execution.graph partO.1 candO) runO
      execution.measured loopsO hiOcand)
  have hfBmem : fB ∈ partB.2.rects := by
    rw [hfBdef, hpartdefB]
    exact List.mem_of_getElem? (ownerScope_part_rects_get execution.params
      (PipelineImpl.componentCandidate execution.graph partB.1 candB) runB
      execution.measured loopsB hiBcand)
  have hwithinO := PipelineImpl.part_rects_within_shelf hpacked hkO hKO fO hfOmem
  have hwithinB := PipelineImpl.part_rects_within_shelf hpacked hkB hKB fB hfBmem
  simp only [PipelineImpl.partRectT, hcO] at hwithinO
  simp only [PipelineImpl.partRectT, hcB] at hwithinB
  have hdisj := PipelineImpl.partsShelvesDisjoint_of_pack hpacked
  refine PipelineImpl.rect_misses_box_of_distinct_parts hdisj (c := kB) (c' := kO)
    hKB hKO (Ne.symm hne) ?_ ?_
  · rw [hbRect, hfBval]
    exact hwithinB
  · rw [hownerRect, hfOval]
    exact hwithinO

/-- `shiftRect` preserves rect disjointness. -/
private theorem ownerScope_shiftRect_disjoint {a b : Rect} {dx dy : Int}
    (h : Disjoint a b) : Disjoint (PipelineImpl.shiftRect dx dy a)
      (PipelineImpl.shiftRect dx dy b) := by
  simp only [Disjoint, Rect.meetsInterior, PipelineImpl.shiftRect] at h ⊢
  omega

/-- Same-part half of the caption owner-scope clearance, stated at run level:
within one executed packed part, the two positions' `frameRect`s in any
successful `componentRun` of that part's component are disjoint.  This is the
remaining frame-separation obligation (`ForeignSpansClear` for mutually
unrelated group declarations, `componentRun_positions_disjoint` for border-0
nodes); the scene-level caption/ancestor hypotheses are kept so the discharger
can derive the node-level non-containment conditions from them. -/
def OwnerScopeSamePartClear (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (index ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (captionLabel inp o res execution ownerIndex source lines) →
    source.owner ∉ res.scene.layoutDump.ancestors b.id →
    (PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) = none →
    ∀ (bi k posOwner posB : Nat) (part : List Nat × PipelineImpl.Part),
      res.scene.boxes[bi]? = some b →
      execution.componentsAcc.parts[k]? = some part →
      part.1[posOwner]? = some ownerIndex →
      part.1[posB]? = some bi →
      posOwner ≠ posB →
      ∀ (candidate : Nat) (run : PipelineImpl.Run),
        PipelineImpl.componentRun execution.params
          (PipelineImpl.componentCandidate execution.graph part.1 candidate)
          execution.measured (candidateOrder candidate) = .ok run →
        Disjoint
          (PipelineImpl.frameRect execution.params
            (PipelineImpl.componentCandidate execution.graph part.1 candidate) run
            posOwner)
          (PipelineImpl.frameRect execution.params
            (PipelineImpl.componentCandidate execution.graph part.1 candidate) run
            posB)

/-- Residual (b) of the caption seam: `OwnerScopeExclusiveClear` holds once the
same-part frame separation is available.  The cross-part half is discharged
here from the executed packing. -/
theorem ownerScopeExclusiveClear_of_same_part {inp : Input} {o : Options}
    {res : FamilyResult} (hsame : OwnerScopeSamePartClear inp o res) :
    OwnerScopeExclusiveClear inp o res := by
  intro execution index ownerIndex source lines b hsrc hmeas hfindIdx hmem hex hscope hd hnone
  have hmem0 : b ∈ res.scene.layoutDump.boxes := hmem
  have hexprEq : (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc)
      = res.scene.boxes := (execution.boxes_eq_map).symm
  have hboxLen : res.scene.boxes.length = inp.boxes.length := by
    rw [execution.boxes_eq_map, List.length_map, List.length_zipIdx]
  simp only [Scene.layoutDump, List.mem_iff_getElem?] at hmem
  obtain ⟨bi, hbi⟩ := hmem
  obtain ⟨sb, hsb, _hbid, _hsbpar, hsbex, hbrect⟩ :=
    PipelineImpl.sceneBox_source_rect execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
  obtain ⟨hOI, obox, hobox, hpobox⟩ := ownerScope_findIdx_lookup hfindIdx
  have hoboxEx : obox.exclusive = false := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hpobox
    simpa using hpobox.2
  have hownerLen : ownerIndex < res.scene.boxes.length := by omega
  obtain ⟨ownerBox, hownerGet⟩ : ∃ ob : Box, res.scene.boxes[ownerIndex]? = some ob :=
    ⟨_, List.getElem?_eq_getElem hownerLen⟩
  obtain ⟨_osource, _hos, _hoid, _hopar, _hoex, hownerRect⟩ :=
    PipelineImpl.sceneBox_source_rect execution hownerGet
  obtain ⟨partO, posO, kO, hkO, hposO⟩ := ownerScope_part_position execution hOI
  obtain ⟨partB, posB, kB, hkB, hposB⟩ := ownerScope_part_position execution hbiLen
  by_cases hksame : kO = kB
  · have hkB' : execution.componentsAcc.parts[kB]? = some partO := hksame ▸ hkO
    have hpartEq : partB = partO := Option.some.inj (hkB.symm.trans hkB')
    rw [hpartEq] at hposB
    have hbine : bi ≠ ownerIndex := by
      intro heq
      have hsbEq : sb = obox := by
        rw [heq] at hsb
        exact Option.some.inj (hsb.symm.trans hobox)
      rw [hsbEq] at hsbex
      rw [hsbex] at hex
      rw [hoboxEx] at hex
      simp at hex
    have hposNe : posO ≠ posB := by
      intro heq
      rw [heq] at hposO
      exact hbine (Option.some.inj (hposB.symm.trans hposO))
    obtain ⟨packed, hpacked, _hfold⟩ := PipelineImpl.bind_ok execution.packed_eq
    have hKB : kB < packed.boxes.length := ownerScope_part_packed_len execution packed
      hpacked hkB'
    obtain ⟨candB, runB, _loopsB, _areaB, hrunB, _hloopsB, _hpartdefB, hlookupB⟩ :=
      PipelineImpl.part_frame_lookup execution packed hpacked hkB'
        (List.getElem?_eq_some_iff.mpr ⟨hKB, rfl⟩)
    have hdisjFrame := hsame execution index ownerIndex source lines b hsrc hmeas hfindIdx
      hmem0 hex hscope hd hnone bi kB posO posB partO hbi hkB' hposO hposB hposNe candB runB hrunB
    have hdisjFrame' : Disjoint
        (PipelineImpl.frameRect execution.params
          (PipelineImpl.componentCandidate execution.graph partO.1 candB) runB posB)
        (PipelineImpl.frameRect execution.params
          (PipelineImpl.componentCandidate execution.graph partO.1 candB) runB posO) :=
      (Disjoint.comm _ _).mp hdisjFrame
    have hrectB := hlookupB posB bi hposB hbiLen
    have hrectO := hlookupB posO ownerIndex hposO hOI
    have hdisjPacked : Disjoint (execution.packedAcc.rects.getD bi default)
        (execution.packedAcc.rects.getD ownerIndex default) := by
      rw [hrectB, hrectO]
      exact ownerScope_shiftRect_disjoint
        (ownerScope_shiftRect_disjoint hdisjFrame')
    have hg : ((PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩) = ownerBox := by
      rw [hexprEq, List.getD_eq_getElem?_getD, hownerGet]
      rfl
    rw [hg, hownerRect, hbrect]
    exact PipelineImpl.disjoint_sceneTransport hdisjPacked
  · have hg : ((PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩) = ownerBox := by
      rw [hexprEq, List.getD_eq_getElem?_getD, hownerGet]
      rfl
    rw [hg]
    exact ownerScopeExclusiveClear_cross_part execution hOI hbiLen hownerRect hbrect
      hkO hkB hposO hposB hksame

end Elegant.Layered

import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.ExactFlatFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact caption scope clearance

Target: `X_captionScopeClearance_holds : X_CaptionScopeClearance exactIds`,
the exact residual that `flatC7B_layoutX`
(`Elegant/Layered/ExactFlatC7.lean:1512`) carries as hypothesis `hcap`.

Plain original: `captionScopeClearance`
(`Elegant/Layered/CaptionScopeGeometry.lean:337`), which splits the caption
case on descendant status and the installed-title test, discharging through
four branch facts. The closed plain proof consumes, per category:

* caption width floors: `SceneCaptionSizing` / `ownerCaptionContainFallback_of_fit`
  (`CaptionScopeGeometry.lean:110`, `CaptionFallbackContainProof.lean:55`),
  from `WellFormed` and `PipelineImpl.InputFixedFit`. No exact version
  exists: exact fixed-size fits are unchecked (zero and negative sizes are
  admitted), so `X_OwnerCaptionContainFallback` stays a residual. Precedent:
  `X_FallbackCaptionClearB8` (`ExactFlatC8b.lean:102`) likewise carries
  `InputFixedFit` as a premise.
* caption owner scope: `ownerScopeExclusiveClear_of_same_part`
  (`CaptionOwnerScopeFacts.lean:247`) from `OwnerScopeSamePartClear` plus the
  cross-part packing proof. No exact version exists; the exact same-part core
  is defined here as `X_OwnerScopeSamePartClear` (residual) and both the
  cross-part step and the same-part transport are replayed over
  `SceneExecutionX`.
* caption run clearance: `captionDescendantClear_of_same_part`
  (`CaptionDescendantFacts.lean:87`) from `CaptionDescendantSamePartClear`,
  and deeper the `ForeignBorderChainXAligned` seam. No exact version of the
  same-part core exists; it is defined here as
  `X_CaptionDescendantSamePartClear` (residual) and the transport is
  replayed. `X_ForeignBorderChainXAligned`
  (`ExactFlatC7CaptionScope.lean:58`) already mirrors the seam and stays open
  below this file.
* ancestor frame strictness: the old `CaptionAncestorFrameStrict` statement
  is false for an ancestor's bottom marker; the closed plain proof avoids it
  via the one-link `component_child_frame_strictInside` fact and never needs
  it here either. The replays below use only part positions and packed-rect
  lookups, so no ancestor-frame residual is introduced. They also never unfold
  a whole pipeline: every step rewrites with spec equations.
Frame-level and id-level transports proved here
(`XCapScope_ownerScopeExclusiveClear_cross_part`,
`XCapScope_captionDescendantClear_of_same_part`,
`XCapScope_ownerScopeExclusiveClear_of_same_part`) reduce the target to four
named single-fact residuals, one per plain caption fact with no exact
version. Each residual carries a probe in
`proofs/wip/Probe/ExactCaptionScopeTProbe.lean`.

Truth status (probed 2026-11-19): the top-level `X_CaptionScopeClearance`
conclusion holds on every probed `layoutX` instance (nine caption rows, all
`meets=false`, including zero-size, oversized, and negative fixed sizes).
The `X_OwnerCaptionContainFallback` residual itself is FALSE as stated: on a
fixed-size group owner the installed title vanishes and the
`ownedTextRect` fallback need not lie inside the owner rect. Witnesses
(`tFlatFixedOwnerInp`, `tFlatFixedOwnerZeroInp` in the probe):
owner `g` non-exclusive, label `l1` owned by `g`, no installed title, yet
`ownerBox.rect.Contained (ownedTextRect ..)` is false
(box `(1898, 1024, 300, 200)` vs caption `(2922, 2048, 0, 1280)`, and
box `(2048, 1024, 0, 0)` vs caption `(3072, 2048, 0, 1280)`).
It stays a hypothesis: discharging the exact caption scope on fixed-size
owners needs a fit-conditioned exact replay (exact fit facts do not exist
yet), not a verbatim replay of `ownerCaptionContainFallback_of_fit`.
-/

/-- X mirror of `CaptionDescendantSamePartClear`
(`CaptionDescendantFacts.lean:60`): the same-part descendant core over the
exact execution. Field for field the plain def, with `SceneExecution`
replaced by `SceneExecutionX` and `captionLabel` by `X_captionLabel`. -/
def X_CaptionDescendantSamePartClear (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (index ownerIndex bi : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (X_captionLabel exactIds execution ownerIndex source lines) →
    source.owner ∈ res.scene.layoutDump.ancestors b.id →
    ∀ (kO kB posO posB : Nat) (partO partB : List Nat × Part),
      res.scene.boxes[bi]? = some b →
      execution.componentsAcc.parts[kO]? = some partO →
      execution.componentsAcc.parts[kB]? = some partB →
      partO.1[posO]? = some ownerIndex →
      partB.1[posB]? = some bi →
      ¬ (sceneCaptionRect execution.params inp o execution.lines
          execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- X mirror of `OwnerScopeSamePartClear`
(`CaptionOwnerScopeFacts.lean:212`): the same-part frame-separation core over
the exact execution. Field for field the plain def, with `SceneExecution`
replaced by `SceneExecutionX` and `componentRun` over the model graph replaced
by `componentRunX` over `exactDecls`. -/
def X_OwnerScopeSamePartClear (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (index ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (X_captionLabel exactIds execution ownerIndex source lines) →
    source.owner ∉ res.scene.layoutDump.ancestors b.id →
    (sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) = none →
    ∀ (bi k posOwner posB : Nat) (part : List Nat × Part),
      res.scene.boxes[bi]? = some b →
      execution.componentsAcc.parts[k]? = some part →
      part.1[posOwner]? = some ownerIndex →
      part.1[posB]? = some bi →
      posOwner ≠ posB →
      ∀ (candidate : Nat) (run : Run),
        componentRunX execution.params (exactDecls exactIds inp)
          (componentCandidate execution.graph part.1 candidate) execution.measured
          (candidateOrder candidate) = .ok run →
        Disjoint
          (frameRect execution.params
            (componentCandidate execution.graph part.1 candidate) run
            posOwner)
          (frameRect execution.params
            (componentCandidate execution.graph part.1 candidate) run
            posB)

/-- `XCapScope_` copy of the private `captionScope_findIdx_lookup`
(`CaptionScopeGeometry.lean`): a `findIdx?` hit exposes the box at that
index and its predicate value. -/
private theorem XCapScope_findIdx_lookup {α : Type} {p : α → Bool} {l : List α}
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

/-- `XCapScope_` copy of the private `placeComponentExact_rects_get`
(`ExactFlatFacts.lean`): the placed rect of component position `i` is the
run's frame rectangle shifted by the exact placement origin. -/
private theorem XCapScope_placeComponentExact_rects_get {P : Params} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {cursor : Int} {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Exact replay of `captionDescendantClear_of_same_part`
(`CaptionDescendantFacts.lean:87`): the descendant branch follows from the
exact same-part core by the exact part-position lookups. Every proper
descendant of the owner is packed into the owner's executed part, so the two
`key_part_positionX` lookups instantiate the premise directly. -/
theorem XCapScope_captionDescendantClear_of_same_part (exactIds : List String)
    (hsame : X_CaptionDescendantSamePartClear exactIds) :
    X_CaptionDescendantClear exactIds := by
  intro inp o res execution index ownerIndex source lines b hsrc hmeas hfindIdx
    hmem hex hscope hd
  have hmem0 : b ∈ res.scene.layoutDump.boxes := hmem
  simp only [Scene.layoutDump, List.mem_iff_getElem?] at hmem
  obtain ⟨bi, hbi⟩ := hmem
  obtain ⟨sb, hsb, _hbid, _hsbpar, _hsbex, _hbrect⟩ :=
    sceneBox_source_rectX execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
  obtain ⟨hOILen, _obox, _hobox, _hpobox⟩ := XCapScope_findIdx_lookup hfindIdx
  obtain ⟨partO, posO, kO, _hmemO, hkO, hposO⟩ := key_part_positionX execution hOILen
  obtain ⟨partB, posB, kB, _hmemB, hkB, hposB⟩ := key_part_positionX execution hbiLen
  exact hsame inp o res execution index ownerIndex bi source lines b hsrc hmeas
    hfindIdx hmem0 hex hscope hd kO kB posO posB partO partB hbi hkO hkB hposO hposB

/-- `XCapScope_` copy of the private `ownerScope_shiftRect_disjoint`
(`CaptionOwnerScopeFacts.lean`): `shiftRect` preserves rect disjointness. -/
private theorem XCapScope_ownerScope_shiftRect_disjoint {a b : Rect} {dx dy : Int}
    (h : Disjoint a b) : Disjoint (shiftRect dx dy a)
      (shiftRect dx dy b) := by
  simp only [Disjoint, Rect.meetsInterior, shiftRect] at h ⊢
  omega

/-- Exact replay of `ownerScopeExclusiveClear_cross_part`
(`CaptionOwnerScopeFacts.lean:102`): when the owner key and the foreign
exclusive box key are packed into distinct shelf boxes, the exact packing
separation (`X_partsSeparated_holds`) plus the transported shelf disjointness
(`Pack.pack_boxes_disjoint` through `orient_transport_disjoint`) put the two
scene rects apart. -/
theorem XCapScope_ownerScopeExclusiveClear_cross_part (exactIds : List String)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {ownerIndex bi : Nat} (hOwnerLen : ownerIndex < inp.boxes.length)
    (hBLen : bi < inp.boxes.length)
    {ownerBox b : Box}
    (hownerRect : ownerBox.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD ownerIndex default)))
    (hbRect : b.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD bi default)))
    {kO kB posO posB : Nat} {partO partB : List Nat × Part}
    (hkO : execution.componentsAcc.parts[kO]? = some partO)
    (hkB : execution.componentsAcc.parts[kB]? = some partB)
    (hposO : partO.1[posO]? = some ownerIndex)
    (hposB : partB.1[posB]? = some bi)
    (hne : kO ≠ kB) :
    ¬ b.rect.meetsInterior ownerBox.rect := by
  have hpack := execution.packed_eq
  obtain ⟨packed, hpacked, _hfold⟩ := bind_ok hpack
  have hKO : kO < packed.boxes.length :=
    part_packed_box_lenX execution packed hpacked hkO
  have hKB : kB < packed.boxes.length :=
    part_packed_box_lenX execution packed hpacked hkB
  obtain ⟨candO, runO, loopsO, _areaO, _hrunO, _hloopsO, hpartdefO, hlookupO⟩ :=
    part_frame_lookupX execution packed hpacked hkO
      (List.getElem?_eq_some_iff.mpr ⟨hKO, rfl⟩)
  obtain ⟨candB, runB, loopsB, _areaB, _hrunB, _hloopsB, hpartdefB, hlookupB⟩ :=
    part_frame_lookupX execution packed hpacked hkB
      (List.getElem?_eq_some_iff.mpr ⟨hKB, rfl⟩)
  have hiOcand : posO <
      (componentCandidate execution.graph partO.1 candO).nodes.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
    simpa using (List.getElem?_eq_some_iff.mp hposO).1
  have hiBcand : posB <
      (componentCandidate execution.graph partB.1 candB).nodes.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
    simpa using (List.getElem?_eq_some_iff.mp hposB).1
  have hfOval := hlookupO posO ownerIndex hposO hOwnerLen
  have hfBval := hlookupB posB bi hposB hBLen
  have hfOmem : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph partO.1 candO) runO
      execution.measured loopsO).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph partO.1 candO) runO
        execution.measured loopsO).minY)
      (frameRect execution.params
        (componentCandidate execution.graph partO.1 candO) runO posO)) ∈
      partO.2.rects := by
    rw [hpartdefO]
    exact List.mem_of_getElem? (XCapScope_placeComponentExact_rects_get hiOcand)
  have hfBmem : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph partB.1 candB) runB
      execution.measured loopsB).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minY)
      (frameRect execution.params
        (componentCandidate execution.graph partB.1 candB) runB posB)) ∈
      partB.2.rects := by
    rw [hpartdefB]
    exact List.mem_of_getElem? (XCapScope_placeComponentExact_rects_get hiBcand)
  have hsep := X_partsSeparated_holds (exactIds := exactIds) (inp := inp) (o := o)
    (res := res)
  have hwithinO := (hsep execution packed kO partO packed.boxes[kO] hpacked hkO
    (List.getElem?_eq_some_iff.mpr ⟨hKO, rfl⟩)).2 _ hfOmem
  have hwithinB := (hsep execution packed kB partB packed.boxes[kB] hpacked hkB
    (List.getElem?_eq_some_iff.mpr ⟨hKB, rfl⟩)).2 _ hfBmem
  have hshelfO : shiftRect (packed.boxes[kO]).x (packed.boxes[kO]).y
      ⟨0, 0, (packed.boxes[kO]).w, (packed.boxes[kO]).h⟩ =
      packed.boxes[kO] := by
    obtain ⟨x, y, w, h⟩ := packed.boxes[kO]
    simp [shiftRect]
  have hshelfB : shiftRect (packed.boxes[kB]).x (packed.boxes[kB]).y
      ⟨0, 0, (packed.boxes[kB]).w, (packed.boxes[kB]).h⟩ =
      packed.boxes[kB] := by
    obtain ⟨x, y, w, h⟩ := packed.boxes[kB]
    simp [shiftRect]
  have hdisjShelves : Disjoint
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect (packed.boxes[kB]).x (packed.boxes[kB]).y
            ⟨0, 0, (packed.boxes[kB]).w, (packed.boxes[kB]).h⟩)))
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect (packed.boxes[kO]).x (packed.boxes[kO]).y
            ⟨0, 0, (packed.boxes[kO]).w, (packed.boxes[kO]).h⟩))) := by
    rw [hshelfB, hshelfO]
    exact orient_transport_disjoint
      (Pack.pack_boxes_disjoint hpacked kB kO hKB hKO (Ne.symm hne))
  rw [hbRect, hfBval, hownerRect, hfOval]
  intro hmeet
  exact hdisjShelves
    (meetsInterior_of_contained_inner hwithinO
      (meetsInterior_of_contained_outer hwithinB hmeet))

/-- Exact replay of `ownerScopeExclusiveClear_of_same_part`
(`CaptionOwnerScopeFacts.lean:247`): the non-descendant branch follows from
the exact same-part core; the cross-part half is discharged here from the
executed exact packing. -/
theorem XCapScope_ownerScopeExclusiveClear_of_same_part (exactIds : List String)
    (hsame : X_OwnerScopeSamePartClear exactIds) :
    X_OwnerScopeExclusiveClear exactIds := by
  intro inp o res execution index ownerIndex source lines b hsrc hmeas hfindIdx
    hmem hex hscope hd hnone
  have hmem0 : b ∈ res.scene.layoutDump.boxes := hmem
  have hexprEq : (sceneBoxesExpr execution.params inp o execution.packedAcc) =
      res.scene.boxes := by
    rw [execution.boxes_eq_mapX]
    rfl
  have hboxLen : res.scene.boxes.length = inp.boxes.length := by
    rw [execution.boxes_eq_mapX, List.length_map, List.length_zipIdx]
  simp only [Scene.layoutDump, List.mem_iff_getElem?] at hmem
  obtain ⟨bi, hbi⟩ := hmem
  obtain ⟨sb, hsb, _hbid, _hsbpar, hsbex, hbrect⟩ :=
    sceneBox_source_rectX execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsb).1
  obtain ⟨hOI, obox, hobox, hpobox⟩ := XCapScope_findIdx_lookup hfindIdx
  have hoboxEx : obox.exclusive = false := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hpobox
    simpa using hpobox.2
  have hownerLen : ownerIndex < res.scene.boxes.length := by omega
  obtain ⟨ownerBox, hownerGet⟩ : ∃ ob : Box, res.scene.boxes[ownerIndex]? = some ob :=
    ⟨_, List.getElem?_eq_getElem hownerLen⟩
  obtain ⟨_osource, _hos, _hoid, _hopar, _hoex, hownerRect⟩ :=
    sceneBox_source_rectX execution hownerGet
  obtain ⟨partO, posO, kO, _hmemO, hkO, hposO⟩ := key_part_positionX execution hOI
  obtain ⟨partB, posB, kB, _hmemB, hkB, hposB⟩ := key_part_positionX execution hbiLen
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
    obtain ⟨packed, hpacked, _hfold⟩ := bind_ok execution.packed_eq
    have hKB : kB < packed.boxes.length :=
      part_packed_box_lenX execution packed hpacked hkB'
    obtain ⟨candB, runB, _loopsB, _areaB, hrunB, _hloopsB, _hpartdefB, hlookupB⟩ :=
      part_frame_lookupX execution packed hpacked hkB'
        (List.getElem?_eq_some_iff.mpr ⟨hKB, rfl⟩)
    have hdisjFrame := hsame inp o res execution index ownerIndex source lines b hsrc hmeas
      hfindIdx hmem0 hex hscope hd hnone bi kB posO posB partO hbi hkB' hposO hposB
      hposNe candB runB hrunB
    have hdisjFrame' : Disjoint
        (frameRect execution.params
          (componentCandidate execution.graph partO.1 candB) runB posB)
        (frameRect execution.params
          (componentCandidate execution.graph partO.1 candB) runB posO) :=
      (Disjoint.comm _ _).mp hdisjFrame
    have hrectB := hlookupB posB bi hposB hbiLen
    have hrectO := hlookupB posO ownerIndex hposO hOI
    have hdisjPacked : Disjoint (execution.packedAcc.rects.getD bi default)
        (execution.packedAcc.rects.getD ownerIndex default) := by
      rw [hrectB, hrectO]
      exact XCapScope_ownerScope_shiftRect_disjoint
        (XCapScope_ownerScope_shiftRect_disjoint hdisjFrame')
    have hg : ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩) = ownerBox := by
      rw [hexprEq, List.getD_eq_getElem?_getD, hownerGet]
      rfl
    rw [hg, hownerRect, hbrect]
    exact disjoint_sceneTransport hdisjPacked
  · have hg : ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩) = ownerBox := by
      rw [hexprEq, List.getD_eq_getElem?_getD, hownerGet]
      rfl
    rw [hg]
    exact XCapScope_ownerScopeExclusiveClear_cross_part exactIds execution hOI
      hbiLen hownerRect hbrect hkO hkB hposO hposB hksame

/-- The exact caption scope clearance from four single-fact residuals: the
descendant and owner-scope branches from their exact same-part cores proved
above, the fallback-containment and installed-title branches as stated. -/
theorem X_captionScopeClearance_holds (exactIds : List String)
    (hdesc : X_CaptionDescendantSamePartClear exactIds)
    (hcontain : X_OwnerCaptionContainFallback exactIds)
    (howners : X_OwnerScopeSamePartClear exactIds)
    (htitle : X_CaptionTitleBranchClear exactIds) :
    X_CaptionScopeClearance exactIds := by
  exact x_captionScopeClearance_holds exactIds
    (XCapScope_captionDescendantClear_of_same_part exactIds hdesc)
    hcontain
    (XCapScope_ownerScopeExclusiveClear_of_same_part exactIds howners)
    htitle

end PipelineImpl
end Layered
end Elegant

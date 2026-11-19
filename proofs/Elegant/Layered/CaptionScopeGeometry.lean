import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.ComposeNotesC8a

set_option autoImplicit false

/-! # Caption scope geometry

`CaptionScopeClearance` (`Layered/LabelsC7Captions.lean`) is the single missing
geometric fact behind the caption seam of flat clause 7.  This file states the
final theorem `captionScopeClearance` over the executed seams that its
discharge needs, plus the pure rect glue.

`labelOwnerAnc` is `owner :: ancestors owner`, so an exclusive *descendant* of
the owner box is outside the scope while Clause 3 puts it inside the owner
rect.  The caption clearance therefore splits on descendant status:

* `CaptionDescendantClear` - `b` is a descendant of the owner: the caption sits
  in the reserved caption band, clear of every descendant box (the part-local
  caption/frame clearance plus descendant frame containment);
* `OwnerScopeExclusiveClear` - `b` is not a descendant: the owner scene box
  rect misses the interior of that foreign exclusive box;
* `OwnerCaptionContain` - the `ownedTextRect` fallback caption lies inside the
  owner scene box rect;
* `CaptionTitleBranchClear` - the installed-title branch of the caption rect.

The fallback branch of the non-descendant case is then pure monotonicity: a
caption inside the owner rect cannot meet a box whose rect misses the owner
rect. -/

namespace Elegant.Layered

/-- Symmetry of `meetsInterior` on rectangles (the definition is a symmetric
conjunction of `max`/`min` comparisons). -/
theorem rect_meetsInterior_comm {a b : Rect} (h : a.meetsInterior b) :
    b.meetsInterior a := by
  obtain ⟨hx, hy⟩ := h
  constructor <;> omega

/-- Monotonicity of `meetsInterior` in the first argument under `Contained`:
an inner rect that meets `other` forces its outer container to meet `other`. -/
theorem contained_meetsInterior_mono {outer inner other : Rect}
    (h : outer.Contained inner) (hm : inner.meetsInterior other) :
    outer.meetsInterior other := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := h
  obtain ⟨hmx, hmy⟩ := hm
  constructor <;> omega

/-- The group title inset stays inside the frame once the caption reservation
fits: the pad is nonnegative, twice the pad fits the frame width, and the pad
plus the title-band height fits the frame height. -/
theorem titleRect_contained {P : PipelineImpl.Params} {r : Rect}
    {lines : List Measure.Line}
    (hpad : 0 ≤ P.clusterPad)
    (hwidth : 2 * P.clusterPad ≤ r.w)
    (hfit : P.clusterPad + (max 1 lines.length : Int) * P.lineH ≤ r.h) :
    r.Contained (PipelineImpl.titleRect P r lines) := by
  unfold PipelineImpl.titleRect
  show r.x ≤ r.x + P.clusterPad ∧
    r.x + P.clusterPad + max 0 (r.w - 2 * P.clusterPad) ≤ r.x + r.w ∧
    r.y ≤ r.y + P.clusterPad ∧
    r.y + P.clusterPad + (max 1 lines.length : Int) * P.lineH ≤ r.y + r.h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- For a group-role owner box the `ownedTextRect` fallback is the title
inset of the owner rect. -/
theorem ownedTextRect_group_eq {P : PipelineImpl.Params} {box : Box}
    {lines : List Measure.Line} (hrole : box.role = "group") :
    PipelineImpl.ownedTextRect P box lines =
      PipelineImpl.titleRect P box.rect lines := by
  simp [PipelineImpl.ownedTextRect, hrole]

/-- The `ownedTextRect` fallback caption of the owner box lies inside the
owner scene box rect: the `titleRect` insets for group owners (with the
caption-sizing reservations) and the centered node-size inset otherwise. -/
def OwnerCaptionContain (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (ownerIndex : Nat),
    let ownerBox : Box :=
      (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩
    ownerBox.rect.Contained
      (PipelineImpl.ownedTextRect execution.params ownerBox
        (execution.lines.getD ownerIndex []))

/-- Scene sizing facts behind the caption fallback containment: every executed
scene carries nonnegative `clusterPad`, aligns the measured label lines with
the model boxes, and gives every real scene box the fit facts that
`ownedTextRect` containment needs (label height fits a node box; the caption
reservation fits a group box). -/
def SceneCaptionSizing (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res),
    0 ≤ execution.params.clusterPad ∧
    execution.lines.length = inp.boxes.length ∧
    ∀ (i : Nat) (box : Box),
      (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc)[i]? =
        some box →
      (box.role = "node" →
          ((execution.lines.getD i []).length : Int) * execution.params.lineH ≤
            box.rect.h) ∧
      (box.role = "group" →
          2 * execution.params.clusterPad ≤ box.rect.w ∧
          execution.params.clusterPad +
              (max 1 (execution.lines.getD i []).length : Int) *
              execution.params.lineH ≤
            box.rect.h)

/-- Discharge of the fallback-containment seam from scene sizing: the
`ownedTextRect` caption of the owner box lies inside the owner box rect — the
`titleRect` inset for group owners, the centered text inset for nodes, and
the trivial zero inset for indexes beyond the box list. -/
theorem ownerCaptionContain {inp : Input} {o : Options} {res : FamilyResult}
    (hsizing : SceneCaptionSizing inp o res) :
    OwnerCaptionContain inp o res := by
  intro execution ownerIndex
  show ((PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩).rect.Contained
    (PipelineImpl.ownedTextRect execution.params
      ((PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩)
      (execution.lines.getD ownerIndex []))
  obtain ⟨hpad, hlines, hfit⟩ := hsizing execution
  have hbl : (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).length
      = inp.boxes.length := by
    simp [PipelineImpl.sceneBoxesExpr]
  by_cases hi : ownerIndex <
      (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).length
  · obtain ⟨box, hbox⟩ : ∃ box : Box,
        (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
          some box := ⟨_, List.getElem?_eq_getElem hi⟩
    have hgetD : (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩ = box := by
      rw [List.getD_eq_getElem?_getD, hbox]
      rfl
    rw [hgetD]
    have hs := hfit ownerIndex box hbox
    by_cases hg : box.role = "group"
    · rw [ownedTextRect_group_eq hg]
      obtain ⟨hgw, hgh⟩ := hs.2 hg
      exact titleRect_contained hpad hgw hgh
    · unfold PipelineImpl.ownedTextRect
      rw [ite_eq_right (by simp [hg] : ¬((box.role == "group") = true))]
      have hnode : box.role = "node" := by
        simp only [PipelineImpl.sceneBoxesExpr, List.getElem?_map] at hbox
        cases hq : (inp.boxes.zipIdx)[ownerIndex]? with
        | none => rw [hq] at hbox; simp at hbox
        | some qy =>
          rw [hq] at hbox
          simp only [Option.map_some] at hbox
          obtain ⟨mb, mi⟩ := qy
          have hmk : Box.mk mb.id mb.role.id
              (PipelineImpl.shiftRect execution.params.canvasMargin
                execution.params.canvasMargin
                (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
                  (execution.packedAcc.rects.getD mi default)))
              mb.parent mb.exclusive = box := Option.some.inj hbox
          cases hroles : mb.role with
          | node => rw [← hmk]; simp only [hroles]; rfl
          | group => rw [← hmk] at hg; simp only [hroles, BoxRole.id] at hg; simp at hg
      have hf := hs.1 hnode
      have hpos : 0 ≤ execution.params.lineH := execution.parameter_signs.1
      have hprod : 0 ≤ ((execution.lines.getD ownerIndex []).length : Int) *
          execution.params.lineH :=
        Int.mul_nonneg (Int.natCast_nonneg _) hpos
      have hdiff : 0 ≤ box.rect.h -
          ((execution.lines.getD ownerIndex []).length : Int) *
            execution.params.lineH := by
        simpa using hf
      have hfeq : Int.fdiv (box.rect.h -
          ((execution.lines.getD ownerIndex []).length : Int) *
            execution.params.lineH) 2 =
          (box.rect.h -
            ((execution.lines.getD ownerIndex []).length : Int) *
              execution.params.lineH) / 2 :=
        Int.fdiv_eq_ediv_of_nonneg _ (by omega)
      have hhalf_nonneg : 0 ≤ (box.rect.h -
          ((execution.lines.getD ownerIndex []).length : Int) *
            execution.params.lineH) / 2 :=
        Int.ediv_nonneg hdiff (by decide)
      have hhalf_le : (box.rect.h -
          ((execution.lines.getD ownerIndex []).length : Int) *
            execution.params.lineH) / 2 ≤ box.rect.h -
          ((execution.lines.getD ownerIndex []).length : Int) *
            execution.params.lineH :=
        Int.ediv_le_self 2 hdiff
      dsimp only
      rw [hfeq]
      show box.rect.x ≤ box.rect.x ∧
        box.rect.x + box.rect.w ≤ box.rect.x + box.rect.w ∧
        box.rect.y ≤ box.rect.y + (box.rect.h - ((execution.lines.getD ownerIndex []).length : Int) * execution.params.lineH) / 2 ∧
        box.rect.y + (box.rect.h - ((execution.lines.getD ownerIndex []).length : Int) * execution.params.lineH) / 2 + ((execution.lines.getD ownerIndex []).length : Int) * execution.params.lineH ≤ box.rect.y + box.rect.h
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · have hlen : execution.lines.length ≤ ownerIndex := by omega
    have hge : (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).length
        ≤ ownerIndex := by omega
    have hll : execution.lines.getD ownerIndex [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
      rfl
    have hgetD : (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩ = (default : Box) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      rfl
    have hzero : (default : Box).rect = ⟨0, 0, 0, 0⟩ := rfl
    rw [hgetD, hll, hzero]
    show (⟨0, 0, 0, 0⟩ : Rect).Contained
      (PipelineImpl.ownedTextRect execution.params
        (Box.mk "" "" ⟨0, 0, 0, 0⟩ "" false) [])
    unfold PipelineImpl.ownedTextRect
    rw [ite_eq_right (by decide : ¬((("" : String) == "group") = true))]
    dsimp only
    simp only [List.length_nil, Int.ofNat_zero, Int.zero_mul]
    decide

/-- The descendant case of the caption clearance: an exclusive box that is a
proper descendant of the caption owner lies under the owner rect (Clause 3
transport), while the caption lies in the reserved caption band outside every
descendant box.  Discharge route: the part-local caption/frame clearance of
`LabelsC8bFacts` for the owner frame, frame containment of descendants, and
the shelf/margin transport of `sceneOf`. -/
def CaptionDescendantClear (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
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
    source.owner ∈ res.scene.layoutDump.ancestors b.id →
    ¬ (PipelineImpl.sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- The non-descendant case: an exclusive box outside the owner's subtree and
outside the owner scope misses the interior of the owner scene box rect. -/
def OwnerScopeExclusiveClear (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
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
    ¬ b.rect.meetsInterior
      ((PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩).rect


/-- The installed-title branch of the caption clearance: when the packed
accumulator carries an installed title for the owner, the substituted title
rect of `sceneCaptionRect` misses the interior of every foreign exclusive dump
box.  Discharge route: the part-local caption/frame clearance
(`LabelsC8bFacts`) transported through the `Pack.pack` shelf shift and the
margin/orientation projection. -/
def CaptionTitleBranchClear (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
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
    ((PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find?
          (fun title => title.1 == source.owner)).isSome = true →
    ¬ (PipelineImpl.sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- The caption seam of flat clause 7: the caption rect of the non-exclusive
owner box misses the interior of every foreign exclusive dump box.  The
descendant case is `CaptionDescendantClear`; the non-descendant case follows
from `OwnerCaptionContain` and `OwnerScopeExclusiveClear` by monotonicity for
the fallback caption, and is `CaptionTitleBranchClear` for an installed
title. -/
theorem captionScopeClearance {inp : Input} {o : Options} {res : FamilyResult}
    (hdesc : CaptionDescendantClear inp o res)
    (hcontain : OwnerCaptionContain inp o res)
    (howners : OwnerScopeExclusiveClear inp o res)
    (htitle : CaptionTitleBranchClear inp o res) :
    CaptionScopeClearance inp o res := by
  intro execution index ownerIndex source lines b hsrc hmeas hfindIdx hmem hex hscope
  by_cases hd : source.owner ∈ res.scene.layoutDump.ancestors b.id
  · exact hdesc execution index ownerIndex source lines b hsrc hmeas hfindIdx
      hmem hex hscope hd
  · have hclr := howners execution index ownerIndex source lines b hsrc hmeas
      hfindIdx hmem hex hscope hd
    simp only [PipelineImpl.sceneCaptionRect]
    cases hopt : (PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      have hc := hcontain execution ownerIndex
      exact fun hmeet =>
        hclr (rect_meetsInterior_comm (contained_meetsInterior_mono hc hmeet))
    | some t =>
      simp only [Option.map_some, Option.getD_some]
      have ht := htitle execution index ownerIndex source lines b hsrc hmeas
        hfindIdx hmem hex hscope (by rw [hopt]; rfl)
      simp only [PipelineImpl.sceneCaptionRect] at ht
      rw [hopt] at ht
      simp only [Option.map_some, Option.getD_some] at ht
      exact ht

end Elegant.Layered

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
* `OwnerCaptionContainFallback` - the `ownedTextRect` fallback caption lies inside the
  owner scene box rect when the owner has no installed title;
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
 owner scene box rect, pinned to the executed fallback run: the owner input box
 at `ownerIndex` carries no installed title. The owner is non-exclusive and owns
 a label, matching the `sceneOf` fallback emission. -/
def OwnerCaptionContainFallback (inp : Input) (o : Options)
     (res : FamilyResult) : Prop :=
   ∀ (execution : PipelineImpl.SceneExecution inp o res) (ownerIndex : Nat)
     (obox : ModelBox),
     inp.boxes[ownerIndex]? = some obox →
     (PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
         execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
     obox.exclusive = false →
     (∃ l ∈ inp.labels, l.owner = obox.id) →
     let ownerBox : Box :=
       (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
         ownerIndex ⟨"", "", default, "", false⟩
     ownerBox.rect.Contained
       (PipelineImpl.ownedTextRect execution.params ownerBox
         (execution.lines.getD ownerIndex []))

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
    (PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) = none →
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

/-- A `findIdx?` hit exposes the box at that index and its predicate value
(local copy of the private `CaptionOwnerScopeFacts` helper). -/
private theorem captionScope_findIdx_lookup {α : Type} {p : α → Bool} {l : List α}
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

/-- The caption seam of flat clause 7: the caption rect of the non-exclusive
owner box misses the interior of every foreign exclusive dump box.  The
descendant case is `CaptionDescendantClear`; the non-descendant case follows
from `OwnerCaptionContainFallback` and `OwnerScopeExclusiveClear` by monotonicity for
the fallback caption, and is `CaptionTitleBranchClear` for an installed
title. -/
theorem captionScopeClearance {inp : Input} {o : Options} {res : FamilyResult}
    (hdesc : CaptionDescendantClear inp o res)
    (hcontain : OwnerCaptionContainFallback inp o res)
    (howners : OwnerScopeExclusiveClear inp o res)
    (htitle : CaptionTitleBranchClear inp o res) :
    CaptionScopeClearance inp o res := by
  intro execution index ownerIndex source lines b hsrc hmeas hfindIdx hmem hex hscope
  by_cases hd : source.owner ∈ res.scene.layoutDump.ancestors b.id
  · exact hdesc execution index ownerIndex source lines b hsrc hmeas hfindIdx
      hmem hex hscope hd
  · simp only [PipelineImpl.sceneCaptionRect]
    cases hopt : (PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      have hclr := howners execution index ownerIndex source lines b hsrc hmeas
        hfindIdx hmem hex hscope hd hopt
      obtain ⟨_, obox, hobox, hpobox⟩ := captionScope_findIdx_lookup hfindIdx
      have heq : obox.id = source.owner := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hpobox
        exact hpobox.1
      have hnone : (PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
          execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
        rw [heq]
        exact hopt
      have hexcl : obox.exclusive = false := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hpobox
        simpa using hpobox.2
      have hown : ∃ l ∈ inp.labels, l.owner = obox.id :=
        ⟨source, List.mem_of_getElem? hsrc, heq.symm⟩
      have hc := hcontain execution ownerIndex obox hobox hnone hexcl hown
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

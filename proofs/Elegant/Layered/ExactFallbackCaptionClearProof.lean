import Elegant.Layered.ExactFlatC8b
import Elegant.Layered.ExactCaptionFallbackProof
import Elegant.Layered.LabelsC8b
import Elegant.Layered.PartFrameCoresProof
import Elegant.Layered.ExactFlatFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact fallback caption clearance from three single-fact residuals.

Target: `X_fallbackCaptionClearB8_holds : X_FallbackCaptionClearB8 exactIds`,
the exact seam fact consumed by `flatC8bB_layoutX`
(`ExactFlatC8b.lean:469`) as `hfall`. It mirrors `fallbackCaptionClear_of_fit`
(`FallbackCaptionClearProof.lean:59`) over `SceneExecutionX`: the fallback
caption of an owner with no installed title clears every group frame once the
fixed-size fit premise holds.

Probe evidence (`proofs/wip/Probe/ExactFallbackCaptionClearTProbe.lean`,
vector profile, `layoutX [] inp tOpts` recomputed phases): the conclusion is
true on every row. The rows with fixed groups too small for their title
(`fb-fixed-300x200`, `fb-fixed-0x0`, `fb-wide-short`, `fb-narrow-tall`) make
the `InputFixedFit` premise false, so the target holds vacuously there; the
fitting rows (`fb-fit-5000`, `fb-nest-fit`, `fb-nofix`, `fb-desc`) satisfy the
raw clearance directly. No narrower fit-conditioned variant is needed: the
tracked def already carries the fit premise, which is exactly what excludes
the too-small witnesses.

The proof replays the plain derivation with three hypotheses, each a single
fact strictly narrower than the goal and true on the probe rows:

* `X_OwnerCaptionContainFallbackFit` (existing,
  `ExactCaptionFallbackProof.lean:113`): the owner caption lies inside the
  owner frame under fit; vacuous on the unfitting rows, direct on the fitting
  rows;
* `X_FallbackGroupStrictCaption` (below): a group-role owner frame lies
  strictly inside its fallback caption under fit; vacuous on the unfitting
  and installed-title rows, direct on the fitting fallback rows;
* `X_FallbackOwnerFrameClearX` (below): every group scene box is disjoint
  from the owner frame, strictly contains it in the strict sense, or is the
  owner scene box itself; true on every probe row, with the equality disjunct
  discharging the owner itself without a global uniqueness premise.
-/

/-- Exact group-owner strict caption: under the fixed-size fit premise, the
fallback caption of a group-role owner with no installed title lies strictly
inside the owner frame. Field for field the strict half of the plain
`hcapGroup` step (`FallbackCaptionClearProof.lean:106`), which derives it from
`titleRect_strictInside_of_fit` and the fixed-owner fit. -/
def X_FallbackGroupStrictCaption (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res),
    InputFixedFit inp o →
    ∀ (ownerIndex : Nat) (obox : ModelBox),
      inp.boxes[ownerIndex]? = some obox →
      (sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
      obox.exclusive = false →
      (∃ l ∈ inp.labels, l.owner = obox.id) →
      obox.role = .group →
      ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩).rect.StrictInside
        (ownedTextRect execution.params
          ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
            ownerIndex ⟨"", "", default, "", false⟩)
          (execution.lines.getD ownerIndex []))

 /-- Exact owner-frame fact: every group scene box is disjoint from the owner
 frame, strictly contains it in the strict sense, or is the owner scene box
 itself. The first two disjuncts mirror `FallbackOwnerFrameClear`
 (`FallbackCaptionClearProof.lean:24`); the equality disjunct covers the owner
 itself, which the plain residual excludes by `g.id ≠ obox.id` and the plain
 proof discharges via the global box-id uniqueness. -/
def X_FallbackOwnerFrameClearX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (ownerIndex : Nat) (obox : ModelBox) (g : Box),
    inp.boxes[ownerIndex]? = some obox →
    (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
    g ∈ res.scene.boxes → g.role = "group" →
    Disjoint g.rect
      ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩).rect ∨
      g.rect.StrictInside
        ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
          ownerIndex ⟨"", "", default, "", false⟩).rect ∨
      g = (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩
 /-- `xfb_` copy of the `sceneBoxesExpr` bridge: the exact scene boxes are the
 `sceneBoxesExpr` projection. Same map as `boxes_eq_mapX`, so definitional. -/
 private theorem xfb_sceneBoxes_eq {exactIds : List String} {inp : Input}
     {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res) :
     res.scene.boxes =
       sceneBoxesExpr execution.params inp o execution.packedAcc := by
   rw [execution.boxes_eq_mapX]
   rfl

 /-- `xfb_` copy of the `xcf_box_index_origin` transport
 (`ExactCaptionFitFactsProof.lean`): the scene box at `index` comes from the
 input box at the same index. Private lemmas do not resolve across modules. -/
 private theorem xfb_box_index_origin {exactIds : List String} {inp : Input}
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

 /-- The exact fallback-caption clearance from the three single-fact residuals.
 Replay of `fallbackCaptionClear_of_fit` over `SceneExecutionX`: containment
 positions the caption inside the owner frame, the frame residual separates
 every other group frame from it (or identifies the owner itself), and the
 group-strict residual covers the owner itself. -/
 theorem X_fallbackCaptionClearB8_holds (exactIds : List String)
     (hcontain : X_OwnerCaptionContainFallbackFit exactIds)
     (hstrict : X_FallbackGroupStrictCaption exactIds)
     (hframe : X_FallbackOwnerFrameClearX exactIds) :
     X_FallbackCaptionClearB8 exactIds := by
   intro inp o res execution hfit source index ownerIndex g hsrc hfind hnone hgMem hgRole
   obtain ⟨hlt, hpred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
   obtain ⟨obox, hobox⟩ : ∃ obox, inp.boxes[ownerIndex]? = some obox :=
     ⟨_, List.getElem?_eq_getElem hlt⟩
   have hge : inp.boxes[ownerIndex] = obox :=
     Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hobox)
   rw [hge] at hpred
   simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hpred
   obtain ⟨hownId, hex⟩ := hpred
   have hnone' : (sceneTitlesExpr execution.params inp o execution.lines
       execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
     rw [hownId]
     exact hnone
   have hown : ∃ l ∈ inp.labels, l.owner = obox.id :=
     ⟨source, List.mem_of_getElem? hsrc, hownId.symm⟩
   have hbl : (sceneBoxesExpr execution.params inp o execution.packedAcc).length
       = inp.boxes.length := by
     simp [sceneBoxesExpr]
   have hi : ownerIndex <
       (sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
     omega
   obtain ⟨obv, hobb⟩ : ∃ box : Box,
       (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
         some box := ⟨_, List.getElem?_eq_getElem hi⟩
   have hgetD : (sceneBoxesExpr execution.params inp o
       execution.packedAcc).getD
       ownerIndex ⟨"", "", default, "", false⟩ = obv := by
     rw [List.getD_eq_getElem?_getD, hobb]
     rfl
   have hboxScene : res.scene.boxes[ownerIndex]? = some obv := by
     rw [xfb_sceneBoxes_eq execution]
     exact hobb
   obtain ⟨actual, hactual, hboxeq⟩ := xfb_box_index_origin execution hboxScene
   rw [hobox] at hactual
   have hact : actual = obox := (Option.some.inj hactual).symm
   have hroleEq : obv.role = obox.role.id := by rw [hboxeq, hact]
   have hcontFull : obv.rect.Contained (ownedTextRect execution.params obv
       (execution.lines.getD ownerIndex [])) := by
     have h := hcontain inp o res execution hfit ownerIndex obox hobox hnone'
       hex hown
     rw [hgetD] at h
     exact h
   rw [hgetD]
   show Disjoint g.rect (ownedTextRect execution.params obv
       (execution.lines.getD ownerIndex [])) ∨
     g.rect.StrictInside (ownedTextRect execution.params obv
       (execution.lines.getD ownerIndex []))
   have hfr := hframe execution ownerIndex obox g hobox hnone' hgMem hgRole
   rw [hgetD] at hfr
   rcases hfr with hdisj | hstrictfr | heq
   · exact Or.inl ((Disjoint.comm _ _).mpr
       (disjoint_of_sub_disjoint hcontFull ((Disjoint.comm _ _).mp hdisj)))
   · by_cases hgr : obox.role = .group
     · have hsc :=
         hstrict execution hfit ownerIndex obox hobox hnone' hex hown hgr
       rw [hgetD] at hsc
       have hcont2 : g.rect.Contained obv.rect := by
         unfold Rect.StrictInside at hstrictfr
         unfold Rect.Contained at ⊢
         omega
       exact Or.inr (strictInside_of_contained hsc hcont2)
     · have hgoal : g.rect.StrictInside (ownedTextRect execution.params obv
           (execution.lines.getD ownerIndex [])) := by
           unfold Rect.StrictInside at hstrictfr ⊢
           unfold Rect.Contained at hcontFull
           omega
       exact Or.inr hgoal
   · subst heq
     have hgr : obox.role = .group := by
       rw [hroleEq] at hgRole
       cases h : obox.role with
       | node =>
         rw [h] at hgRole
         simp only [BoxRole.id] at hgRole
         exact absurd hgRole (by decide)
       | group => rfl
     have hsc :=
       hstrict execution hfit ownerIndex obox hobox hnone' hex hown hgr
     rw [hgetD] at hsc
     exact Or.inr hsc
end PipelineImpl
end Layered
end Elegant

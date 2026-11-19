import Elegant.Layered.ExactStepLeafFactsProof
import Elegant.Layered.ExactStepGeometryProof
import Elegant.Layered.ExactFitClosure
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.FramedParentsSub
import Elegant.Layered.InputFixedFit

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Validator

/-! # Exact recursive-step child-label inset.

Closes the open `XSGL_StepC8bChildLabelsFit` leaf of
`ExactStepLeafFactsProof.lean` by reduction to a strictly narrower flat
residual: labels of the child scene lie in the child margin inset.

Proved: `xsgl_stepC8bChildLabelsFit_holds` derives
`XSGL_StepC8bChildLabelsFit exactIds` from the flat residual below, by fuel
induction over `layoutRecursiveB (layoutX exactIds)` (mirror of the plain
`layoutRecursive_labels_inset`): the base-direct cases use the residual, and
each expansion merge transports shifted child labels through the executed
exact frame fit (`XG_frame_fitB`), parent labels verbatim through the
`layoutRecursiveB` box inset, and group captions through the exact title
band, reusing `expandChild_labels_eq_wrapped`.

Stays open: `XSCL_FlatChildLabelsFit`, the fuel-zero/base-direct case over
`layoutX` (labels of a successful flat exact layout lie in the margin
inset). It is strictly narrower than the target (flat base only, no
recursion) and a lemma on the way. True on all sixteen `SCLT` probes
(`proofs/wip/Probe/StepChildLabelsTProbe.lean`: eight flat runs under `[]`,
eight child runs under `["g"]`/`["g1", "g2"]`; non-vacuous on the
member-owned and group-caption label inputs; degenerate empty-group,
zero-size fixed box, duplicate-id, nested-group, and self-loop inputs all
`ok=true`). The remaining work is the replay of `flat_layout_labels_inset`
over `SceneExecutionX` via `componentRunX_spec` and `exactPartsBounded'`.
-/

/-- Narrower residual for `XSGL_StepC8bChildLabelsFit`: labels of a successful
flat exact layout lie in the margin inset of its canvas. Fuel-zero and
base-direct case of the `layoutRecursiveB` label induction below. True on all
eight `SCLT_flatRun` probes; the `SceneExecutionX` replay of
`flat_layout_labels_inset` is left open. -/
def XSCL_FlatChildLabelsFit (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    InputFixedFit inp o →
    layoutX exactIds inp o = .ok res →
    ∀ Q : Params, checkedParams o.profile inp.kind = .ok Q →
    ∀ cl ∈ res.scene.labels,
      (insetRect res.scene.canvas Q.canvasMargin).Contained cl.rect

/-- `xscl_` copy of the private `titleWidth_nonneg`
(`ExpandChildTitleBandProof.lean`). -/
private theorem xscl_titleWidth_nonneg (ls : List Measure.Line) :
    0 ≤ ls.foldl (fun width line => max width line.width) 0 := by
  suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
      0 ≤ ls.foldl (fun width line => max width line.width) acc by
    exact key ls 0 (by omega)
  intro ls acc hac
  induction ls generalizing acc with
  | nil => simpa using hac
  | cons line ls ih =>
    simp only [List.foldl_cons]
    exact ih _ (Int.le_trans hac (Int.le_max_left _ _))

/-- `xscl_` copy of the private `titleRect_contained_aux`
(`ExpandChildTitleBandProof.lean`). -/
private theorem xscl_titleRect_contained_aux {direction : String}
    {pad tw th conw conh fx fy fw fh : Int}
    (hpad : 0 ≤ pad)
    (hconw : 0 ≤ conw) (hconh : 0 ≤ conh)
    (hfw : (childFrameSize direction pad tw th ⟨conw, conh⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad tw th ⟨conw, conh⟩).h ≤ fh) :
    (⟨fx, fy, fw, fh⟩ : Rect).Contained
      (childTitleRect direction pad tw th ⟨fx, fy, fw, fh⟩) := by
  have htw : tw + 2 * pad ≤ fw := by
    unfold childFrameSize at hfw
    split at hfw <;> dsimp only at hfw <;> omega
  have hth : th + 2 * pad ≤ fh := by
    unfold childFrameSize at hfh
    split at hfh <;> dsimp only at hfh <;> omega
  unfold childTitleRect
  split <;> unfold Rect.Contained <;> dsimp only <;>
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] <;> omega

/-- `xscl_` copy of the private `titleInset_disjoint_aux`
(`ExpandChildTitleBandProof.lean`). -/
private theorem xscl_titleInset_disjoint_aux {direction : String}
    {pad tw th margin cw ch fx fy fw fh dx dy : Int}
    (htw : 0 ≤ tw) (hth : 0 ≤ th)
    (hfw : (childFrameSize direction pad tw th
      ⟨cw - 2 * margin, ch - 2 * margin⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad tw th
      ⟨cw - 2 * margin, ch - 2 * margin⟩).h ≤ fh)
    (hdx : dx = fx + (childInset direction pad tw th).x - margin)
    (hdy : dy = fy + (childInset direction pad tw th).y - margin) :
    Disjoint (childTitleRect direction pad tw th ⟨fx, fy, fw, fh⟩)
      (shiftRect dx dy (insetRect ⟨cw, ch⟩ margin)) := by
  have hdir : direction = "LR" ∨ direction = "RL" ∨ direction = "BT" ∨
      (direction ≠ "LR" ∧ direction ≠ "RL" ∧ direction ≠ "BT") := by
    by_cases h1 : direction = "LR"
    · exact Or.inl h1
    · by_cases h2 : direction = "RL"
      · exact Or.inr (Or.inl h2)
      · by_cases h3 : direction = "BT"
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
  rcases hdir with hLR | hRL | hBT | ⟨hnLR, hnRL, hnBT⟩
  · rw [hLR] at hfw hfh hdx hdy ⊢
    simp only [childTitleRect, childInset, childFrameSize, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega
  · rw [hRL] at hfw hfh hdx hdy ⊢
    simp only [childTitleRect, childInset, childFrameSize, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega
  · rw [hBT] at hfw hfh hdx hdy ⊢
    have eW : (childFrameSize "BT" pad tw th
        ⟨cw - 2 * margin, ch - 2 * margin⟩).w
        = max (cw - 2 * margin) tw + 2 * pad := rfl
    have eH : (childFrameSize "BT" pad tw th
        ⟨cw - 2 * margin, ch - 2 * margin⟩).h
        = ch - 2 * margin + th + 2 * pad := rfl
    rw [eW] at hfw
    rw [eH] at hfh
    simp only [childTitleRect, childInset, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega
  · simp only [childTitleRect, childInset, childFrameSize, shiftRect, insetRect,
      Disjoint, Rect.meetsInterior] at hfw hfh hdx hdy ⊢
    omega

/-- Exact title band: the group caption rect lies in the located frame and
misses the shifted child margin inset. `xscl_` copy of `xsgl_title_band`
(`ExactStepLeafFactsProof.lean`) with the exact frame reservation
(`XG_frame_size_bounds`) and the exact canvas margins
(`exactCanvasMargins`). -/
private theorem xscl_title_band (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    frame.rect.Contained (groupTitleRect group P titleLines' titleHeight frame) ∧
    Disjoint (groupTitleRect group P titleLines' titleHeight frame)
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
  intro frame titleLines' dx dy hfind hdx hdy hwrap
  have hP := hparams.1
  have hheightEq := hparams.2.1
  have hpad : 0 ≤ P.clusterPad := checkedParams_clusterPad_nonneg hP
  have hth : 0 ≤ titleHeight := by
    rw [hheightEq]
    exact Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP)
  have hchild : layoutRecursiveB (layoutX exactIds) fuel
      (childSubInput inp group) (childSubOptions o group) = .ok child :=
    hctxB.2.2.2.1
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  have hcon := (exactCanvasMargins exactIds) fuel _ _ _ hchild P hQchild
  have hconw : 0 ≤ child.scene.canvas.w - 2 * P.canvasMargin := by omega
  have hconh : 0 ≤ child.scene.canvas.h - 2 * P.canvasMargin := by omega
  obtain ⟨hfw, hfh⟩ := XG_frame_size_bounds exactIds fuel P inp o group
    titleLines titleHeight parent child res hexpand hframed hctxB hparams
    frame titleLines' hfind hwrap
  have htw := xscl_titleWidth_nonneg titleLines'
  refine ⟨?_, ?_⟩
  · unfold groupTitleRect
    exact xscl_titleRect_contained_aux hpad hconw hconh hfw hfh
  · unfold groupTitleRect
    exact xscl_titleInset_disjoint_aux htw hth hfw hfh hdx hdy

/-- Labels of a successful `layoutRecursiveB (layoutX exactIds)` lie in the
margin inset of the canvas. Mirror of `layoutRecursive_labels_inset`, with
the flat case as the `XSCL_FlatChildLabelsFit` residual and the expansion
merge through the executed exact frame fit (`XG_frame_fitB`), the exact
title band, and the `layoutRecursiveB` box inset. -/
private theorem xscl_layoutRecursiveB_labels_inset (exactIds : List String)
    (hbase : XSCL_FlatChildLabelsFit exactIds) (fuel : Nat) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) →
      framedParents inp = true →
      InputFixedFit inp o →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ Q : Params, checkedParams o.profile inp.kind = .ok Q →
      ∀ cl ∈ res.scene.labels,
        (insetRect res.scene.canvas Q.canvasMargin).Contained cl.rect := by
  induction fuel with
  | zero =>
    intro inp o res hwf hframed hfit h Q hQ cl hcl
    exact hbase inp o res hwf hframed hfit h Q hQ cl hcl
  | succ fuel ih =>
    intro inp o res hwf hframed hfit h Q hQ cl hcl
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with ⟨_, hlayout⟩ |
      ⟨group, Pm, metric, child, titleLines, parent, hg, hPm, hm, hc, ht, hp,
        hexpand⟩
    · exact hbase inp o res hwf hframed hfit hlayout Q hQ cl hcl
    · have hQm : Pm = Q := Except.ok.inj (hPm.symm.trans hQ)
      subst hQm
      obtain ⟨hwfChild, hparentWF⟩ := subInputWellFormedC2 inp o group hwf
      obtain ⟨hframedChild, hframedParentSub⟩ :=
        framedParentsSub inp o group hwf hframed
      have hframedParent : framedParents
          (parentSubInput inp group Pm titleLines child) = true :=
        hframedParentSub _ _ _
      have hQchild : checkedParams (childSubOptions o group).profile
          (childSubInput inp group).kind = .ok Pm := hPm
      have hQparent : checkedParams o.profile
          (parentSubInput inp group Pm titleLines child).kind = .ok Pm := hPm
      have hfitChild : InputFixedFit (childSubInput inp group)
          (childSubOptions o group) := hfit.childSubInput group
      have hcm := (exactCanvasMargins exactIds) fuel _ _ _ hc Pm hQchild
      have hfitParent : InputFixedFit
          (parentSubInput inp group Pm titleLines child) o :=
        InputFixedFit.parentSubInput hwf hfit hPm hm ht hcm.1 hcm.2
      have hcIH := ih (childSubInput inp group) (childSubOptions o group) child
        hwfChild hframedChild hfitChild hc Pm hQchild
      have hwfParent : WellFormed
          (inputModel (parentSubInput inp group Pm titleLines child) o) :=
        hparentWF _ _ _
      have hpIH := ih (parentSubInput inp group Pm titleLines child) o parent
        hwfParent hframedParent hfitParent hp Pm hQparent
      obtain ⟨frame, metricS, ftl, _linesS, fdx, fdy, hframe, hmS, htlS, _hlS,
        hdxS, hdyS, hcanvasS, _hboxesS⟩ := expandChild_sources hexpand
      have hmetricSeq : metric = metricS :=
        Except.ok.inj (hm.symm.trans hmS)
      subst hmetricSeq
      have htlSeq : titleLines = ftl :=
        Except.ok.inj (ht.symm.trans htlS)
      subst htlSeq
      have hwrapS : ExpandChildTitleWrapped Pm inp o group titleLines :=
        ⟨metric, hm, ht⟩
      have hlabelsEq := expandChild_labels_eq_wrapped hexpand frame titleLines
        fdx fdy hframe hdxS hdyS hwrapS
      have hctxB : ExpandChildCallContextB (layoutX exactIds) fuel Pm inp o
          group titleLines ((max 1 titleLines.length : Int) * Pm.lineH)
          parent child res :=
        ⟨hwf, hg, rfl, hc, hp, hexpand⟩
      have hparams : ExpandChildCallParams Pm inp o group titleLines
          ((max 1 titleLines.length : Int) * Pm.lineH) :=
        ⟨hPm, rfl, hwrapS⟩
      have hfitFrame : frame.rect.Contained
          (shiftRect fdx fdy (insetRect child.scene.canvas Pm.canvasMargin)) :=
        XG_frame_fitB exactIds fuel Pm inp o group titleLines
          ((max 1 titleLines.length : Int) * Pm.lineH) parent child res
          hexpand hframed hctxB hparams frame fdx fdy hframe hdxS hdyS
      have hparentInset := (layoutRecursiveB_inset (layoutX exactIds)
        (XG_flatInset exactIds) subInputWellFormedC2 (exactFitClosed exactIds)
        fuel _ _ _ hwfParent hframedParent hp Pm hQparent).2
      have hband := xscl_title_band exactIds fuel Pm inp o group titleLines
        ((max 1 titleLines.length : Int) * Pm.lineH) parent child res
        hexpand hframed hctxB hparams
        frame titleLines fdx fdy hframe hdxS hdyS hwrapS
      rw [hlabelsEq] at hcl
      obtain ⟨model, _hmodel, hbind⟩ := List.mem_filterMap.mp hcl
      cases hfind : (((child.scene.labels.map fun label : SceneLabel =>
          { label with rect := shiftRect fdx fdy label.rect }) ++
        parent.scene.labels).find? (fun label : SceneLabel =>
          label.id == model.id)) with
      | none => rw [hfind] at hbind; simp at hbind
      | some label =>
        rw [hfind, Option.bind_some] at hbind
        have hclEq := Option.some.inj hbind
        by_cases hown : (model.owner == group.id) = true
        · rw [hown] at hclEq
          simp only [reduceIte] at hclEq
          have hframeMem : frame ∈ parent.scene.boxes :=
            List.mem_of_find?_eq_some hframe
          have hcapFrame : frame.rect.Contained
              (groupTitleRect group Pm titleLines
                ((max 1 titleLines.length : Int) * Pm.lineH) frame) :=
            hband.1
          have hframeIn : (insetRect parent.scene.canvas Pm.canvasMargin).Contained
              frame.rect := hparentInset frame hframeMem
          rw [hcanvasS, ← hclEq]
          exact Rect.Contained.trans hframeIn hcapFrame
        · have hcondF : (model.owner == group.id) = false := by
            cases hb : (model.owner == group.id) with
            | false => rfl
            | true => exact absurd hb hown
          rw [hcondF] at hclEq
          simp only [Bool.false_eq_true, reduceIte] at hclEq
          have hlabelMem : label ∈ (child.scene.labels.map
              (fun l => { l with rect := shiftRect fdx fdy l.rect })) ++
              parent.scene.labels := List.mem_of_find?_eq_some hfind
          rcases List.mem_append.mp hlabelMem with hcm | hpm
          · obtain ⟨cl', hcl'mem, hcl'Eq⟩ := List.mem_map.mp hcm
            have hclIH : (insetRect child.scene.canvas Pm.canvasMargin).Contained
                cl'.rect := hcIH cl' hcl'mem
            have hshiftC : (shiftRect fdx fdy
                (insetRect child.scene.canvas Pm.canvasMargin)).Contained
                (shiftRect fdx fdy cl'.rect) :=
              (contained_shiftRect fdx fdy).mpr hclIH
            have hframeMem : frame ∈ parent.scene.boxes :=
              List.mem_of_find?_eq_some hframe
            have hframeIn : (insetRect parent.scene.canvas
                Pm.canvasMargin).Contained frame.rect :=
              hparentInset frame hframeMem
            have hclRect : cl.rect = shiftRect fdx fdy cl'.rect := by
              rw [← hclEq, ← hcl'Eq]
            rw [hcanvasS, hclRect]
            exact Rect.Contained.trans hframeIn
              (Rect.Contained.trans hfitFrame hshiftC)
          · have hclRect : cl.rect = label.rect := by rw [← hclEq]
            rw [hcanvasS, hclRect]
            exact hpIH label hpm

/-- Reduction of the open `XSGL_StepC8bChildLabelsFit` leaf to the flat
residual: the child scene of every executed exact `expandChild` call
satisfies the label inset, from the caller `InputFixedFit` premise the plain
`expandChild_child_labels_inset` needs. The child success in the call
context is a `layoutRecursiveB (layoutX exactIds)` success at the child
sub-input, so the `B` label induction above applies with the well-formedness,
framed-parents, fit, and checked-params facts threaded to the child exactly
as in the plain derivation. -/
theorem xsgl_stepC8bChildLabelsFit_holds (exactIds : List String)
    (hbase : XSCL_FlatChildLabelsFit exactIds) :
    XSGL_StepC8bChildLabelsFit exactIds := by
  intro fuel P inp o group _titleLines _titleHeight _parent child _res _hexpand
    hframed hctxB hparams hfit cl hcl
  obtain ⟨hwf, _hgroup, _hpboxes, hchild, _hparent, _hexpand'⟩ := hctxB
  obtain ⟨hP, _hheightEq, _hwrapCtx⟩ := hparams
  have hwfChild : WellFormed
      (inputModel (childSubInput inp group) (childSubOptions o group)) :=
    (subInputWellFormedC2 inp o group hwf).1
  have hframedChild : framedParents (childSubInput inp group) = true :=
    (framedParentsSub inp o group hwf hframed).1
  have hQchild : checkedParams (childSubOptions o group).profile
      (childSubInput inp group).kind = .ok P := hP
  have hfitChild : InputFixedFit (childSubInput inp group)
      (childSubOptions o group) := hfit.childSubInput group
  exact xscl_layoutRecursiveB_labels_inset exactIds hbase fuel _ _ _
    hwfChild hframedChild hfitChild hchild P hQchild cl hcl

end PipelineImpl
end Layered
end Elegant

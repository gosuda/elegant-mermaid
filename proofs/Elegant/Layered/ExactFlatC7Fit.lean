import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactFlatC7Forward
import Elegant.Layered.ExactFlatC7Reversed
import Elegant.Layered.ExactFlatC7Placed
import Elegant.Layered.ExactFlatC7ExclusiveKey
import Elegant.Layered.ExactCaptionFallbackProof
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.InputFixedFit

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Fit-conditioned flat C7 for the exact pipeline.

`flatC7B_layoutX_fit` replays `flatC7B_layoutX` (`ExactFlatC7.lean`) over the
new `FlatC7B`, which threads `InputFixedFit inp o` like the `captions` seam.
The five non-caption premises close by the tracked proved facts; the caption
branch closes by the fit-conditioned residual `X_CaptionScopeClearanceFit`
through the local `xc7f_` copies below. -/

/-- `xc7f_` copy of the private `X_caption_index_eq_of_id_eq`
(`ExactFlatC7.lean`): two positions of a model label list whose labels share
an id are equal. Private lemmas do not resolve across modules. -/
private theorem xc7f_caption_index_eq_of_id_eq {l : List ModelLabel}
    (hn : (l.map (·.id)).Nodup) {i j : Nat} {a b : ModelLabel}
    (hi : l[i]? = some a) (hj : l[j]? = some b) (hid : a.id = b.id) : i = j := by
  have hin : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjn : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hget : (l.map (·.id))[i]? = (l.map (·.id))[j]? := by
    rw [List.getElem?_map, hi, List.getElem?_map, hj]
    simp only [Option.map_some]
    exact congrArg Option.some hid
  have e1 : (l.map (·.id))[i]? = some a.id := by
    rw [List.getElem?_map, hi, Option.map_some]
  have e2 : (l.map (·.id))[j]? = some a.id := by
    rw [List.getElem?_map, hj, Option.map_some, hid]
  have h3 : i < (l.map (·.id)).length := by simpa using hin
  have h4 : j < (l.map (·.id)).length := by simpa using hjn
  have hv : (l.map (·.id))[i]'h3 = (l.map (·.id))[j]'h4 :=
    Option.some.inj ((List.getElem?_eq_getElem h3).symm.trans (e1.trans (e2.symm.trans
      (List.getElem?_eq_getElem h4))))
  have hp := List.pairwise_iff_getElem.mp hn
  by_cases hlt : i < j
  · exact absurd hv (hp i j h3 h4 hlt)
  · by_cases hjt : j < i
    · exact absurd hv.symm (hp j i h4 h3 hjt)
    · omega

/-- Fit-conditioned X caption containment: mirror of
`X_sceneCaptionBoxContainment` (`ExactFlatC7.lean`) over the fit-conditioned
residual. The single use of the unconditional clearance becomes the supplied
`hclearFit` at the ambient `hfit`. -/
theorem xc7f_sceneCaptionBoxContainmentFit {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfit : InputFixedFit inp o)
    (hclearFit : X_CaptionScopeClearanceFit exactIds) :
    X_SceneCaptionBoxContainment exactIds inp o res := by
  intro execution l index source hl hsrc hid hmeas howner b hb hex hscope
  rw [execution.scene_eq] at hl
  obtain ⟨q, hq, hemitted⟩ := List.mem_filterMap.mp hl
  obtain ⟨lmodel, lindex⟩ := q
  have hsrcL : inp.labels[lindex]? = some lmodel := List.mem_zipIdx_iff_getElem?.mp hq
  have hlabelNodes := Elegant.Layered.labelIds_nodup hwf
  cases hexcl : inp.boxes.any
      (fun box => box.id == lmodel.owner && box.exclusive) with
  | true =>
    rw [hexcl] at hemitted
    simp only [↓reduceIte] at hemitted
    cases hemitted
  | false =>
    rw [hexcl] at hemitted
    simp only at hemitted
    cases hm : execution.measured.find? (fun item => item.index == lindex) with
    | some measured =>
      rw [hm] at hemitted
      have heq : l = _ := (Option.some.inj hemitted).symm
      have hidEq : lmodel.id = source.id := by
        have h1 : l.id = lmodel.id := by rw [heq]
        exact h1.symm.trans hid
      have hindex : lindex = index :=
        xc7f_caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
      rw [hindex] at hm
      rw [hm] at hmeas
      cases hmeas
    | none =>
      rw [hm] at hemitted
      cases ho : inp.boxes.findIdx?
          (fun box => box.id == lmodel.owner && !box.exclusive) with
      | none =>
        rw [ho] at hemitted
        cases hemitted
      | some ownerIndex =>
        rw [ho] at hemitted
        have heq : l = _ := (Option.some.inj hemitted).symm
        have hidEq : lmodel.id = source.id := by
          have h1 : l.id = lmodel.id := by rw [heq]
          exact h1.symm.trans hid
        have hindex : lindex = index :=
          xc7f_caption_index_eq_of_id_eq hlabelNodes hsrcL hsrc hidEq
        rw [hindex] at hsrcL
        have hlmodel : lmodel = source := Option.some.inj (hsrcL.symm.trans hsrc)
        have hoS : inp.boxes.findIdx?
            (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex := by
          rw [← hlmodel]
          exact ho
        have hrect : l.rect = sceneCaptionRect execution.params inp o
            execution.lines execution.packedAcc ownerIndex source.owner := by
          rw [congrArg (fun s : SceneLabel => s.rect) heq]
          unfold sceneCaptionRect
          rw [hlmodel]
          rfl
        have hscope' : b.id ∉ res.scene.layoutDump.labelOwnerAnc
            (X_captionLabel exactIds execution ownerIndex source l.lines) := by
          have hown : (X_captionLabel exactIds execution ownerIndex source l.lines).owner =
              l.toLabel.owner := by
            simp only [X_captionLabel]
            have h2 : l.owner = source.owner := by
              rw [congrArg (fun s : SceneLabel => s.owner) heq]
              rw [hlmodel]
            rw [h2]
          rw [Elegant.Layered.labelOwnerAnc_congr_owner hown]
          exact hscope
        have hclr := hclearFit inp o res hfit execution index ownerIndex source l.lines b hsrc
          (by rw [hindex] at hm; exact hm) hoS hb hex hscope'
        rw [hrect]
        exact hclr

/-- Flat C7 for the exact pipeline under the fit premise: every successful
`layoutX` keeps every label clear of exclusive boxes outside the label's owner
scope, modulo the X branch, placement, and fit-conditioned caption residuals.
Replays `flatC7B_layoutX` with `hfit` threaded to the caption branch; the five
other premises close by the tracked proved facts. -/
theorem flatC7B_layoutX_fit (exactIds : List String)
    (hloop : X_RunLocalLoopSeparation exactIds)
    (hcapFit : X_CaptionScopeClearanceFit exactIds) :
    FlatC7B (layoutX exactIds) := by
  intro inp o res hwf hfp hfit hsep hseam1 hseam2 h
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hrunlocal : X_RunLocalLabelClearance exactIds inp o res :=
    X_runLocalLabelClearance_holds (inp := inp) (o := o) (res := res) hloop
      (x_runLocalForwardSeparation_holds exactIds)
      (x_runLocalReversedSeparation_holds exactIds)
  have hbelong : X_LabelBelongsToRun exactIds inp o res :=
    X_labelBelongsToRun (inp := inp) (o := o) (res := res) hwf x_routeLabelsPlaced_holds
  have hbox : X_ExclusiveBoxInLabelRun exactIds inp o res :=
    X_exclusiveBoxInLabelRun (inp := inp) (o := o) (res := res) hwf hfp
      (x_exclusiveRunNodeDecl_holds exactIds)
      (x_exclusiveKeyOutsideCgPaths_holds exactIds)
  have hbridges : X_RouteLabelDumpBridges exactIds inp o res :=
    X_routeLabelDumpBridges (inp := inp) (o := o) (res := res) hbelong hbox
  have hparts : X_PartsSeparated exactIds inp o res :=
    X_partsSeparated_holds (inp := inp) (o := o) (res := res)
  have hcaps : X_SceneCaptionBoxContainment exactIds inp o res :=
    xc7f_sceneCaptionBoxContainmentFit (inp := inp) (o := o) (res := res) hwf hfit hcapFit
  exact X_layout_c7 hwf hfp hparts ⟨hrunlocal, hbridges⟩ hcaps h

end PipelineImpl
end Layered
end Elegant

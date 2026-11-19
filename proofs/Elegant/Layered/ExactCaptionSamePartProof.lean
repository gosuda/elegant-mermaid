import Elegant.Layered.ExactCaptionFitFactsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact caption same-part leaves: descendant and owner scope.

Targets (fields of `ExactSeams`, `Kinds/UsecaseValidExact.lean`):
* `capDesc  : X_CaptionDescendantSamePartClear exactIds`
  (`ExactCaptionScopeProof.lean`): the scene caption rect of a non-exclusive
  owner misses the interior of every exclusive descendant box, for every
  same-part position tuple.
* `capOwnersW : X_OwnerScopeSamePartClearW exactIds`
  (`ExactCaptionFitFactsProof.lean`): the well-formed-local twin of
  `X_OwnerScopeSamePartClear`, with the local
  `WellFormed (inputModel inp o)` premise after the execution binder.

Truth status (probed 2026-11-19,
`proofs/wip/Probe/ExactCaptionSamePartTProbe.lean`, `layoutX []` recomputed
phases, vector profile): every executed row reports `meets=false`.
Rows: nest (descendant, installed title), flat (scope, installed title),
nodechild (node owner with exclusive child, fallback, descendant),
nolab (vacuous), self (self-loop), zero (zero-size fixed descendant),
deep (two nested labels), fixdesc (fixed group owner, fallback,
descendant). No falsifier found; both leaves are kept as stated.

Proof shape, one named sub-lemma residual per leaf:
* `capOwnersW` follows from the single residual `X_FallbackOwnerCasesX`
  (also the `fbCases` seam field) by the proved
  `x_ownerScopeSamePartClearW_holds`, discharging its node-border premise
  with the closed `x_ownerResNodeBorderZeroX_holds`. The cross-part half is
  closed inside `XCapScope_ownerScopeExclusiveClear_cross_part`.
* `capDesc` follows from the sibling installed-title leaf
  `X_CaptionTitleBranchClear` (the `capTitle` seam field) and the single
  residual `X_DescendantFallbackBandX` by the proved
  `x_captionDescendantSamePartClear_holds` (replayed below as the private
  skeleton `xcsp_desc_of_title_fall`). The two closed rewrites below
  discharge the fallback band's first steps: the caption rect under an
  absent installed title is the `ownedTextRect` fallback, and every scene
  box rect is the margin/orientation transport of its packed rect.
  The remaining run-level band (group caption reservation over
  `componentRunX`, packed transport, scene transport) stays open in
  `X_DescendantFallbackBandX`.
-/

/-- Scene caption rect under an absent installed title: the `find?` misses,
so the rect is the `ownedTextRect` fallback. Closed; discharges the first
rewrite of `X_DescendantFallbackBandX`. -/
theorem xcsp_sceneCaptionRect_of_titles_none {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {packed : Acc}
    {ownerIndex : Nat} {owner : String}
    (hnone : (sceneTitlesExpr P inp o lines packed).find?
      (fun title => title.1 == owner) = none) :
    sceneCaptionRect P inp o lines packed ownerIndex owner =
      ownedTextRect P
        ((sceneBoxesExpr P inp o packed).getD ownerIndex
          ⟨"", "", default, "", false⟩)
        (lines.getD ownerIndex []) := by
  unfold sceneCaptionRect
  rw [hnone]
  rfl

/-- Scene box rect transport: every executed scene box rect is the canvas
margin shift of the orientation transport of its packed rect. Closed public
projection of `sceneBox_source_rectX`; discharges the rect-value steps of
`X_DescendantFallbackBandX`. -/
theorem xcsp_sceneBox_rect_transport {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {bi : Nat} {b : Box} (hb : res.scene.boxes[bi]? = some b) :
    b.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD bi default)) := by
  obtain ⟨_, _, _, _, _, hrect⟩ := sceneBox_source_rectX execution hb
  exact hrect

/-- Well-formed-local owner-scope same-part clearance from its single
residual: the fallback-owner case split. The node-border premise is closed
by `x_ownerResNodeBorderZeroX_holds`; positions are disjoint by the closed
`XS_C8a_PositionsDisjoint_of_run` inside. -/
theorem xcapSamePart_ownerScopeW_of_cases (exactIds : List String)
    (hcases : X_FallbackOwnerCasesX exactIds) :
    X_OwnerScopeSamePartClearW exactIds :=
  x_ownerScopeSamePartClearW_holds exactIds hcases
    (x_ownerResNodeBorderZeroX_holds exactIds)

/-- Private skeleton: the descendant same-part clearance from the sibling
installed-title leaf and its single fallback-band residual. -/
private theorem xcsp_desc_of_title_fall (exactIds : List String)
    (htitle : X_CaptionTitleBranchClear exactIds)
    (hfall : X_DescendantFallbackBandX exactIds) :
    X_CaptionDescendantSamePartClear exactIds :=
  x_captionDescendantSamePartClear_holds exactIds htitle hfall

end PipelineImpl
end Layered
end Elegant

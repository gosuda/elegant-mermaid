import Elegant.Layered.ExactCaptionAncestorsLocalProof
import Elegant.Layered.ExactCaptionAncestorLinksProof
import Elegant.Layered.ExactCaptionMemberFactsProof
import Elegant.Layered.ExactCaptionMembersProof
import Elegant.Layered.ExactCaptionSelfProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact run-level caption clearance, per-execution form (`XF_CaptionRunClearXW`)

W replay of `XF_captionRunClearX_holds` (`ExactCaptionRunClearProof.lean:332`)
with local admission premises after the execution binder. The replayed
composition reads no run spec: each per-run fact comes from a W leaf
(`ExactCaptionAncestorsLocalProof`, `ExactCaptionMemberFactsProof`) or from a
premise-free leaf used as-is (`ExactCaptionSelfProof`,
`ExactCaptionMembersProof`). No global admission premise over all executions
appears anywhere in this file. Private helpers of
`ExactCaptionRunClearProof` are recopied with the `xrw_` prefix. -/

/-- `xrw_` copy of `xcap_strictInside_contained`
(`ExactCaptionRunClearProof.lean:234`): strict inside implies containment. -/
private theorem xrw_strictInside_contained {o i : Rect}
    (h : o.StrictInside i) : o.Contained i := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- `xrw_` copy of `xcap_selfClearX`
(`ExactCaptionRunClearProof.lean:243`): exact self strictness from its three
edges. -/
private theorem xrw_selfClearX {P : Params} {cg : Graph} {run : Run}
    {o : Options} {lines : List (List Measure.Line)} {comp : List Nat}
    {i : Nat} {stored0 : Rect} {tNode : Node}
    (hmem : (i, stored0) ∈ componentTitles P cg run)
    (hnode : cg.nodes[i]? = some tNode) (hborder : tNode.border = -2)
    (hside : CaptionSelfSidesStrict P cg run o lines comp)
    (htop : (frameRect P cg run i).y <
      (transportCaption P o lines comp i stored0).y)
    (hbot : CaptionSelfBottomStrict P cg run o lines comp) :
    (frameRect P cg run i).StrictInside
      (transportCaption P o lines comp i stored0) := by
  have hside' := hside i stored0 tNode hmem hnode hborder
  have hbot' := hbot i stored0 tNode hmem hnode hborder
  exact ⟨hside'.1, hside'.2, htop, hbot'⟩

/-- `xrw_` copy of `xcap_localPairX` (`ExactCaptionRunClearProof.lean:259`). -/
private theorem xrw_localPairX {P : Params} {cg : Graph} {run : Run}
    {o : Options} {lines : List (List Measure.Line)} {comp : List Nat}
    (hside : CaptionSelfSidesStrict P cg run o lines comp)
    (hbot : CaptionSelfBottomStrict P cg run o lines comp)
    (htop : ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
      (i, stored0) ∈ componentTitles P cg run →
      cg.nodes[i]? = some tNode → tNode.border = -2 →
      (frameRect P cg run i).y <
        (transportCaption P o lines comp i stored0).y)
    (hmark : CaptionSameDeclMarkerDisjoint P cg run o lines comp)
    (hmemdesc : CaptionMemberDescDisjoint P cg run o lines comp)
    (hplain : ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
      (i, stored0) ∈ componentTitles P cg run →
      cg.nodes[i]? = some tNode → tNode.border = -2 →
      ∀ (pos : Nat) (fNode : Node) (g0 : Rect),
        cg.nodes[pos]? = some fNode →
        tNode.decl ≠ fNode.decl →
        fNode.border = 0 →
        fNode.clusterPath.contains tNode.decl = true →
        frameRect P cg run pos = g0 →
        Disjoint g0 (transportCaption P o lines comp i stored0))
    (hnest : CaptionAncestorGroupFrameStrict P cg run)
    (hmarkAnc : CaptionAncestorMarkerClear P cg run o lines comp)
    (hotherAnc : CaptionAncestorOtherClear P cg run o lines comp) :
    (∀ (i : Nat) (stored0 : Rect) (tNode : Node),
      (i, stored0) ∈ componentTitles P cg run →
      cg.nodes[i]? = some tNode →
      tNode.border = -2 →
      (frameRect P cg run i).StrictInside
        (transportCaption P o lines comp i stored0)) ∧
    (∀ (i : Nat) (stored0 : Rect) (tNode : Node),
      (i, stored0) ∈ componentTitles P cg run →
      cg.nodes[i]? = some tNode →
      tNode.border = -2 →
      ∀ (pos : Nat) (fNode : Node) (g0 : Rect),
        cg.nodes[pos]? = some fNode →
        (tNode.decl = fNode.decl ∨
          fNode.clusterPath.contains tNode.decl = true ∨
          tNode.clusterPath.contains fNode.decl = true) →
        frameRect P cg run pos = g0 →
        Disjoint g0 (transportCaption P o lines comp i stored0) ∨
        g0.StrictInside (transportCaption P o lines comp i stored0)) := by
  constructor
  · intro i stored0 tNode hmem hnode hborder
    exact xrw_selfClearX hmem hnode hborder hside
      (htop i stored0 tNode hmem hnode hborder) hbot
  · intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hrel
    intro hframe
    have hself := xrw_selfClearX hmem hnode hborder hside
      (htop i stored0 tNode hmem hnode hborder) hbot
    rcases hrel with hsame | hft | htf
    · exact captionSameDeclClear_executed hself hmark hmem hnode hborder hfn hsame hframe
    · by_cases hne : tNode.decl = fNode.decl
      · exact captionSameDeclClear_executed hself hmark hmem hnode hborder hfn hne hframe
      · by_cases hplainB : fNode.border = 0
        · exact Or.inl (hplain i stored0 tNode hmem hnode hborder pos fNode g0
            hfn hne hplainB hft hframe)
        · exact captionMemberDescClear_executed hmemdesc hmem hnode hborder hfn hne
            hft hplainB hframe
    · by_cases hne : tNode.decl = fNode.decl
      · exact captionSameDeclClear_executed hself hmark hmem hnode hborder hfn hne hframe
      · by_cases hftB : fNode.clusterPath.contains tNode.decl = true
        · by_cases hplainB : fNode.border = 0
          · exact Or.inl (hplain i stored0 tNode hmem hnode hborder pos fNode g0
              hfn hne hplainB hftB hframe)
          · exact captionMemberDescClear_executed hmemdesc hmem hnode hborder hfn hne
              hftB hplainB hframe
        · exact captionAncestorClear_executed hself hnest hmarkAnc hotherAnc hmem
            hnode hborder hfn hne htf hframe

/-- Per-execution form of `XF_CaptionRunClearX`
(`ExactPartFrameCoresProof.lean:74`): the same run-level caption clearance
with local admission premises directly after the execution binder. No
`InputFixedFit` premise: the original conclusion is not fit-conditioned. -/
def XF_CaptionRunClearXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionRunClear execution.params
      (componentCandidate execution.graph comp candidate) run
      (transportCapSize execution.params o execution.lines comp)

/-- Per-execution run-level caption clearance from narrow residuals only:
replay of `XF_captionRunClearX_holds` over the W leaves
(`XC_ancestorGroupFrameXW_holds`, `XC_ancestorMarkerXW_holds`,
`XC_ancestorOtherXW_holds`, `XC_foreignSpansXW_holds`,
`XC_memberDescXW_holds`) and the premise-free leaves used as-is
(`XC_selfSidesX_holds`, `XC_selfBottomX_holds`, `XC_selfTopX_holds`,
`XC_sameDeclMarkerX_holds`, `XC_plainMemberX_holds`). -/
theorem XF_captionRunClearXW_holds (exactIds : List String)
    (hsideLeft : XC_SelfSidesLeftNarrowX exactIds)
    (hsideRight : XC_SelfSidesRightNarrowX exactIds)
    (hbotHeight : XC_SelfBottomHeightNarrowX exactIds)
    (hcap : XC_CapBandX exactIds)
    (hlink : XCA_GroupLinkX exactIds)
    (hbelow : XCA_MarkerBelowX exactIds)
    (himpossible : XCA_PlainAncestorImpossibleX exactIds)
    (hspans : XB_ForeignClusterRankSpans exactIds)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (halignB : XB_ForeignBorderChainXAligned exactIds)
    (hord : XB_OrderedIntervals exactIds)
    (htopNN : XB_TopNonneg exactIds)
    (hmemNE : XB_MemberNonempty exactIds)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplainXN : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds) :
    XF_CaptionRunClearXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  have hside : XC_SelfSidesX exactIds :=
    XC_selfSidesX_holds exactIds hsideLeft hsideRight
  have hbot : XC_SelfBottomX exactIds :=
    XC_selfBottomX_holds exactIds hbotHeight
  have htopT : XC_SelfTopX exactIds := XC_selfTopX_holds exactIds
  have hmark : XC_SameDeclMarkerX exactIds :=
    XC_sameDeclMarkerX_holds exactIds hcap
  have hmemdescW : XC_MemberDescXW exactIds :=
    XC_memberDescXW_holds exactIds hcap
  have hplainM : XC_PlainMemberX exactIds :=
    XC_plainMemberX_holds exactIds hcap
  have hnestW : XC_AncestorGroupFrameXW exactIds :=
    XC_ancestorGroupFrameXW_holds exactIds hlink
  have hmarkAncW : XC_AncestorMarkerXW exactIds :=
    XC_ancestorMarkerXW_holds exactIds hbelow
  have hotherAncW : XC_AncestorOtherXW exactIds :=
    XC_ancestorOtherXW_holds exactIds himpossible
  have hclearW : XC_ForeignSpansXW exactIds :=
    XC_foreignSpansXW_holds exactIds hspans horder halignB hord
      htopNN hmemNE hbracket hplainXN halignN
  have hsideR := hside execution hcomp hrun
  have hbotR := hbot execution hcomp hrun
  have htopR := htopT execution hcomp hrun
  have hmarkR := hmark execution hcomp hrun
  have hmemdescR := hmemdescW execution hwf hfp hcomp hrun
  have hplainR := hplainM execution hcomp hrun
  have hnestR := hnestW execution hwf hfp hcomp hrun
  have hmarkAncR := hmarkAncW execution hwf hfp hcomp hrun
  have hotherAncR := hotherAncW execution hwf hfp hcomp hrun
  have hclearR := hclearW execution hwf hfp hcomp hrun
  have hpair := xrw_localPairX hsideR hbotR htopR hmarkR hmemdescR hplainR
    hnestR hmarkAncR hotherAncR
  unfold CaptionRunClear
  intro i stored0 tNode hmem hnode hborder pos g0 hpos hframe
  cases hfn : (componentCandidate execution.graph comp candidate).nodes[pos]? with
  | none =>
    rw [List.getElem?_eq_none_iff] at hfn
    omega
  | some fNode =>
    by_cases hrel : tNode.decl = fNode.decl ∨
        fNode.clusterPath.contains tNode.decl = true ∨
        tNode.clusterPath.contains fNode.decl = true
    · exact hpair.2 i stored0 tNode hmem hnode hborder pos fNode g0 hfn hrel hframe
    · have hne : tNode.decl ≠ fNode.decl := fun h => hrel (Or.inl h)
      have hpathW : fNode.clusterPath.contains tNode.decl = false := by
        cases hc : fNode.clusterPath.contains tNode.decl with
        | true => exact absurd (Or.inr (Or.inl hc)) hrel
        | false => rfl
      have hpathU : tNode.clusterPath.contains fNode.decl = false := by
        cases hc : tNode.clusterPath.contains fNode.decl with
        | true => exact absurd (Or.inr (Or.inr hc)) hrel
        | false => rfl
      have hdisj := hclearR i pos tNode fNode hnode hfn hborder hne hpathW hpathU
      have hself := hpair.1 i stored0 tNode hmem hnode hborder
      have hcont := xrw_strictInside_contained hself
      rw [hframe] at hdisj
      exact Or.inl ((Disjoint.comm _ _).mp (disjoint_of_sub_disjoint hcont hdisj))

/-- Per-execution run-level caption clearance from the W-link residual:
W-link variant of `XF_captionRunClearXW_holds`, replaying the same
composition with `XC_ancestorGroupFrameXW_of_linkW`. -/
theorem XF_captionRunClearXW_of_linkW (exactIds : List String)
    (hsideLeft : XC_SelfSidesLeftNarrowX exactIds)
    (hsideRight : XC_SelfSidesRightNarrowX exactIds)
    (hbotHeight : XC_SelfBottomHeightNarrowX exactIds)
    (hcap : XC_CapBandX exactIds)
    (hlinkW : XCA_GroupLinkXW exactIds)
    (hbelow : XCA_MarkerBelowX exactIds)
    (himpossible : XCA_PlainAncestorImpossibleX exactIds)
    (hspans : XB_ForeignClusterRankSpans exactIds)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (halignB : XB_ForeignBorderChainXAligned exactIds)
    (hord : XB_OrderedIntervals exactIds)
    (htopNN : XB_TopNonneg exactIds)
    (hmemNE : XB_MemberNonempty exactIds)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplainXN : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds) :
    XF_CaptionRunClearXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  have hside : XC_SelfSidesX exactIds :=
    XC_selfSidesX_holds exactIds hsideLeft hsideRight
  have hbot : XC_SelfBottomX exactIds :=
    XC_selfBottomX_holds exactIds hbotHeight
  have htopT : XC_SelfTopX exactIds := XC_selfTopX_holds exactIds
  have hmark : XC_SameDeclMarkerX exactIds :=
    XC_sameDeclMarkerX_holds exactIds hcap
  have hmemdescW : XC_MemberDescXW exactIds :=
    XC_memberDescXW_holds exactIds hcap
  have hplainM : XC_PlainMemberX exactIds :=
    XC_plainMemberX_holds exactIds hcap
  have hnestW : XC_AncestorGroupFrameXW exactIds :=
    XC_ancestorGroupFrameXW_of_linkW exactIds hlinkW
  have hmarkAncW : XC_AncestorMarkerXW exactIds :=
    XC_ancestorMarkerXW_holds exactIds hbelow
  have hotherAncW : XC_AncestorOtherXW exactIds :=
    XC_ancestorOtherXW_holds exactIds himpossible
  have hclearW : XC_ForeignSpansXW exactIds :=
    XC_foreignSpansXW_holds exactIds hspans horder halignB hord
      htopNN hmemNE hbracket hplainXN halignN
  have hsideR := hside execution hcomp hrun
  have hbotR := hbot execution hcomp hrun
  have htopR := htopT execution hcomp hrun
  have hmarkR := hmark execution hcomp hrun
  have hmemdescR := hmemdescW execution hwf hfp hcomp hrun
  have hplainR := hplainM execution hcomp hrun
  have hnestR := hnestW execution hwf hfp hcomp hrun
  have hmarkAncR := hmarkAncW execution hwf hfp hcomp hrun
  have hotherAncR := hotherAncW execution hwf hfp hcomp hrun
  have hclearR := hclearW execution hwf hfp hcomp hrun
  have hpair := xrw_localPairX hsideR hbotR htopR hmarkR hmemdescR hplainR
    hnestR hmarkAncR hotherAncR
  unfold CaptionRunClear
  intro i stored0 tNode hmem hnode hborder pos g0 hpos hframe
  cases hfn : (componentCandidate execution.graph comp candidate).nodes[pos]? with
  | none =>
    rw [List.getElem?_eq_none_iff] at hfn
    omega
  | some fNode =>
    by_cases hrel : tNode.decl = fNode.decl ∨
        fNode.clusterPath.contains tNode.decl = true ∨
        tNode.clusterPath.contains fNode.decl = true
    · exact hpair.2 i stored0 tNode hmem hnode hborder pos fNode g0 hfn hrel hframe
    · have hne : tNode.decl ≠ fNode.decl := fun h => hrel (Or.inl h)
      have hpathW : fNode.clusterPath.contains tNode.decl = false := by
        cases hc : fNode.clusterPath.contains tNode.decl with
        | true => exact absurd (Or.inr (Or.inl hc)) hrel
        | false => rfl
      have hpathU : tNode.clusterPath.contains fNode.decl = false := by
        cases hc : tNode.clusterPath.contains fNode.decl with
        | true => exact absurd (Or.inr (Or.inr hc)) hrel
        | false => rfl
      have hdisj := hclearR i pos tNode fNode hnode hfn hborder hne hpathW hpathU
      have hself := hpair.1 i stored0 tNode hmem hnode hborder
      have hcont := xrw_strictInside_contained hself
      rw [hframe] at hdisj
      exact Or.inl ((Disjoint.comm _ _).mp (disjoint_of_sub_disjoint hcont hdisj))

end PipelineImpl

end Layered
end Elegant

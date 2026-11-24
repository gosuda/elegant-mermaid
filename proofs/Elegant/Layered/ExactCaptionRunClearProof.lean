import Elegant.Layered.ExactPartFrameCoresProof
import Elegant.Layered.CaptionLocalClearProof
import Elegant.Layered.PartCaptionRunClearProof
import Elegant.Layered.PartFrameCoresProof
import Elegant.Layered.ForeignFrameClearance

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact run-level caption clearance (`XF_CaptionRunClearX`)

Target: `XF_captionRunClearX_holds`, the exact-pipeline replay of
`captionHalf_closed` (`CaptionRunClearClosed.lean:351`), which itself restates
`captionRunClear_closed` (`CaptionRunClearClosed.lean:303`) in the part-level
consumer's measured-only form.

Plain proof shape (reused outright here, run-generic): `captionRunClear_closed`
discharges the seven per-run hypotheses of `captionRunClear_executed`, then
`captionLocalClear_executed` splits related positions by declaration
containment and `captionRunClear_executed` sends unrelated positions through
the foreign-span seam. The three composition bridges
(`captionSameDeclClear_executed`, `captionMemberDescClear_executed`,
`captionAncestorClear_executed`), the nesting transitivity
(`captionStrictInside_trans`), the containment step
(`disjoint_of_sub_disjoint`), and the final unrelated-case split never read
the run spec, so they apply verbatim to exact runs.

Plain lemmas on the path that read the plain run spec
(`componentRun_spec` conjuncts `rankCoordsWith`/`proxyYs`), with the exact
replacement each residual's future discharge uses:

* `captionSelfSidesStrict_executed` (x-interval only): the title-copy/side-marker
  separation survives the size hook, which leaves border markers and title
  copies alone (`sizeProperPortsX` guard, `ExactPipeline.lean:55`; key fields
  via `sizeProperPortsX_key`, `ExactFlatFacts.lean:264`) and the x-interval by
  `X_ForeignBorderChainXAligned` (`ExactFlatC7CaptionScope.lean:58`).
  Residual: `XC_SelfSidesX`.
* `captionSelfTop` (placement source): candidate placement source transported
  across `exactGraph` (`exactGraph_node_key`, `ExactFlatFacts.lean:158`).
  Residual: `XC_SelfTopX`.
* `captionSelfBottom_proved` (rank bands): whole-rank shifts preserve in-band
  inclusion (`X_ReserveBands_holds`, `ExactFlatC2.lean:955`; pre-reserve bands
  `X_pre_band`, `ExactFlatC2.lean:668`; final bands `componentRunX_node_band`,
  `ComponentRunGenGeometry.lean:626`). Residual: `XC_SelfBottomX`.
* `captionSameDeclMarkerDisjoint_executed` (title-vs-bottom-marker gap):
  same band lemmas via `componentRunX_spec` (`ExactFlatFacts.lean:284`).
  Residual: `XC_SameDeclMarkerX`.
* `captionPlainMemberClear_proved` (member band lower bound via
  `fbs_run_node_band`, `rankAxis_band_top_strict`, `proxyYs_getD`): pre-reserve
  plus reserved bands and sibling disjointness (`componentRunX_positions_disjoint`,
  `ComponentRunGenGeometry.lean:527`). Residual: `XC_PlainMemberX`.
* `captionMemberDescDisjoint_executed` (descendant rank chain): same band
  lemmas plus `ExactPartBounded` title/record facts. Residual: `XC_MemberDescX`.
* `captionAncestorGroupFrameStrict_executed` (transitive ancestor nesting):
  `X_ReserveBands_holds` plus `componentRunX_node_band`.
  Residual: `XC_AncestorGroupFrameX`.
* `captionAncestorMarkerClear_executed` (ancestor bottom-marker band below
  caption): `X_ReserveBands_holds` plus `componentRunX_positions_disjoint`.
  Residual: `XC_AncestorMarkerX`.
* `captionAncestorOtherClear_executed` (vacuous over candidate shapes):
  candidate marker shape transported across `exactGraph`
  (`X_componentCandidate_marker_shape`, `ExactFlatC5Rank.lean:332`, via
  `exactGraph_node_key`). Residual: `XC_AncestorOtherX`.
* `foreignSpansClear_of_run` (measured graph plus `componentRun`): exact twin
  from `XB_foreignBorderSpansSeparated_holds` (`ExactForeignBorderSpansProof`)
  and `XN_foreignNonGroupSpansClear_holds` (`ExactForeignNonGroupSpansProof`)
  under `X_ForeignBorderChainXAligned` (per-run form `X_C8a_ForeignSpansAll`,
  `ExactFlatC8a.lean:232`). Residual: `XC_ForeignSpansX`.

Each residual below is a single fact strictly narrower than the goal (one
edge, one declaration case, or one span clause). Probe:
`proofs/wip/Probe/ExactCaptionRunClearTProbe.lean` evaluates every residual
on flat, nested, sane fixed, and wider-than-slot fixed inputs. -/

/-- Exact self-sides residual: horizontal half of self strictness over one
exact run. Plain original: `CaptionSelfSidesStrict`
(`CaptionLocalClearProof.lean:73`). -/
def XC_SelfSidesX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionSelfSidesStrict execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp

/-- Exact self-bottom residual: bottom-edge half of self strictness over one
exact run. Plain original: `CaptionSelfBottomStrict`
(`CaptionLocalClearProof.lean:88`). -/
def XC_SelfBottomX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionSelfBottomStrict execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp

/-- Exact self-top residual: the caption starts strictly below its own frame
top over one exact run. Plain original: the conclusion of `captionSelfTop`
(`PartCaptionRunClearProof.lean:209`). -/
def XC_SelfTopX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
      (i, stored0) ∈ componentTitles execution.params
        (componentCandidate execution.graph comp candidate) run →
      (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode →
      tNode.border = -2 →
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run i).y <
        (transportCaption execution.params o execution.lines comp i stored0).y

/-- Exact same-declaration marker residual over one exact run. Plain original:
`CaptionSameDeclMarkerDisjoint` (`CaptionLocalClearProof.lean:102`). -/
def XC_SameDeclMarkerX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionSameDeclMarkerDisjoint execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp

/-- Exact descendant residual over one exact run. Plain original:
`CaptionMemberDescDisjoint` (`CaptionLocalClearProof.lean:120`). -/
def XC_MemberDescX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionMemberDescDisjoint execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp

/-- Exact plain-member residual over one exact run: a plain member on the
title's cluster path is disjoint from the transported caption. Plain original:
the conclusion of `captionPlainMemberClear_proved`
(`CaptionLocalClearProof.lean:480`). -/
def XC_PlainMemberX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
      (i, stored0) ∈ componentTitles execution.params
        (componentCandidate execution.graph comp candidate) run →
      (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode →
      tNode.border = -2 →
      ∀ (pos : Nat) (fNode : Node) (g0 : Rect),
        (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode →
        tNode.decl ≠ fNode.decl →
        fNode.border = 0 →
        fNode.clusterPath.contains tNode.decl = true →
        frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos = g0 →
        Disjoint g0
          (transportCaption execution.params o execution.lines comp i stored0)

/-- Exact ancestor-group-frame residual over one exact run. Plain original:
`CaptionAncestorGroupFrameStrict` (`CaptionLocalClearProof.lean:143`). -/
def XC_AncestorGroupFrameX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionAncestorGroupFrameStrict execution.params
      (componentCandidate execution.graph comp candidate) run

/-- Exact ancestor-marker residual over one exact run. Plain original:
`CaptionAncestorMarkerClear` (`CaptionLocalClearProof.lean:159`). -/
def XC_AncestorMarkerX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionAncestorMarkerClear execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp

/-- Exact ancestor-other residual over one exact run. Plain original:
`CaptionAncestorOtherClear` (`CaptionLocalClearProof.lean:180`). -/
def XC_AncestorOtherX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionAncestorOtherClear execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp

/-- Exact foreign-span residual over one exact run. Plain original:
`ForeignSpansClear` (`ForeignFrameClearance.lean:48`); per-run exact form
mirrors `X_C8a_ForeignSpansAll` (`ExactFlatC8a.lean:232`). -/
def XC_ForeignSpansX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ForeignSpansClear execution.params
      (componentCandidate execution.graph comp candidate) run

/-- Copy of the local `strictInside_contained`: strict inside implies
containment. -/
private theorem xcap_strictInside_contained {o i : Rect}
    (h : o.StrictInside i) : o.Contained i := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- Exact self strictness from its three edges: copy of
`captionSelfClear_executed` with the top and bottom edges as premises. -/
private theorem xcap_selfClearX {P : Params} {cg : Graph} {run : Run}
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

/-- Exact local pair from the narrow residuals: copy of
`captionLocalClear_executed` with every run-spec lemma replaced by its
residual premise. -/
private theorem xcap_localPairX {P : Params} {cg : Graph} {run : Run}
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
    exact xcap_selfClearX hmem hnode hborder hside
      (htop i stored0 tNode hmem hnode hborder) hbot
  · intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hrel
    intro hframe
    have hself := xcap_selfClearX hmem hnode hborder hside
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

/-- Exact closed run-level caption clearance: replay of `captionHalf_closed`
over `componentRunX`. Every per-run hypothesis is one of the narrow exact
residuals above; the composition itself reads no run spec. -/
theorem XF_captionRunClearX_holds (exactIds : List String)
    (hside : XC_SelfSidesX exactIds)
    (hbot : XC_SelfBottomX exactIds)
    (htop : XC_SelfTopX exactIds)
    (hmark : XC_SameDeclMarkerX exactIds)
    (hmemdesc : XC_MemberDescX exactIds)
    (hplain : XC_PlainMemberX exactIds)
    (hnest : XC_AncestorGroupFrameX exactIds)
    (hmarkAnc : XC_AncestorMarkerX exactIds)
    (hotherAnc : XC_AncestorOtherX exactIds)
    (hclear : XC_ForeignSpansX exactIds) :
    XF_CaptionRunClearX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  have hsideR := hside execution hcomp hrun
  have hbotR := hbot execution hcomp hrun
  have htopR := htop execution hcomp hrun
  have hmarkR := hmark execution hcomp hrun
  have hmemdescR := hmemdesc execution hcomp hrun
  have hplainR := hplain execution hcomp hrun
  have hnestR := hnest execution hcomp hrun
  have hmarkAncR := hmarkAnc execution hcomp hrun
  have hotherAncR := hotherAnc execution hcomp hrun
  have hclearR := hclear execution hcomp hrun
  have hpair := xcap_localPairX hsideR hbotR htopR hmarkR hmemdescR hplainR
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
      have hcont := xcap_strictInside_contained hself
      rw [hframe] at hdisj
      exact Or.inl ((Disjoint.comm _ _).mp (disjoint_of_sub_disjoint hcont hdisj))

end PipelineImpl
end Layered
end Elegant

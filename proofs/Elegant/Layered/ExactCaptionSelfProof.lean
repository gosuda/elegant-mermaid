import Elegant.Layered.ExactCaptionRunClearProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Stored title y equals its own frame y plus `clusterPad`, from the
definition of `componentTitles` alone (no run spec). -/
theorem componentTitles_y_eq_frame {P : Params} {cg : Graph} {run : Run}
    {i : Nat} {stored0 : Rect}
    (hmem : (i, stored0) ∈ componentTitles P cg run) :
    stored0.y = (frameRect P cg run i).y + P.clusterPad := by
  unfold componentTitles at hmem
  obtain ⟨top, htopMem, htopEmit⟩ := List.mem_filterMap.mp hmem
  dsimp only at htopEmit
  by_cases hb : top.1.border = -2
  · simp [hb] at htopEmit
    cases hfind : run.proper.nodes.zipIdx.find?
        (fun q => q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
    | none =>
      simp [hfind] at htopEmit
    | some title =>
      simp [hfind] at htopEmit
      obtain ⟨hi, hrect⟩ := htopEmit
      have hy : stored0.y = (frameRect P cg run top.2).y + P.clusterPad := by
        have hcongr : (Rect.mk
          (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
          ((frameRect P cg run top.2).y + P.clusterPad) top.1.w
          (top.1.h - P.clusterPad)).y = stored0.y := congrArg Rect.y hrect
        simpa using hcongr.symm
      rw [hi] at hy
      exact hy
  · simp [hb] at htopEmit

/-- Exact self-top: the caption starts strictly below its own frame top.
Proved outright: the stored title y is `frame.y + clusterPad` by
`componentTitles_y_eq_frame`, the transported caption keeps that y, and `clusterPad`
is positive from `execution.checked`. Plain original: `captionSelfTop`. -/
theorem XC_selfTopX_holds (exactIds : List String) : XC_SelfTopX exactIds := by
  intro inp o res execution comp _hmem candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder
  have hpad : 0 < execution.params.clusterPad :=
    checkedParams_clusterPad_pos execution.checked
  have hy := componentTitles_y_eq_frame (P := execution.params) hmem
  have htrans : (transportCaption execution.params o execution.lines comp i stored0).y =
      stored0.y := rfl
  omega

/-- Narrow left half of exact self-sides: one of the two `StrictInside`
x-inequalities. Strictly narrower than `XC_SelfSidesX`; single geometric
fact. Plain path: title-copy/left-marker separation. -/
def XC_SelfSidesLeftNarrowX (exactIds : List String) : Prop :=
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
        (componentCandidate execution.graph comp candidate) run i).x <
        (transportCaption execution.params o execution.lines comp i stored0).x

/-- Narrow right half of exact self-sides: one of the two `StrictInside`
x-inequalities. Strictly narrower than `XC_SelfSidesX`; single geometric
fact. Plain path: title-copy/right-marker separation. -/
def XC_SelfSidesRightNarrowX (exactIds : List String) : Prop :=
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
      (transportCaption execution.params o execution.lines comp i stored0).x +
        (transportCaption execution.params o execution.lines comp i stored0).w <
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run i).x +
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run i).w

/-- Narrow height form of exact self-bottom: the padded measured caption
height fits in its own frame height. No titles, no transported rect, no
y-positions; single inequality. With the definitional stored-title y
(`componentTitles_y_eq_frame`) it gives `XC_SelfBottomX`. Plain path: title-band
bottom strictly above the bottom-marker rank. -/
def XC_SelfBottomHeightNarrowX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ (i : Nat) (tNode : Node),
      (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode →
      tNode.border = -2 →
      execution.params.clusterPad +
        (transportCapSize execution.params o execution.lines comp i).2 <
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run i).h

/-- Exact self-sides from its two narrow halves: replay of the plain
`captionSelfSidesStrict_executed` combination step. -/
theorem XC_selfSidesX_holds (exactIds : List String)
    (hl : XC_SelfSidesLeftNarrowX exactIds)
    (hr : XC_SelfSidesRightNarrowX exactIds) :
    XC_SelfSidesX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder
  exact ⟨hl execution hcomp hrun i stored0 tNode hmem hnode hborder,
    hr execution hcomp hrun i stored0 tNode hmem hnode hborder⟩

/-- Exact self-bottom from its narrow height form plus the definitional
stored-title y. Replay of the plain `captionSelfBottom_proved` combination
step (`captionInTopBand_executed` upper bound plus rank-band strictness,
here as the single height inequality). -/
theorem XC_selfBottomX_holds (exactIds : List String)
    (hh : XC_SelfBottomHeightNarrowX exactIds) :
    XC_SelfBottomX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder
  have hy := componentTitles_y_eq_frame (P := execution.params) hmem
  have hheight := hh execution hcomp hrun i tNode hnode hborder
  have hty : (transportCaption execution.params o execution.lines comp i stored0).y =
      stored0.y := rfl
  have hth : (transportCaption execution.params o execution.lines comp i stored0).h =
      (transportCapSize execution.params o execution.lines comp i).2 := rfl
  omega

end PipelineImpl
end Layered
end Elegant

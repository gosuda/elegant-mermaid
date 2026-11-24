import Elegant.Layered.LoopFootprintBeyondProperProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Single stage-level residual (file-unique name `TopSliverRightGapBt`): for a
group-top `v` (border `-2`) with nonempty loops, every sliver frame `b` that is
nondegenerate, y-overlapping the footprint, and not left of it lies right of
the footprint. Strictly narrower than `TopLoopsSliverResidual`: it is silent
about degenerate frames, y-separated frames, and frames left of the footprint,
and its consequent is one placed-`x` inequality. The alignment premise carries
the accepted open seam `hx` into the fact. Probe
`proofs/wip/Probe/BeyondTopSliverTProbe.lean` checks the exact consequent on
executed runs with labeled wide loops and a foreign titled group right of the
looping group: 48 firings, zero violations, zero separation violations. -/
def TopSliverRightGapBt (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions) (v b : Nat),
    comp ∈ components e.graph →
    componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run →
    v < (componentCandidate e.graph comp candidate).nodes.length →
    (componentCandidate e.graph comp candidate).nodes.length ≤ b →
    b < run.proper.nodes.length →
    ((componentCandidate e.graph comp candidate).nodes.getD v default).border = -2 →
    loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
      (componentCandidate e.graph comp candidate).slot ≠ [] →
    SideMarkerSpanAligned →
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≠ 0 →
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).h ≠ 0 →
    (frameRect default (componentCandidate e.graph comp candidate) run b).w ≠ 0 →
    (frameRect default (componentCandidate e.graph comp candidate) run b).h ≠ 0 →
    ¬((loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).y +
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).h ≤
        (frameRect default (componentCandidate e.graph comp candidate) run b).y) →
    ¬((frameRect default (componentCandidate e.graph comp candidate) run b).y +
        (frameRect default (componentCandidate e.graph comp candidate) run b).h ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).y) →
    ¬((frameRect default (componentCandidate e.graph comp candidate) run b).x +
        (frameRect default (componentCandidate e.graph comp candidate) run b).w ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x) →
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x +
      (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≤
      (frameRect default (componentCandidate e.graph comp candidate) run b).x

/-- A zero-width footprint is disjoint from every frame. -/
private theorem bttop_sep_of_foot_width {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hw : (loopFootprint cg run labels v).w = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  omega

/-- A zero-height footprint is disjoint from every frame. -/
private theorem bttop_sep_of_foot_height {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hh : (loopFootprint cg run labels v).h = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨-, hy⟩
  omega

/-- A zero-width frame is disjoint from every loop footprint. -/
private theorem bttop_sep_of_frame_width {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hw : (frameRect default cg run b).w = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  omega

/-- A zero-height frame is disjoint from every loop footprint. -/
private theorem bttop_sep_of_frame_height {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hh : (frameRect default cg run b).h = 0) :
    LoopFootprintSeparation cg run labels v b := by
  unfold LoopFootprintSeparation Disjoint Rect.meetsInterior
  rintro ⟨-, hy⟩
  omega

/-- Main theorem: the footprint of a group-top self-loop separates from every
sliver frame, modulo the accepted open seam `hx` (genuinely used: converted to
the executed alignment and fed to the gap residual) and the single placement
x-gap residual above. Degenerate, y-separated, and left-positioned slivers
close directly; the remainder is exactly the residual. -/
theorem topLoopsSliverResidual_holds
    (hx : ForeignBorderChainXAligned)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hgap : TopSliverRightGapBt inp o res) :
    TopLoopsSliverResidual inp o res := by
  intro e comp candidate run orderOptions v b hcomp hrun hv hle hlt htop hne
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  by_cases hwfp : (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).w = 0
  · exact bttop_sep_of_foot_width hwfp
  by_cases hhfp : (loopFootprint (componentCandidate e.graph comp candidate) run
      e.measured v).h = 0
  · exact bttop_sep_of_foot_height hhfp
  by_cases hwfr : (frameRect default (componentCandidate e.graph comp candidate) run b).w = 0
  · exact bttop_sep_of_frame_width hwfr
  by_cases hhfr : (frameRect default (componentCandidate e.graph comp candidate) run b).h = 0
  · exact bttop_sep_of_frame_height hhfr
  by_cases hys : (loopFootprint (componentCandidate e.graph comp candidate) run
        e.measured v).y +
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).h ≤
        (frameRect default (componentCandidate e.graph comp candidate) run b).y ∨
      (frameRect default (componentCandidate e.graph comp candidate) run b).y +
        (frameRect default (componentCandidate e.graph comp candidate) run b).h ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).y
  · unfold LoopFootprintSeparation
    exact rect_disjoint_of_y hys
  · by_cases hleft : (frameRect default (componentCandidate e.graph comp candidate) run b).x +
        (frameRect default (componentCandidate e.graph comp candidate) run b).w ≤
        (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x
    · unfold LoopFootprintSeparation
      exact rect_disjoint_of_x (Or.inr hleft)
    · unfold LoopFootprintSeparation
      refine rect_disjoint_of_x (Or.inl ?_)
      simp only [not_or] at hys
      obtain ⟨hys1, hys2⟩ := hys
      exact hgap e comp candidate run orderOptions v b hcomp hrun hv hle hlt
        htop hne halign hwfp hhfp hwfr hhfr hys1 hys2 hleft

end PipelineImpl
end Layered
end Elegant

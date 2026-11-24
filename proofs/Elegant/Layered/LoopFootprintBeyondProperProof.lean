import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.FlatC6LoopProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Prefixed copy of the private `extent_empty` in `LoopFootprintResidualProof`:
the loop extent of an empty size list is zero. -/
private theorem beyond_extent_empty (slot : Int) : Loops.extent slot [] = 0 := by
  simp [Loops.extent]

/-- Prefixed copy of the private `sep_of_empty_loops` in
`LoopFootprintResidualProof`: with an empty loop-size list the footprint has
zero width, so it meets no frame interior. -/
private theorem beyond_sep_of_empty_loops {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v b : Nat}
    (hempty : loopSizes cg.edges labels v cg.slot = [])
    (hexact : run.exact = []) :
    LoopFootprintSeparation cg run labels v b := by
  have hcon : run.exact.contains v = false := by simp [hexact]
  have hext : (if run.exact.contains v then Loops.exactExtent else Loops.extent)
      cg.slot (loopSizes cg.edges labels v cg.slot) = 0 := by
    have h1 : (if run.exact.contains v then Loops.exactExtent else Loops.extent) =
        Loops.extent := by simp only [hcon, Bool.false_eq_true, ↓reduceIte]
    rw [h1, hempty]
    exact beyond_extent_empty _
  unfold LoopFootprintSeparation loopFootprint
  rw [hext]
  unfold Disjoint Rect.meetsInterior
  rintro ⟨hx, -⟩
  dsimp only at hx
  omega

/-- Narrow residual (plain owner): the footprint of an in-range plain
(`border = 0`) candidate node separates from every sliver frame
(`cgLen ≤ b < properLen`). Strictly narrower than `LoopFootprintBeyondProper`
by the added `border = 0` premise. Probe census over all executed runs and
all six orderings shows zero violations for every plain-vs-sliver pair. -/
def PlainSliverResidual (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions) (v b : Nat),
    comp ∈ components e.graph →
    componentRun e.params (componentCandidate e.graph comp candidate) e.measured
      orderOptions = .ok run →
    v < (componentCandidate e.graph comp candidate).nodes.length →
    (componentCandidate e.graph comp candidate).nodes.length ≤ b →
    b < run.proper.nodes.length →
    ((componentCandidate e.graph comp candidate).nodes.getD v default).border = 0 →
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b

/-- Narrow residual (top owner with loops): the footprint of an in-range group-top
(`border = -2`) candidate node that owns a nonempty loop-size list separates
from every sliver frame. Strictly narrower than `LoopFootprintBeyondProper`
by the added top-border and nonempty-loops premises. The y-branch (different
ranks) follows from member ranks inside `[lo, hi]` plus `rankAxis_bands_disjoint`;
the x-branch (same rank) reduces to same-cluster marker x-alignment, which is
the accepted open seam `ForeignBorderChainXAligned` that the consumer holds.
Probe census shows zero violations; the 120 same-rank x-overlaps are all
nested-group markers already y-separated or degenerate. -/
def TopLoopsSliverResidual (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
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
    LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
      e.measured v b

/-- The beyond-proper footprint seam holds modulo the two narrow sliver
residuals above.
Case split: plain `v` by `PlainSliverResidual`; bottom `v` (`border = 2`) by
the proved `LoopFootprintBottomEmpty_holds` plus the empty-footprint copy;
top `v` with empty loops by the empty-footprint copy; top `v` with loops by
`TopLoopsSliverResidual`. -/
theorem loopFootprintBeyondProper_holds
    (hPlain : ∀ {inp : Input} {o : Options} {res : FamilyResult},
      PlainSliverResidual inp o res)
    (hTop : ∀ {inp : Input} {o : Options} {res : FamilyResult},
      TopLoopsSliverResidual inp o res) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    LoopFootprintBeyondProper inp o res := by
  intro inp o res _hwf _hfp
  intro e comp candidate run orderOptions v b hcomp hrun hv hle hlt
  by_cases hv0 : ((componentCandidate e.graph comp candidate).nodes.getD v default).border = 0
  · exact hPlain e comp candidate run orderOptions v b hcomp hrun hv hle hlt hv0
  · rcases LoopFootprintOtherBorder_holds e comp candidate run orderOptions v hcomp hrun hv hv0
      with htop | hbot
    · by_cases hempty : loopSizes (componentCandidate e.graph comp candidate).edges
          e.measured v (componentCandidate e.graph comp candidate).slot = []
      · exact beyond_sep_of_empty_loops hempty (componentRun_exact_nil hrun)
      · exact hTop e comp candidate run orderOptions v b hcomp hrun hv hle hlt htop hempty
    · have hempty := LoopFootprintBottomEmpty_holds e comp candidate run orderOptions v
        hcomp hrun hv hbot
      exact beyond_sep_of_empty_loops hempty (componentRun_exact_nil hrun)

end PipelineImpl
end Layered
end Elegant

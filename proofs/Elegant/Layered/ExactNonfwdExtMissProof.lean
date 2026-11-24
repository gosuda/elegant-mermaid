import Elegant.Layered.ExactForwardScopeFreeProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact nonforward exterior miss: y-overlap narrowing

Proved: `XNonfwd_extMissRem_of_parts` assembles `XNonfwd_ExtMissRem`
(`ExactForwardScopeFreeProof.lean`: non-self `v ≠ e.tail` miss plus
group-owner self miss with `border ≠ 0`) from two strictly narrower
y-overlap residuals below. Each residual adds one vertical-overlap premise
(`max y < min bottom`) to its parent conjunct; the y-disjoint half of each
conjunct is proved outright inside the assembly (`fun h => hy h.2`).

Stays open: `XNonfwd_ExtMissNonSelfYOverlap` (non-self y-overlapping miss)
and `XNonfwd_ExtMissGroupSelfYOverlap` (group-owner self y-overlapping
miss). Both hold on every executed probe case of
`ExactForwardScopeFreeTProbe` (eleven `#eval report` lines, zero violations
in both checks: flat, shared-rank wide, self alone, zero-size `0x0`,
sibling, nested-group, empty-group, group-loop `G -> G` with
`ownerBorder=-2` over 5 runs of 10 proper boxes, group-loop flat, reversed
pair into a group; ill-formed input and exact-of-group rejected by
`layoutX`): the full miss has no violations there, so each y-overlap
subset has none either. The plain-owner self case (`border = 0`) stays
closed by `XNonfwd_ExtMiss_of_rem` in the imported module.
-/

/-- Narrow residual for the non-self conjunct of `XNonfwd_ExtMissRem`:
the same binders plus a vertical-overlap premise. Strictly narrower than
the parent (one extra premise); the y-disjoint half is closed outright in
`XNonfwd_extMissRem_of_parts`. True on every `ExactForwardScopeFreeTProbe`
miss case, since the full miss has zero violations there. -/
def XNonfwd_ExtMissNonSelfYOverlap (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    v ≠ e.tail →
    max (loopFootprintExt cg run execution.measured e.tail).y
        (RouteImpl.boxRect run.proper run.xs run.ys v).y <
      min ((loopFootprintExt cg run execution.measured e.tail).y +
        (loopFootprintExt cg run execution.measured e.tail).h)
        ((RouteImpl.boxRect run.proper run.xs run.ys v).y +
          (RouteImpl.boxRect run.proper run.xs run.ys v).h) →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Narrow residual for the group-owner self conjunct of
`XNonfwd_ExtMissRem`: the same binders plus a vertical-overlap premise.
Strictly narrower than the parent (one extra premise); the y-disjoint half
is closed outright in `XNonfwd_extMissRem_of_parts`. True on the
`groupLoop` probe rows (`ownerBorder=-2`, no violations). -/
def XNonfwd_ExtMissGroupSelfYOverlap (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    e.tail < run.proper.nodes.length →
    (cg.nodes.getD e.tail default).border ≠ 0 →
    max (loopFootprintExt cg run execution.measured e.tail).y
        (RouteImpl.boxRect run.proper run.xs run.ys e.tail).y <
      min ((loopFootprintExt cg run execution.measured e.tail).y +
        (loopFootprintExt cg run execution.measured e.tail).h)
        ((RouteImpl.boxRect run.proper run.xs run.ys e.tail).y +
          (RouteImpl.boxRect run.proper run.xs run.ys e.tail).h) →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys e.tail)

/-- Both conjuncts of `XNonfwd_ExtMissRem` from the two y-overlap
residuals: y-disjoint boxes miss outright, y-overlapping boxes use the
corresponding residual. -/
theorem XNonfwd_extMissRem_of_parts (exactIds : List String)
    (hNonSelf : XNonfwd_ExtMissNonSelfYOverlap exactIds)
    (hGroupSelf : XNonfwd_ExtMissGroupSelfYOverlap exactIds) :
    XNonfwd_ExtMissRem exactIds := by
  constructor
  · intro inp o res execution comp candidate run orderOptions cg k e v
      hcomp hcg hrun hk hloop hv hne
    by_cases hy : max (loopFootprintExt cg run execution.measured e.tail).y
          (RouteImpl.boxRect run.proper run.xs run.ys v).y <
        min ((loopFootprintExt cg run execution.measured e.tail).y +
          (loopFootprintExt cg run execution.measured e.tail).h)
          ((RouteImpl.boxRect run.proper run.xs run.ys v).y +
            (RouteImpl.boxRect run.proper run.xs run.ys v).h)
    · exact hNonSelf inp o res execution comp candidate run orderOptions cg k e v
        hcomp hcg hrun hk hloop hv hne hy
    · exact fun h => hy h.2
  · intro inp o res execution comp candidate run orderOptions cg k e
      hcomp hcg hrun hk hloop hv hB
    by_cases hy : max (loopFootprintExt cg run execution.measured e.tail).y
          (RouteImpl.boxRect run.proper run.xs run.ys e.tail).y <
        min ((loopFootprintExt cg run execution.measured e.tail).y +
          (loopFootprintExt cg run execution.measured e.tail).h)
          ((RouteImpl.boxRect run.proper run.xs run.ys e.tail).y +
            (RouteImpl.boxRect run.proper run.xs run.ys e.tail).h)
    · exact hGroupSelf inp o res execution comp candidate run orderOptions cg k e
        hcomp hcg hrun hk hloop hv hB hy
    · exact fun h => hy h.2

end PipelineImpl
end Layered
end Elegant

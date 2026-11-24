import Elegant.Layered.RouteRunClearCases

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ## Dummy-cell foreign clearance (coords-stage residual)

`RouteLabelDummyCellForeignClear` is the placement-level core of
`RouteLabelForeignClear`: every forward label-anchor dummy cell misses every
group frame whose declaration avoids the dummy's cluster path. The label-level
conclusion follows via the proved `routeLabelInDummy_of_run` containment
(dummy cell contains the placed label rect).

 Why this shape: the own-group route (`case_group_foreign` via an own group on
 the dummy's path plus the linked strict dummy frame and seam-implied foreign-frame
disjointness) is unavailable when the dummy path is empty — crossing edges have
`nd.node.clusterPath = []` (common prefix of endpoint paths from different
regions), so every group is "outside" yet no own group exists. The dummy-cell
statement covers both cases uniformly (empty and nonempty paths).

Probe evidence (`proofs/wip/Probe/RouteLabelForeignClearTProbe.lean`,
`RouteLabelForeignClearTProbe3.lean`): 155 outside pairs across 6 inputs
(cross-border, inside-group, sibling-cross, nested, sibling-inside,
nested-sibling) × TB/LR/cell profiles × 5 candidates — `dummyMeets = false`
everywhere, including nonempty-path dummies against outside sibling groups
(where an own group also exists) and empty-path dummies (where none exists).
No violations at either label or dummy-cell level.

Future derivation (not attempted here): the empty-path case is a rank-band /
border-marker separation of one proper cell against a group hull (the same
machinery as `ForeignNonGroupSpansClear`, applied to a cell instead of a
 frame); the nonempty-path case follows from the linked strict dummy frame
 plus `ForeignFramesDisjoint` through the innermost own group. Hence the
 retained seam hypotheses below. -/
def RouteLabelDummyCellForeignClear (P : Params) (cg : Graph) (run : Run) : Prop :=
  ∀ (edge : Nat) (e : Edge),
    cg.edges[edge]? = some e → e.tail ≠ e.head → e.reversed = false →
    ∀ (d : Nat) (nd : ProperNode), nd.dummy = true →
      run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge && rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (nd, d) →
      ∀ (gpos : Nat) (gn : Node), cg.nodes[gpos]? = some gn → gn.border = -2 →
        gn.decl ∉ nd.node.clusterPath →
        Disjoint (Labels.rectAt run.proper run.xs run.ys d) (frameRect P cg run gpos)

/-- Executed `RouteLabelForeignClear`: a placed forward label misses every
group frame outside its anchor dummy's cluster path. The label lies in its
 dummy cell (`routeLabelInDummy_of_run`, proved); the cell misses the foreign
 frame by the coords-stage residual `RouteLabelDummyCellForeignClear`. The
 three span seams are retained as hypotheses for the future derivation of the
 residual (see above); they are not needed for this step. -/
theorem routeLabelForeignClear_of_run {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    (_hbracket : BracketMarkersAtRank) (_hrank : ForeignClusterRankSpans)
    (_hxalign : ForeignBorderChainXAligned)
    (hcell : RouteLabelDummyCellForeignClear execution.params
      (componentCandidate execution.graph comp candidate) run) :
    RouteLabelForeignClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  intro _ _ _ _ k rect l₀ edge e hmem hmem0 hidx hedge hdecl hne hrev
    d nd hdummy hfindd gpos gn hg hgrp hout
  have hC := routeLabelInDummy_of_run execution hcomp hrun k rect l₀ edge e
    hmem hmem0 hidx hedge hdecl hne hrev d nd hdummy hfindd
  have hD := hcell edge e hedge hne hrev d nd hdummy hfindd gpos gn hg hgrp hout
  have hS : Disjoint rect (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run gpos) := by
    unfold Rect.Contained at hC
    unfold Disjoint Rect.meetsInterior at hD ⊢
    omega
  unfold Disjoint Rect.meetsInterior at hS ⊢
  omega

end Elegant.Layered.PipelineImpl

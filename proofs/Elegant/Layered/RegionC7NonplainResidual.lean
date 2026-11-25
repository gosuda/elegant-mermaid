import Elegant.Layered.RegionC7SelectedForwardSameRank
import Elegant.Layered.RegionBaseExecutedValidity

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- `r7Eff` is some only when the component resolved regions: the `none` arm
of `r7Eff` is exactly the region-free (exact) pipeline. -/
theorem r7Eff_isSome_imp {idSets : List (String × List String)} {o : Options}
    {P : Params} {lines : List (List Measure.Line)}
    {rs : Option ComponentRegions}
    (h : (r7Eff idSets o P lines rs).isSome = true) : rs.isSome = true := by
  cases rs with
  | none => simp [r7Eff] at h
  | some _ => rfl

/-- On an executed selected pair, an `r7Eff`-none effective spec means the
component resolved no regions at all. -/
theorem r7Selected_eff_none_imp_rs_none {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (heff : r7Eff idSets o execution.params execution.lines pair.rs = none) :
    pair.rs = none := by
  have hresolve := componentTrialR_selected_regions pair.candidate pair.regions_eq
  change newComponentRegions (r7Eff idSets o execution.params execution.lines pair.rs)
      execution.params inp
      (componentCandidateR (r7Eff idSets o execution.params execution.lines pair.rs)
        execution.graph pair.part.1 pair.candidate) = .ok pair.rs at hresolve
  rw [heff] at hresolve
  rw [newComponentRegions_none] at hresolve
  simpa using (Except.ok.inj hresolve).symm

/-- Every selected loop pair with a plain tail and a plain target is settled,
cross-owner, or exact-later: the unsettled-loop residual has no plain-tail
instances. The case split is on the target rank relative to the tail, the
effective region spec, the last cluster path, and exact sizing. -/
theorem r7Selected_plainLoop_covered {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (hloop : pair.edge.tail = pair.edge.head)
    {nu nv : Node}
    (hu : pair.cg.nodes[pair.edge.tail]? = some nu)
    (hv : pair.cg.nodes[pair.target]? = some nv)
    (hbu : nu.border = 0) (hbv : nv.border = 0) :
    R7_SelectedSettledLoop pair ∨ R7_SelectedActiveCrossOwnerPlainLoop pair ∨
      R7_SelectedExactLaterPlainLoop pair := by
  classical
  by_cases hvu : pair.target = pair.edge.tail
  · left
    refine ⟨hloop, ?_⟩
    exact ⟨nu, nv, hu, hv, hbu, hbv, Or.inl hvu⟩
  · rcases Nat.lt_trichotomy
      ((rk pair.run.proper.rank pair.target).toNat)
      ((rk pair.run.proper.rank pair.edge.tail).toNat) with hlt | heq | hgt
    · left
      refine ⟨hloop, ?_⟩
      exact ⟨nu, nv, hu, hv, hbu, hbv, Or.inr (Or.inl hlt)⟩
    · by_cases hspec : (r7Eff idSets o execution.params execution.lines pair.rs).isSome = true
      · by_cases hpath : nu.clusterPath.getLast? = nv.clusterPath.getLast?
        · left
          refine ⟨hloop, ?_⟩
          exact ⟨nu, nv, hu, hv, hbu, hbv,
            Or.inr (Or.inr (Or.inl ⟨heq.symm, fun _ => hpath⟩))⟩
        · right; left
          refine ⟨r7Eff_isSome_imp hspec, hloop, heq.symm, ?_⟩
          exact ⟨nu, nv, hu, hv, hbu, hbv, hpath⟩
      · left
        refine ⟨hloop, ?_⟩
        exact ⟨nu, nv, hu, hv, hbu, hbv,
          Or.inr (Or.inr (Or.inl ⟨heq.symm, fun h => (hspec h).elim⟩))⟩
    · by_cases hexact : pair.run.exact.contains pair.edge.tail = true
      · right; right
        refine ⟨hloop, hexact, hgt, ?_⟩
        exact ⟨nu, nv, hu, hv, hbu, hbv⟩
      · have hfalse : pair.run.exact.contains pair.edge.tail = false := by
          cases h : pair.run.exact.contains pair.edge.tail with
          | true => exact (hexact h).elim
          | false => rfl
        left
        refine ⟨hloop, ?_⟩
        exact ⟨nu, nv, hu, hv, hbu, hbv, Or.inr (Or.inr (Or.inr ⟨hgt, hfalse⟩))⟩

/-- Under the region admission premises, a residual group-tail selected loop
runs the exact (region-free) pipeline: the active group-owner clause fails
only when `r7Eff` is none. -/
theorem r7Selected_groupTail_eff_none {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hgroupneg : ¬ (WellFormed (inputModel inp o) ∧ framedParents inp = true ∧
      ∃ (s : RegionSpec) (owner : Node),
        r7Eff idSets o execution.params execution.lines pair.rs = some s ∧
        pair.cg.nodes[pair.edge.tail]? = some owner ∧ owner.border = -2))
    {nu : Node} (hu : pair.cg.nodes[pair.edge.tail]? = some nu) (hb : nu.border = -2) :
    pair.rs = none := by
  have hnoeff : ¬ ∃ s : RegionSpec,
      r7Eff idSets o execution.params execution.lines pair.rs = some s := by
    rintro ⟨s, hs⟩
    exact hgroupneg ⟨hwf, hfp, s, nu, hs, hu, hb⟩
  have heff : r7Eff idSets o execution.params execution.lines pair.rs = none := by
    cases h : r7Eff idSets o execution.params execution.lines pair.rs with
    | none => rfl
    | some s => exact (hnoeff ⟨s, h⟩).elim
  exact r7Selected_eff_none_imp_rs_none pair heff

/-- The remaining selected-loop C7 obligation after the plain-tail and
active-group eliminations: an inactive (region-free) selected loop owned by a
group top against a plain target. Every other selected-loop instance is
settled, cross-owner, exact-later, or an active group loop. -/
def R7_SelectedInactiveGroupLoopClearance {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (pair : R7_SelectedRoutePair execution l b),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    pair.edge.tail = pair.edge.head → pair.rs = none →
    (∃ node : Node, pair.cg.nodes[pair.target]? = some node ∧ node.border = 0) →
    ∃ nu : Node, pair.cg.nodes[pair.edge.tail]? = some nu ∧ nu.border = -2 →
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target)

#print axioms Elegant.Layered.PipelineImpl.r7Eff_isSome_imp
#print axioms Elegant.Layered.PipelineImpl.r7Selected_eff_none_imp_rs_none
#print axioms Elegant.Layered.PipelineImpl.r7Selected_plainLoop_covered
#print axioms Elegant.Layered.PipelineImpl.r7Selected_groupTail_eff_none

end Elegant.Layered.PipelineImpl

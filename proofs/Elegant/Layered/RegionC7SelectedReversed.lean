import Elegant.Layered.RegionSelectedCaptionClearance
import Elegant.Layered.RegionC6SelectedTrunk

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- The selected branch is identified by the actual ranked edge and the original
plain box lookup, without a geometric clearance premise. -/
def R7_SelectedReversedPlainPair {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b) : Prop :=
  pair.edge.tail ≠ pair.edge.head ∧ pair.edge.reversed = true ∧
    ∃ node, pair.cg.nodes[pair.target]? = some node ∧ node.border = 0

/-- The selected reversed stack clears the target draw interval in either sibling
order. For a local lane the upper bound includes the label width, not just its trunk. -/
theorem r7Selected_reversedPlain_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (hpair : R7_SelectedReversedPlainPair pair) :
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  obtain ⟨hnotLoop, hrev, node, hnode, hplain⟩ := hpair
  obtain ⟨_, lane, _, hfind, henv⟩ :=
    reversed_envelope_eq hnotLoop hrev pair.envelope_eq
  have hstack := (List.of_mem_zip pair.stack).2
  have hslot := r7ComponentRun_slot_of_scene execution
    (comp := pair.part.1) (candidate := pair.candidate) pair.run_eq
  have hx : pair.rect.x = lane.lane + execution.params.slot := by
    calc
      pair.rect.x = pair.envelope.x := (stackRects_entry hstack).1
      _ = lane.lane + pair.cg.slot := congrArg Rect.x henv
      _ = lane.lane + execution.params.slot := by rw [hslot]
  have hw : pair.rect.w ≤ (stackSize pair.cg.slot
      (routeLabels execution.measured pair.edge.decl)).width := by
    rw [stackSize_width_eq]
    exact stackRect_width_le hstack
  have hs : 0 ≤ execution.params.slot :=
    Int.le_trans (by decide) (componentRunR_slot_pos pair.run_eq)
  let effective := r7Eff idSets o execution.params execution.lines pair.rs
  have hrun : componentRunR execution.params (exactDecls exactIds inp) effective inp
      (componentCandidateR effective execution.graph pair.part.1 pair.candidate)
      execution.measured (candidateOrder pair.candidate) = .ok (pair.cg, pair.run) := pair.run_eq
  have hresolve : newComponentRegions effective execution.params inp
      (componentCandidateR effective execution.graph pair.part.1 pair.candidate) =
      .ok pair.rs := componentTrialR_selected_regions pair.candidate pair.regions_eq
  intro _ _ _
  cases heff : effective with
  | none =>
    rw [heff] at hrun
    obtain ⟨rs, _, _, _, _, _, _, _, _, reserved, _, _, _, _, stages⟩ :=
      componentRunR_stages hrun
    have hnone : rs = none := Except.ok.inj stages.hRs.symm
    have hreserved : reserved = [] := by
      rcases stages.hPlaced with ⟨_, _, _, hnil, _⟩ | ⟨_, _, hactive, _, _⟩
      · exact hnil
      · rw [hnone] at hactive
        cases hactive
    rcases stages.hLanes with ⟨_, hroute⟩ | ⟨hnotEmpty, _⟩
    · have hmem := List.mem_of_find?_eq_some hfind
      obtain ⟨_, _, _, hplan⟩ := RouteImpl.routeWithLanes_spec hroute
      rw [hplan] at hmem
      have hright := RouteImpl.plannedLane_right_strict hs hmem
      have hbox := RouteImpl.laneRight_bound pair.run.proper pair.run.xs pair.target_size
      have hext : 0 ≤ ((pair.run.proper.nodes.getD pair.target default).node.loopExtent : Int) :=
        Int.natCast_nonneg _
      apply Or.inr
      rw [hx, Elegant.Layered.boxRect_left, Elegant.Layered.boxRect_w]
      omega
    · simp [hreserved] at hnotEmpty
  | some spec =>
    rw [heff] at hrun
    cases hrs : pair.rs with
    | none => simp [effective, r7Eff, hrs] at heff
    | some rm =>
      have hactive := hresolve
      rw [heff, hrs] at hactive
      rcases RegionOrdinaryC6.selectedTrunk_labelBand_crossClear (o := o)
        execution.checked hrun hactive pair.edge_eq hnotLoop hnode hplain hfind with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)

def R7_SelectedRouteAfterReversedPlain {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (pair : R7_SelectedRoutePair execution l b),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel → ¬ R7_SelectedSettledLoop pair →
    ¬ R7_SelectedReversedPlainPair pair →
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target)

theorem r7SelectedRoute_iff_afterReversedPlain {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    R7_SelectedRouteObligation execution ↔ R7_SelectedRouteAfterReversedPlain execution := by
  classical
  constructor
  · intro h l b pair hl hb hex hscope hloop _
    exact h l b pair hl hb hex hscope hloop
  · intro h l b pair hl hb hex hscope hloop
    by_cases hrev : R7_SelectedReversedPlainPair pair
    · exact r7Selected_reversedPlain_clear pair hrev
    · exact h l b pair hl hb hex hscope hloop hrev

end Elegant.Layered.PipelineImpl

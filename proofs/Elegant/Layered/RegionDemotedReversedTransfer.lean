import Elegant.Layered.RegionReservedChildTransfer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

def R8b_EmittedDemotedReversedAt {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (index : Nat) (stored : Rect) (pos : Nat)
    (_srcBox : ModelBox) : Prop :=
  selected.spec = none ∧
  ∃ (srcLabel : ModelLabel) (label : MeasuredLabel) (raw : Rect) (group : Node)
    (edge : Nat) (e : Edge),
    inp.labels[index]? = some srcLabel ∧
    (inp.boxes.any fun b => b.id == srcLabel.owner && b.exclusive) = false ∧
    execution.measured.find? (fun l => l.index == index) = some label ∧
    (index, raw) ∈ placedLabels execution.params selected.cg selected.run execution.measured ∧
    (let bounds := placeBoundsX execution.params selected.cg selected.run
        execution.measured selected.loops
     stored = shiftRect (0 - bounds.minX) (-bounds.minY) raw) ∧
    selected.cg.edges.findIdx? (fun x => x.decl == label.edge) = some edge ∧
    selected.cg.edges[edge]? = some e ∧ e.tail ≠ e.head ∧ e.reversed = true ∧
    selected.cg.nodes[pos]? = some group ∧ group.border = -2

private theorem r8b_demotedReversed_raw_disjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    {selected : R8b_ChosenPart execution part} {index pos edge : Nat}
    {raw : Rect} {label : MeasuredLabel} {e : Edge} {group : Node}
    (hspec : selected.spec = none)
    (hfind : execution.measured.find? (fun l => l.index == index) = some label)
    (hraw : (index, raw) ∈ placedLabels execution.params selected.cg selected.run execution.measured)
    (hedgeFind : selected.cg.edges.findIdx? (fun x => x.decl == label.edge) = some edge)
    (hedge : selected.cg.edges[edge]? = some e) (htail : e.tail ≠ e.head)
    (hrev : e.reversed = true) (hnode : selected.cg.nodes[pos]? = some group)
    (hborder : group.border = -2) :
    Disjoint (frameRect execution.params selected.cg selected.run pos) raw := by
  have hrun := selected.run_eq
  rw [hspec] at hrun
  obtain ⟨rs, _, _, _, _, _, _, _, widths, reserved, _, _, _, _, stages⟩ :=
    componentRunR_stages hrun
  have hrs : rs = none := Except.ok.inj stages.hRs.symm
  subst rs
  have hcg : selected.cg = componentCandidateR none execution.graph part.1 selected.candidate := by
    rcases stages.hRank with ⟨_, _, _, _, hcg, _⟩ | ⟨_, hactive, _⟩
    · exact hcg
    · cases hactive
  have hcgSlot : selected.cg.slot = execution.params.slot := by
    have hcandidate : (componentCandidateR none execution.graph part.1 selected.candidate).slot =
        execution.graph.slot := by
      change (componentCandidate execution.graph part.1 selected.candidate).slot = _
      unfold componentCandidate
      dsimp only
      split
      · split <;> rfl
      · unfold cycleGraph
        split <;> rfl
    obtain ⟨_, _, hg⟩ := bind_ok execution.graph_eq
    have hslot0 : execution.graph.slot = execution.graph0.slot :=
      (congrArg Graph.slot (Except.ok.inj hg)).symm
    obtain ⟨_, _, _, hgraph0, _, _⟩ := measuredGraph_prepared_source execution.graph0_eq
    rw [hcg, hcandidate, hslot0, hgraph0] <;> rfl
  have hslot : 0 ≤ execution.params.slot := by
    have h := (checkedParams_valid execution.checked).2.2.1
    omega
  have hreserved : reserved = [] := by
    rcases stages.hPlaced with ⟨_, _, _, hnil, _⟩ | ⟨_, _, hactive, _, _⟩
    · exact hnil
    · cases hactive
  have hroute : RouteImpl.routeWithLanes execution.params.slot selected.run.proper
      selected.run.layers selected.run.xs (selected.cg.edges.map (·.reversed)) widths =
      .ok selected.run.lanes := by
    rcases stages.hLanes with ⟨_, hroute⟩ | ⟨hnotEmpty, _⟩
    · exact hroute
    · simp [hreserved] at hnotEmpty
  have hindex : label.index = index := by
    have hpred := List.find?_some hfind
    simpa only [beq_iff_eq] using hpred
  obtain ⟨lane, hlane, _, hx⟩ :=
    placedLabels_reversed_lane_x hraw (measureLabels_index_nodup execution.measured_eq)
      (List.mem_of_find?_eq_some hfind) hindex hedgeFind hedge htail hrev
  have hLaneMem := List.mem_of_find?_eq_some hlane
  obtain ⟨_, _, _, hplan⟩ := RouteImpl.routeWithLanes_spec hroute
  rw [hplan] at hLaneMem
  have hlower : RouteImpl.laneRight selected.run.proper selected.run.xs +
      execution.params.slot ≤ lane.lane := RouteImpl.plannedLane_right_strict hslot hLaneMem
  have hframeRight :
      (frameRect execution.params selected.cg selected.run pos).x +
        (frameRect execution.params selected.cg selected.run pos).w ≤
        RouteImpl.laneRight selected.run.proper selected.run.xs := by
    have hhull : (boundsOf (groupBorderRects selected.cg selected.run group.decl) []).right ≤
        RouteImpl.laneRight selected.run.proper selected.run.xs := by
      apply boundsOf_right_le_of_all (RouteImpl.laneRight_nonneg _ _)
      intro r hr
      obtain ⟨v, _, hv, _, _, rfl⟩ := groupBorderRects_inv hr
      have h := RouteImpl.laneRight_bound selected.run.proper selected.run.xs
        (List.getElem?_eq_some_iff.mp hv).1
      have he : 0 ≤ ((selected.run.proper.nodes.getD v default).node.loopExtent : Int) :=
        Int.natCast_nonneg _
      change RouteImpl.xAt selected.run.xs v -
        Int.fdiv (RouteImpl.nodeW selected.run.proper v) 2 +
        RouteImpl.nodeW selected.run.proper v ≤ _
      omega
    rw [frameRect_group_span hnode hborder]
    dsimp only
    omega
  exact rect_disjoint_of_x (Or.inl (by omega))

theorem r8b_demotedReversed_part_disjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    {selected : R8b_ChosenPart execution part} {index pos : Nat} {stored frame : Rect}
    {srcBox : ModelBox} (hframe : part.2.rects[pos]? = some frame)
    (hbranch : R8b_EmittedDemotedReversedAt selected index stored pos srcBox) :
    Disjoint frame stored := by
  obtain ⟨hspec, _, _, raw, _, _, _, _, _, hfind, hraw, hstored, hedgeFind, hedge, htail,
    hrev, hnode, hborder⟩ := hbranch
  have hclear := r8b_demotedReversed_raw_disjoint hspec hfind hraw hedgeFind hedge htail hrev
    hnode hborder
  let bounds := placeBoundsX execution.params selected.cg selected.run execution.measured
    selected.loops
  let translate := shiftRect (0 - bounds.minX) (-bounds.minY)
  have hpos := (List.getElem?_eq_some_iff.mp hnode).1
  have hframe' : part.2.rects[pos]? =
      some (translate (frameRect execution.params selected.cg selected.run pos)) := by
    rw [selected.part_eq]
    unfold placeComponentExact
    change (((List.range selected.cg.nodes.length).map
      (frameRect execution.params selected.cg selected.run)).map translate)[pos]? = _
    simp only [List.getElem?_map, List.getElem?_range hpos, Option.map_some]
  have hframeEq := Option.some.inj (hframe.symm.trans hframe')
  change stored = translate raw at hstored
  rw [hframeEq, hstored]
  exact disjoint_shiftRect hclear

theorem regionC8b_selectedDemotedReversed_emitted {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    {selected : R8b_ChosenPart execution part} {index pos key : Nat}
    {stored frame shelf : Rect} {srcBox : ModelBox}
    (hframe : part.2.rects[pos]? = some frame)
    (hkey : part.1[pos]? = some key) (hsrc : inp.boxes[key]? = some srcBox)
    (hgroup : srcBox.role = .group)
    (hpackBox : execution.packedAcc.rects.getD key default = shiftRect shelf.x shelf.y frame)
    (hpackLabel : execution.packedAcc.labels.getD index default = shiftRect shelf.x shelf.y stored)
    (hbranch : R8b_EmittedDemotedReversedAt selected index stored pos srcBox) :
    ∃ (srcLabel : ModelLabel) (g : Box) (l : SceneLabel),
      inp.labels[index]? = some srcLabel ∧ g ∈ res.scene.boxes ∧ l ∈ res.scene.labels ∧
      g.id = srcBox.id ∧ g.role = "group" ∧ l.id = srcLabel.id ∧ Disjoint g.rect l.rect := by
  obtain ⟨hspec, srcLabel, _, _, _, _, _, hsrcLabel, hvisible, hfind, hraw, hstored,
    hedgeFind, hedge, htail, hrev, hnode, hborder⟩ := hbranch
  have hclear := r8b_demotedReversed_raw_disjoint hspec hfind hraw hedgeFind hedge htail hrev
    hnode hborder
  have hpos := (List.getElem?_eq_some_iff.mp hnode).1
  obtain ⟨g, l, hg, hl, hgid, hrole, hlid, hdisjoint⟩ :=
    regionC8b_samePart_emitted_routeLabel_disjoint execution selected.part_eq hkey hpos
      hsrc hgroup hsrcLabel hvisible hfind hframe hstored
      (fun _ _ => hpackBox) (fun _ => hpackLabel) hraw hclear
  exact ⟨srcLabel, g, l, hsrcLabel, hg, hl, hgid, hrole, hlid, hdisjoint⟩

def R_ExecutedPartFrameCoresB8OuterReservedChildDemotedRemainder (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    ∀ part ∈ execution.componentsAcc.parts,
      (∀ (selected : R8b_ChosenPart execution part)
        (index : Nat) (stored : Rect) (pos key : Nat) (src : ModelBox) (frame : Rect),
        (index, stored) ∈ part.2.labels →
        part.1[pos]? = some key →
        inp.boxes[key]? = some src →
        src.role = .group →
        part.2.rects[pos]? = some frame →
        ¬ R8b_EmittedOuterReversedAt selected index stored pos →
        ¬ R8b_EmittedReservedChildAt selected index pos →
        ¬ R8b_EmittedDemotedReversedAt selected index stored pos src →
        Disjoint frame stored ∨ frame.StrictInside stored) ∧
      PartCaptionFrameClear execution.params inp o execution.lines part

theorem R_executedPartFrameCoresB8OuterReservedChildRemainder_iff_demotedRemainder
    (exactIds : List String) (idSets : List (String × List String)) :
    R_ExecutedPartFrameCoresB8OuterReservedChildRemainder exactIds idSets ↔
      R_ExecutedPartFrameCoresB8OuterReservedChildDemotedRemainder exactIds idSets := by
  classical
  constructor
  · intro old inp o res execution part hpart
    obtain ⟨hroute, hcaption⟩ := old execution part hpart
    refine ⟨?_, hcaption⟩
    intro selected index stored pos key src frame hlabel hkey hsrc hgroup hframe houter hchild _
    exact hroute selected index stored pos key src frame hlabel hkey hsrc hgroup hframe
      houter hchild
  · intro remaining inp o res execution part hpart
    obtain ⟨hroute, hcaption⟩ := remaining execution part hpart
    refine ⟨?_, hcaption⟩
    intro selected index stored pos key src frame hlabel hkey hsrc hgroup hframe houter hchild
    by_cases hdemoted : R8b_EmittedDemotedReversedAt selected index stored pos src
    · exact Or.inl (r8b_demotedReversed_part_disjoint hframe hdemoted)
    · exact hroute selected index stored pos key src frame hlabel hkey hsrc hgroup hframe
        houter hchild hdemoted

#print axioms r8b_demotedReversed_part_disjoint
#print axioms regionC8b_selectedDemotedReversed_emitted
#print axioms R_executedPartFrameCoresB8OuterReservedChildRemainder_iff_demotedRemainder

end Elegant.Layered.PipelineImpl

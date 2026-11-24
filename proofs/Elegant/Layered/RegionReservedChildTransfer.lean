import Elegant.Layered.RegionReservedChildJoinTrace

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- The actual edge owner has an immediate child whose top record is the frame
slot in the selected part. The owner and child row use the pre-crossing proper
of that candidate, not the rewritten `run.coordinateProper`. -/
def R8b_ActualReservedChildAt {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (e : Edge) (pos : Nat) : Prop :=
  ∃ (s : RegionSpec) (rm : ComponentRegions),
    selected.spec = some s ∧
    newComponentRegions (some s) execution.params inp
      (componentCandidateR (some s) execution.graph part.1 selected.candidate) = .ok (some rm) ∧
    ∃ (p : Proper) (groups : List Nat) (children : List (List Nat)),
      activeReservedChildCrossInput execution.params (exactDecls exactIds inp) s rm
        (componentCandidateR (some s) execution.graph part.1 selected.candidate)
        execution.measured = .ok p ∧
      nodeGroupsOf rm p = .ok groups ∧ regionChildren rm = .ok children ∧
      ∃ (owner child k : Nat) (c : RegionCluster),
        owner < rm.clusters.length ∧
        edgeOwnerOf rm groups rm.clusters.length e.tail e.head = owner ∧
        (children.getD owner [])[k]? = some child ∧
        rm.clusters[child]? = some c ∧ c.top = pos

/-- A stored route label that is emitted through `sceneOf`'s measured-label
arm and whose actual selected non-self reversed edge owns the frame's parent. -/
def R8b_EmittedReservedChildAt {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (index pos : Nat) : Prop :=
  ∃ (srcLabel : ModelLabel) (label : MeasuredLabel) (edge : Nat) (e : Edge),
    inp.labels[index]? = some srcLabel ∧
    (inp.boxes.any fun b => b.id == srcLabel.owner && b.exclusive) = false ∧
    execution.measured.find? (fun l => l.index == index) = some label ∧
    selected.cg.edges.findIdx? (fun x => x.decl == label.edge) = some edge ∧
    selected.cg.edges[edge]? = some e ∧ e.tail ≠ e.head ∧ e.reversed = true ∧
    R8b_ActualReservedChildAt selected e pos

theorem r8b_reservedChild_geometry {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part)
    (hpart : part ∈ execution.componentsAcc.parts) {index pos : Nat} {stored frame : Rect}
    (hstored : (index, stored) ∈ part.2.labels) (hframe : part.2.rects[pos]? = some frame)
    (hbranch : R8b_EmittedReservedChildAt selected index pos) :
    Disjoint frame stored ∧
    ∃ (srcLabel : ModelLabel) (label : MeasuredLabel) (raw : Rect),
      inp.labels[index]? = some srcLabel ∧
      (inp.boxes.any fun b => b.id == srcLabel.owner && b.exclusive) = false ∧
      execution.measured.find? (fun l => l.index == index) = some label ∧
      pos < selected.cg.nodes.length ∧
      (index, raw) ∈ placedLabels execution.params selected.cg selected.run execution.measured ∧
      (let b := placeBoundsX execution.params selected.cg selected.run execution.measured
          selected.loops
       stored = shiftRect (0 - b.minX) (-b.minY) raw) ∧
      Disjoint (frameRect execution.params selected.cg selected.run pos) raw := by
  obtain ⟨srcLabel, label, edge, e, hsrcLabel, hvisible, hfind, hedgeFind, hedge, hnonloop,
    hreversed, hownerChild⟩ := hbranch
  obtain ⟨s, rm, hspec, hactive, proper, groups, children, hproper, hgroups, hchildren,
    owner, child, k, c, howner, heOwner, hchild, hc, htop⟩ := hownerChild
  have hrun := selected.run_eq
  rw [hspec] at hrun
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem hpart
  obtain ⟨p, _, _, _, stages, _, hinput, ⟨_, _, hrank⟩, hclear⟩ :=
    componentRunR_active_reservedChildReversedLabel_disjoint_traced execution.graph0_eq
      execution.graph_eq hcomp execution.checked hrun hactive
  have heProper : p = proper := Except.ok.inj (hinput.symm.trans hproper)
  subst p
  have heGroups : stages.groups = groups := Except.ok.inj (stages.hGroups.symm.trans hgroups)
  have heChildren : stages.placement.children = children := by
    rw [stages.hPlacement]
    exact Except.ok.inj (stages.hChildren.symm.trans hchildren)
  have howner' : edgeOwnerOf rm stages.groups rm.clusters.length e.tail e.head = owner := by
    rwa [heGroups]
  have hchild' : (stages.placement.children.getD owner [])[k]? = some child := by
    rwa [heChildren]
  obtain ⟨node, hnode, hborder, hdecl⟩ := activeChild_frame_record hactive hrank hc
  rw [htop] at hnode
  let b := placeBoundsX execution.params selected.cg selected.run execution.measured selected.loops
  have hmapped : (index, stored) ∈
      (placedLabels execution.params selected.cg selected.run execution.measured).map
        (fun q => (q.1, shiftRect (0 - b.minX) (-b.minY) q.2)) := by
    rw [selected.part_eq] at hstored
    exact hstored
  obtain ⟨⟨i, raw⟩, hraw, heStore⟩ := List.mem_map.mp hmapped
  change (i, shiftRect (0 - b.minX) (-b.minY) raw) = (index, stored) at heStore
  simp only [Prod.mk.injEq] at heStore
  obtain ⟨hi, heStore⟩ := heStore
  subst i
  have hindex : label.index = index := by
    have hpred := List.find?_some hfind
    simpa only [beq_iff_eq] using hpred
  obtain ⟨_, _, _, hrawClear, hstoredClear⟩ := hclear howner howner' hchild' hc
    hnode hborder hdecl hraw (measureLabels_index_nodup execution.measured_eq)
    (List.mem_of_find?_eq_some hfind) hindex hedgeFind hedge hnonloop hreversed
  refine ⟨hstoredClear selected.loops selected.part_eq hframe heStore.symm, ?_⟩
  exact ⟨srcLabel, label, raw, hsrcLabel, hvisible, hfind, (List.getElem?_eq_some_iff.mp hnode).1,
    hraw, heStore.symm, hrawClear⟩

/-- Transport the selected direct-child case to the emitted box and label, with
both packed lookups referring to the same shelf. -/
theorem regionC8b_selectedReservedChild_emitted {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part)
    (hpart : part ∈ execution.componentsAcc.parts) {index pos key : Nat}
    {stored frame shelf : Rect} {srcBox : ModelBox}
    (hstored : (index, stored) ∈ part.2.labels) (hframe : part.2.rects[pos]? = some frame)
    (hkey : part.1[pos]? = some key) (hsrc : inp.boxes[key]? = some srcBox)
    (hgroup : srcBox.role = .group)
    (hpackBox : execution.packedAcc.rects.getD key default = shiftRect shelf.x shelf.y frame)
    (hpackLabel : execution.packedAcc.labels.getD index default = shiftRect shelf.x shelf.y stored)
    (hbranch : R8b_EmittedReservedChildAt selected index pos) :
    ∃ (srcLabel : ModelLabel) (g : Box) (l : SceneLabel),
      inp.labels[index]? = some srcLabel ∧ g ∈ res.scene.boxes ∧ l ∈ res.scene.labels ∧
      g.id = srcBox.id ∧ g.role = "group" ∧ l.id = srcLabel.id ∧ Disjoint g.rect l.rect := by
  obtain ⟨_, srcLabel, label, raw, hsrcLabel, hvisible, hfind, hpos, hmem, hshift, hclear⟩ :=
    r8b_reservedChild_geometry selected hpart hstored hframe hbranch
  obtain ⟨g, l, hg, hl, hid, hrole, hlid, hdisjoint⟩ :=
    regionC8b_samePart_emitted_routeLabel_disjoint execution selected.part_eq hkey hpos
      hsrc hgroup hsrcLabel hvisible hfind hframe hshift
      (fun _ _ => hpackBox) (fun _ => hpackLabel) hmem hclear
  exact ⟨srcLabel, g, l, hsrcLabel, hg, hl, hid, hrole, hlid, hdisjoint⟩

/-- Same selected stored cores as the outer remainder, except that the actual
emitted reversed-label/immediate-child case no longer needs clearance here. -/
def R_ExecutedPartFrameCoresB8OuterReservedChildRemainder (exactIds : List String)
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
        Disjoint frame stored ∨ frame.StrictInside stored) ∧
      PartCaptionFrameClear execution.params inp o execution.lines part

theorem R_executedPartFrameCoresB8OuterRemainder_iff_reservedChildRemainder
    (exactIds : List String) (idSets : List (String × List String)) :
    R_ExecutedPartFrameCoresB8OuterRemainder exactIds idSets ↔
      R_ExecutedPartFrameCoresB8OuterReservedChildRemainder exactIds idSets := by
  classical
  constructor
  · intro old inp o res execution part hpart
    obtain ⟨hroute, hcaption⟩ := old execution part hpart
    refine ⟨?_, hcaption⟩
    intro selected index stored pos key src frame hlabel hkey hsrc hgroup hframe houter _
    exact hroute selected index stored pos key src frame hlabel hkey hsrc hgroup hframe houter
  · intro remaining inp o res execution part hpart
    obtain ⟨hroute, hcaption⟩ := remaining execution part hpart
    refine ⟨?_, hcaption⟩
    intro selected index stored pos key src frame hlabel hkey hsrc hgroup hframe houter
    by_cases hchild : R8b_EmittedReservedChildAt selected index pos
    · exact Or.inl (r8b_reservedChild_geometry selected hpart hlabel hframe hchild).1
    · exact hroute selected index stored pos key src frame hlabel hkey hsrc hgroup hframe houter hchild

theorem R_reindexedPartFrameCoresB8OuterRemainder_iff_reservedChildRemainder
    (exactIds : List String) (idSets : List (String × List String)) :
    (∀ sub : Input, R_ExecutedPartFrameCoresB8OuterRemainder exactIds
      (reindexRegionSets idSets sub)) ↔
    (∀ sub : Input, R_ExecutedPartFrameCoresB8OuterReservedChildRemainder exactIds
      (reindexRegionSets idSets sub)) := by
  constructor
  · intro h sub
    exact (R_executedPartFrameCoresB8OuterRemainder_iff_reservedChildRemainder exactIds
      (reindexRegionSets idSets sub)).mp (h sub)
  · intro h sub
    exact (R_executedPartFrameCoresB8OuterRemainder_iff_reservedChildRemainder exactIds
      (reindexRegionSets idSets sub)).mpr (h sub)

end Elegant.Layered.PipelineImpl

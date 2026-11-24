import Elegant.Layered.RegionDemotedReversedTransfer
import Elegant.Layered.RegionFlatInset
import Elegant.Layered.RegionReduction
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactNonforwardHullFinalProof
import Elegant.Layered.PolylineBoxMiss

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- The selected measured-label arm, for a self-loop against its own frame or
against a genuine group frame in the demoted run that admits exact replay.
The same-slot case does not require demotion, a particular owner depth, or
side-marker geometry. The exact replay applies to ancestors, descendants,
and unrelated group frames of the same selected component. -/
def R8b_EmittedSelectedLoopFrameAt {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (index pos : Nat) : Prop :=
  ∃ (srcLabel : ModelLabel) (label : MeasuredLabel) (edge : Nat) (e : Edge) (group : Node),
    inp.labels[index]? = some srcLabel ∧
    (inp.boxes.any fun b => b.id == srcLabel.owner && b.exclusive) = false ∧
    execution.measured.find? (fun l => l.index == index) = some label ∧
    selected.cg.edges.findIdx? (fun x => x.decl == label.edge) = some edge ∧
    selected.cg.edges[edge]? = some e ∧ e.tail = e.head ∧
    selected.cg.nodes[pos]? = some group ∧
    (e.tail = pos ∨ selected.spec = none ∧ group.border = -2 ∧
      WellFormed (inputModel inp o) ∧ framedParents inp = true ∧
      ∃ exactResult, layoutX exactIds inp o = .ok exactResult)

private theorem r8b_loop_slot_nonneg {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    0 ≤ cg'.slot := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  have hnorm := stages.hNorm
  unfold NormalizeImpl.normalize at hnorm
  split at hnorm
  · simp at hnorm
  · rename_i slot hs
    split at hnorm
    · rename_i hc
      by_cases hz : cg'.slot = 0
      · omega
      · have he : cg'.slot = slot := by
          simpa [NormalizeImpl.slotOf, hz] using hs
        rw [he]
        exact hc.2.2
    · simp at hnorm

private theorem r8b_loop_stack_contained {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {edge : Nat} {e : Edge} {env raw : Rect}
    (hslot : 0 ≤ cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hedge : cg.edges[edge]? = some e) (hloop : e.tail = e.head)
    (henv : labelEnvelope P cg run labels edge e = some env)
    (hstack : raw ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels labels e.decl).map fun l => (l.width, l.height))) :
    (loopFootprintExt cg run labels e.tail).Contained raw := by
  have hfoot : (loopFootprintExt cg run labels e.tail).Contained env := by
    unfold labelEnvelope at henv
    obtain ⟨_, _, hplacement⟩ := Option.bind_eq_some_iff.mp henv
    have hsame : (e.tail == e.head) = true := by simp [hloop]
    cases hexact : run.exact.contains e.tail
    · simp only [hsame, hexact] at hplacement
      exact X_loopEnvelope_containedExt hslot hlab hexact hedge hloop
        (Option.some.inj hplacement).symm
    · simp only [hsame, hexact] at hplacement
      exact X_loopExactEnvelope_containedExt hslot hlab hedge hloop
        (Option.some.inj hplacement).symm hexact
  obtain ⟨hw, hh⟩ := labelEnvelope_loop_size hloop henv
  have hsizes : ∀ size ∈ (routeLabels labels e.decl).map (fun l => (l.width, l.height)),
      0 ≤ size.1 ∧ 0 ≤ size.2 := by
    intro size hsize
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hsize
    have hn := hlab l (List.mem_filter.mp hl).1
    exact ⟨hn.1, hn.2.1⟩
  rw [stackSize_width_eq] at hw
  rw [stackSize_height_eq] at hh
  obtain ⟨_, _, hsub⟩ := Labels.stackRects_contained env cg.slot hslot hsizes
    (Int.le_of_eq hw.symm) (Int.le_of_eq hh.symm) raw hstack
  exact Rect.Contained.trans hfoot hsub

private theorem r8b_demoted_loop_hull_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res exactResult : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part)
    (hpart : part ∈ execution.componentsAcc.parts)
    (hnone : selected.spec = none) (hok : layoutX exactIds inp o = .ok exactResult)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {edge pos : Nat} {e : Edge} {group : Node}
    (hedge : selected.cg.edges[edge]? = some e) (hloop : e.tail = e.head)
    (hgroup : selected.cg.nodes[pos]? = some group) (hborder : group.border = -2) :
    Disjoint (frameRect execution.params selected.cg selected.run pos)
      (loopFootprintExt selected.cg selected.run execution.measured e.tail) ∨
    (frameRect execution.params selected.cg selected.run pos).StrictInside
      (loopFootprintExt selected.cg selected.run execution.measured e.tail) := by
  have hr := selected.run_eq
  rw [hnone, componentRunR_none, componentCandidateR_none] at hr
  change (componentRunX execution.params (exactDecls exactIds inp)
    (componentCandidate execution.graph part.1 selected.candidate)
    execution.measured (candidateOrder selected.candidate) >>=
      fun run => Except.ok (componentCandidate execution.graph part.1 selected.candidate, run)) =
    .ok (selected.cg, selected.run) at hr
  obtain ⟨run, hrun, hout⟩ := bind_ok hr
  have hpair := Except.ok.inj hout
  have hcg : selected.cg = componentCandidate execution.graph part.1 selected.candidate :=
    (congrArg Prod.fst hpair).symm
  have hrunEq : run = selected.run := congrArg Prod.snd hpair
  rw [hrunEq] at hrun
  obtain ⟨x⟩ := layoutX_sceneExecution hok
  have hp : x.params = execution.params := Except.ok.inj (x.checked.symm.trans execution.checked)
  have hm : x.metric = execution.metric := Except.ok.inj (x.metric_eq.symm.trans execution.metric_eq)
  have hl : x.lines = execution.lines := by
    have h := x.lines_eq
    rw [hp, hm] at h
    exact Except.ok.inj (h.symm.trans execution.lines_eq)
  have hmeasured : x.measured = execution.measured := by
    have h := x.measured_eq
    rw [hp, hm] at h
    exact Except.ok.inj (h.symm.trans execution.measured_eq)
  have hg0 : x.graph0 = execution.graph0 := by
    have h := x.graph0_eq
    rw [hp, hl] at h
    exact Except.ok.inj (h.symm.trans execution.graph0_eq)
  have hg : x.graph = execution.graph := by
    have h := x.graph_eq
    rw [hp, hmeasured, hg0] at h
    exact Except.ok.inj (h.symm.trans execution.graph_eq)
  have hcomp : part.1 ∈ components x.graph := by
    rw [hg, ← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem hpart
  have hxcg : selected.cg = componentCandidate x.graph part.1 selected.candidate := by
    rwa [hg]
  have hxrun : componentRunX x.params (exactDecls exactIds inp) selected.cg
      x.measured (candidateOrder selected.candidate) = .ok selected.run := by
    rw [hxcg, hp, hmeasured, hg]
    exact hrun
  have hself : ∃ loop ∈ selected.cg.edges, loop.tail = e.tail ∧ loop.head = e.tail :=
    ⟨e, List.mem_of_getElem? hedge, rfl, hloop.symm⟩
  have hpos := (List.getElem?_eq_some_iff.mp hgroup).1
  have hclear := exactNonforward_groupHullExtW exactIds inp o exactResult x hwf hfp
    part.1 selected.candidate selected.run (candidateOrder selected.candidate)
    selected.cg e.tail pos hcomp hxcg hxrun hself hpos group hgroup hborder
  simpa only [hp, hmeasured] using hclear

/-- Clearance of the stored label and frame using their common part-placement shift. -/
theorem r8b_selectedLoopFrame_part_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part)
    (hpart : part ∈ execution.componentsAcc.parts) {index pos : Nat} {stored frame : Rect}
    (hlabel : (index, stored) ∈ part.2.labels) (hframe : part.2.rects[pos]? = some frame)
    (hbranch : R8b_EmittedSelectedLoopFrameAt selected index pos) :
    Disjoint frame stored ∨ frame.StrictInside stored := by
  obtain ⟨_, label, edge, e, group, _, _, hfind, hfindEdge, hedge, hloop, hgroup, hscope⟩ := hbranch
  let bounds := placeBoundsX execution.params selected.cg selected.run execution.measured
    selected.loops
  let translate := shiftRect (0 - bounds.minX) (-bounds.minY)
  have hmapped : (index, stored) ∈
      (placedLabels execution.params selected.cg selected.run execution.measured).map
        (fun q => (q.1, translate q.2)) := by
    rw [selected.part_eq] at hlabel
    exact hlabel
  obtain ⟨⟨i, raw⟩, hraw, hstored⟩ := List.mem_map.mp hmapped
  change (i, translate raw) = (index, stored) at hstored
  simp only [Prod.mk.injEq] at hstored
  obtain ⟨hi, hstored⟩ := hstored
  subst i
  have hnodup := measureLabels_index_nodup execution.measured_eq
  obtain ⟨ml, k, actual, env, rect, hml, hi, hk, ha, henv, hstack, hrect⟩ :=
    placedLabels_pair_inv hnodup hraw
  have hindex : label.index = index := by
    simpa only [beq_iff_eq] using List.find?_some hfind
  have hmlEq := measured_eq_of_index_eq execution.measured hnodup ml label hml
    (List.mem_of_find?_eq_some hfind) (hi.trans hindex.symm)
  subst ml
  have heq : k = edge := Option.some.inj (hk.symm.trans hfindEdge)
  subst k
  have heq : actual = e := Option.some.inj (ha.symm.trans hedge)
  subst actual
  have hstackMem := (List.of_mem_zip (List.mem_of_find?_eq_some hstack)).2
  rw [← hrect] at hstackMem
  have hcont := r8b_loop_stack_contained (r8b_loop_slot_nonneg selected.run_eq)
    execution.measured_nonnegR hedge hloop henv hstackMem
  have hpos := (List.getElem?_eq_some_iff.mp hgroup).1
  have hframe' : part.2.rects[pos]? =
      some (translate (frameRect execution.params selected.cg selected.run pos)) := by
    rw [selected.part_eq]
    unfold placeComponentExact
    change (((List.range selected.cg.nodes.length).map
      (frameRect execution.params selected.cg selected.run)).map translate)[pos]? = _
    simp only [List.getElem?_map, List.getElem?_range hpos, Option.map_some]
  rw [Option.some.inj (hframe.symm.trans hframe'), ← hstored]
  rcases hscope with hown | ⟨hnone, hborder, hwf, hfp, exactResult, hok⟩
  · have hleft := hcont.1
    change (frameRect execution.params selected.cg selected.run e.tail).x +
      (frameRect execution.params selected.cg selected.run e.tail).w ≤ raw.x at hleft
    rw [hown] at hleft
    exact Or.inl (disjoint_shiftRect (rect_disjoint_of_x (Or.inl hleft)))
  · rcases r8b_demoted_loop_hull_clear selected hpart hnone hok hwf hfp hedge hloop
        hgroup hborder with hd | hs
    · exact Or.inl (disjoint_shiftRect (disjoint_contained_right hd hcont))
    · have hstrict : (frameRect execution.params selected.cg selected.run pos).StrictInside raw := by
        exact ⟨Int.lt_of_lt_of_le hs.1 hcont.1,
          Int.lt_of_le_of_lt hcont.2.1 hs.2.1,
          Int.lt_of_lt_of_le hs.2.2.1 hcont.2.2.1,
          Int.lt_of_le_of_lt hcont.2.2.2 hs.2.2.2⟩
      exact Or.inr (strictInside_shiftRect hstrict)

/-- The prior residual with just the proved selected self-loop pairs removed. -/
def R_ExecutedPartFrameCoresB8LoopRemainder (exactIds : List String)
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
        ¬ R8b_EmittedSelectedLoopFrameAt selected index pos →
        Disjoint frame stored ∨ frame.StrictInside stored) ∧
      PartCaptionFrameClear execution.params inp o execution.lines part

theorem R_executedPartFrameCoresB8DemotedRemainder_iff_loopRemainder
    (exactIds : List String) (idSets : List (String × List String)) :
    R_ExecutedPartFrameCoresB8OuterReservedChildDemotedRemainder exactIds idSets ↔
      R_ExecutedPartFrameCoresB8LoopRemainder exactIds idSets := by
  classical
  constructor
  · intro old inp o res execution part hpart
    obtain ⟨hroute, hcaption⟩ := old execution part hpart
    refine ⟨?_, hcaption⟩
    intro selected index stored pos key src frame hlabel hkey hsrc hgroup hframe houter hchild
      hdemoted _
    exact hroute selected index stored pos key src frame hlabel hkey hsrc hgroup hframe
      houter hchild hdemoted
  · intro remaining inp o res execution part hpart
    obtain ⟨hroute, hcaption⟩ := remaining execution part hpart
    refine ⟨?_, hcaption⟩
    intro selected index stored pos key src frame hlabel hkey hsrc hgroup hframe houter hchild
      hdemoted
    by_cases hloop : R8b_EmittedSelectedLoopFrameAt selected index pos
    · exact r8b_selectedLoopFrame_part_clear selected hpart hlabel hframe hloop
    · exact hroute selected index stored pos key src frame hlabel hkey hsrc hgroup hframe
        houter hchild hdemoted hloop

#print axioms r8b_selectedLoopFrame_part_clear
#print axioms R_executedPartFrameCoresB8DemotedRemainder_iff_loopRemainder

end Elegant.Layered.PipelineImpl

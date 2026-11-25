import Elegant.Layered.RegionFlatC6SamePart
import Elegant.Layered.RegionActiveOrderProof
import Elegant.Layered.RegionFlatC6

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

structure R6_SelectedLoopPartR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (c : Nat) (part : List Nat × Part) where
  candidate : Nat
  used : Option RegionSpec
  cg : Graph
  run : Run
  loops : List (Nat × LoopPlacement)
  area : Int
  hPart : execution.componentsAcc.parts[c]? = some part
  hComp : part.1 ∈ components execution.graph
  hChosen : ∃ chosen,
    Portfolio.portfolio o.thoroughness
      (componentTrialR execution.params exactIds (r7Spec idSets o execution.params execution.lines)
        inp o execution.graph part.1 execution.measured) = .ok chosen ∧ chosen.value = (cg, run)
  hResolved : ∃ rs,
    newComponentRegions (r7Spec idSets o execution.params execution.lines) execution.params inp
      (componentGraph execution.graph part.1) = .ok rs ∧
    used = if rs.isSome then r7Spec idSets o execution.params execution.lines else none
  hRun : componentRunR execution.params (exactDecls exactIds inp) used inp
    (componentCandidateR used execution.graph part.1 candidate)
    execution.measured (candidateOrder candidate) = .ok (cg, run)
  hLoops : componentLoops execution.params cg run execution.measured = .ok loops
  hPlaced : part.2 = { placeComponentExact execution.params cg run 0 execution.measured loops
    with area := area }

theorem SceneExecutionR.selectedLoopPartR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {c : Nat} {part : List Nat × Part}
    (hpart : execution.componentsAcc.parts[c]? = some part) :
    Nonempty (R6_SelectedLoopPartR execution c part) := by
  obtain ⟨hparts, hgeometry⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  have hmem := List.mem_of_getElem? hpart
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hmem
  obtain ⟨candidate, chosen, cg, run, loops, area, used, _, hchosen, hvalue, hres, hrun,
    hloops, hplaced⟩ := hgeometry part hmem
  exact ⟨⟨candidate, used, cg, run, loops, area, hpart, hcomp, ⟨chosen, hchosen, hvalue⟩,
    hres, hrun, hloops, hplaced⟩⟩

private theorem candidateR_nodes (spec : Option RegionSpec) (g : Graph) (comp : List Nat)
    (k : Nat) : (componentCandidateR spec g comp k).nodes = (componentGraph g comp).nodes := by
  cases spec
  · exact componentCandidate_nodes g comp k
  · rfl

private theorem candidateR_slot (spec : Option RegionSpec) (g : Graph) (comp : List Nat)
    (k : Nat) : (componentCandidateR spec g comp k).slot = g.slot := by
  cases spec with
  | some _ => rfl
  | none =>
    change (componentCandidate g comp k).slot = g.slot
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl

private theorem rankedR_slot {rm : ComponentRegions} {candidate cg : Graph}
    {ranks : List Int} {budget : Bool}
    (h : rankEquivalentR rm candidate = .ok (ranks, cg, budget)) : cg.slot = candidate.slot := by
  unfold rankEquivalentR at h
  dsimp only at h
  split at h
  · simp [bind, Except.bind] at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    exact (congrArg (fun q : List Int × Graph × Bool => q.2.1.slot) (Except.ok.inj h)).symm

private theorem selectedGraphR_nodes_slot {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions}
    (h : componentRunR P exact spec inp candidate labels order = .ok (cg, run)) :
    cg.nodes = candidate.nodes ∧ cg.slot = candidate.slot := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages h
  rcases stages.hRank with ⟨_, _, _, _, hcg, _⟩ | ⟨_, _, hrank⟩
  · rw [hcg]; exact ⟨rfl, rfl⟩
  · exact ⟨rankEquivalentR_nodes_eq hrank, rankedR_slot hrank⟩

private theorem regionGraph_slot_pos {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) : 0 < e.graph.slot := by
  have hg := e.graph_eq
  unfold exactGraph at hg
  obtain ⟨_, _, hg⟩ := bind_ok hg
  have hs : e.graph.slot = e.graph0.slot := by rw [← Except.ok.inj hg]
  obtain ⟨_, _, _, _, _, _, hslot, hprep, _⟩ :=
    measuredGraph_loop_reservation_before_prepare e.graph0_eq
  have hs0 : e.graph0.slot = e.params.slot := by rw [hprep]; exact hslot
  rw [hs, hs0]
  have hp := (checkedParams_valid e.checked).2.2.1
  omega

private theorem regionCandidate_resolution {spec : Option RegionSpec} {P : Params}
    {inp : Input} {g : Graph} {comp : List Nat} {k : Nat} :
    newComponentRegions spec P inp (componentCandidateR spec g comp k) =
      newComponentRegions spec P inp (componentGraph g comp) := by
  unfold newComponentRegions
  cases spec with
  | none => rfl
  | some s =>
    have hn := candidateR_nodes (some s) g comp k
    simp only [clusterRows, hn]

private theorem laneEntry_length {α : Type} (xs : List α) (i : Nat) (a : α) :
    (setAt xs i a).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [setAt, ih]

private theorem foldlM_preserved {α β : Type} (step : α → β → Except LayoutError α)
    (inv : α → Prop) (hstep : ∀ {a b out}, inv a → step a b = .ok out → inv out) :
    ∀ (xs : List β) {start finish : α}, inv start →
      xs.foldlM step start = .ok finish → inv finish := by
  intro xs
  induction xs with
  | nil =>
    intro start finish hs h
    rw [List.foldlM_nil] at h
    rwa [← Except.ok.inj h]
  | cons b bs ih =>
    intro start finish hs h
    rw [List.foldlM_cons] at h
    obtain ⟨_, hnext, hrest⟩ := bind_ok h
    exact ih (hstep hs hnext) hrest

private theorem allocateGroup_lane_length {pl : RegionPlacement} {P : Params}
    {widths : List Int} {g : Nat} {before after : List Int × List Int × List (Option Int)}
    (h : allocateGroup pl P widths g before = .ok after) : after.2.2.length = before.2.2.length := by
  rcases before with ⟨x, lefts, lanes⟩
  unfold allocateGroup at h
  dsimp only at h
  obtain ⟨placed, _, h⟩ := bind_ok h
  obtain ⟨finish, hlanes, h⟩ := bind_ok h
  rw [← Except.ok.inj h]
  dsimp only
  apply foldlM_preserved _ (fun q : List (Option Int) × Int => q.1.length = lanes.length)
    _ _ rfl hlanes
  intro q edge out hlen hq
  let cursor := q.2 + P.slot
  change (if I32_MAX < cursor then Except.error LayoutError.overflow
    else Except.ok (setAt q.1 edge (some cursor),
      cursor + P.slot + pl.buckets.laneWidth.getD g 0)) = .ok out at hq
  split at hq
  · cases hq
  · rw [← Except.ok.inj hq]
    exact (laneEntry_length _ _ _).trans hlen

private theorem allocatePl_lane_length {pl : RegionPlacement} {P : Params} {xs out : List Int}
    {allocation : RegionAllocation} (h : allocatePl pl P xs = .ok (allocation, out)) :
    allocation.lanes.length = pl.p.chains.length := by
  unfold allocatePl at h
  obtain ⟨finish, hfold, h⟩ := bind_ok h
  have hlen : finish.2.2.length = pl.p.chains.length := by
    apply foldlM_preserved _ (fun state : List Int × List Int × List (Option Int) =>
      state.2.2.length = pl.p.chains.length) _ _ List.length_replicate hfold
    intro state g next hstate hstep
    exact (allocateGroup_lane_length hstep).trans hstate
  have hEq := congrArg (fun p : RegionAllocation × List Int => p.1.lanes.length) (Except.ok.inj h)
  exact hEq.symm.trans hlen

def R6_ActiveLoopRoutingR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) : Prop :=
  ∃ spec regions reserved, s.used = some spec ∧
    newComponentRegions s.used e.params inp
      (componentCandidateR s.used e.graph part.1 s.candidate) = .ok (some regions) ∧
    reserved.length = s.cg.edges.length ∧ reserved.isEmpty = false ∧
    routeWithLanesR e.params.slot s.run.proper s.run.layers s.run.xs (s.cg.edges.map (·.reversed))
      (s.cg.edges.map fun ed => (stackSize s.cg.slot (routeLabels e.measured ed.decl)).width)
      reserved = .ok s.run.lanes

set_option maxHeartbeats 900000 in
theorem R6_SelectedLoopPartR.dispatch {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) {i : Nat} {edge : Edge}
    (hedge : s.cg.edges[i]? = some edge) :
    (s.used = none ∧ s.cg = componentCandidate e.graph part.1 s.candidate ∧
      componentRunX e.params (exactDecls exactIds inp) s.cg e.measured
        (candidateOrder s.candidate) = .ok s.run) ∨
    R6_ActiveLoopRoutingR s := by
  cases hu : s.used with
  | none =>
    have hr := s.hRun
    rw [hu, componentRunR_none, componentCandidateR_none] at hr
    change (componentRunX e.params (exactDecls exactIds inp)
      (componentCandidate e.graph part.1 s.candidate) e.measured (candidateOrder s.candidate) >>=
        fun run => Except.ok (componentCandidate e.graph part.1 s.candidate, run)) =
      .ok (s.cg, s.run) at hr
    obtain ⟨run, hx, hout⟩ := bind_ok hr
    have hpair := Except.ok.inj hout
    have hcg : s.cg = componentCandidate e.graph part.1 s.candidate :=
      (congrArg Prod.fst hpair).symm
    have hrun : run = s.run := congrArg Prod.snd hpair
    refine Or.inl ⟨by first | exact hu | rfl, hcg, ?_⟩
    rw [hcg, hx, hrun]
  | some spec =>
    obtain ⟨rs, hrs, hused⟩ := s.hResolved
    have hr : ∃ regions, newComponentRegions s.used e.params inp
        (componentCandidateR s.used e.graph part.1 s.candidate) = .ok (some regions) := by
      cases rs with
      | none => simp [hu] at hused
      | some regions =>
        have hs : s.used = r7Spec idSets o e.params e.lines := by simpa using hused
        refine ⟨regions, ?_⟩
        rw [regionCandidate_resolution, hs]
        exact hrs
    obtain ⟨regions, hregions⟩ := hr
    obtain ⟨rs, _, _, _, _, p, _, _, _, reserved, placed, _, _, _, hrank⟩ :=
      componentRunR_stages s.hRun
    have hrs : rs = some regions := Except.ok.inj (hrank.hRs.symm.trans hregions)
    rcases hrank.hPlaced with ⟨hnone, _, _, _, _⟩ | ⟨rm, _, hrm, _, hcross⟩
    · rw [hrs] at hnone
      cases hnone
    have heq : rm = regions := Option.some.inj (hrm.symm.trans hrs)
    subst rm
    obtain ⟨stages⟩ := crossCoordsR_allocation_stages hcross
    have hchains : placed.chains = p.chains := (crossCoordsR_label_metadata hcross).2.2.2
    have hlen : reserved.length = s.cg.edges.length := by
      rw [stages.hLanes, allocatePl_lane_length stages.hAllocation, stages.hPlacement]
      change p.chains.length = s.cg.edges.length
      rw [← hchains, ← hrank.hCoordProper, componentRunR_coordinate_chainsR s.hRun,
        componentRunR_proper_chains_lengthR s.hRun]
    have hn : reserved.isEmpty = false := by
      cases reserved with
      | nil => simp at hlen; have hi := (List.getElem?_eq_some_iff.mp hedge).1; omega
      | cons _ _ => rfl
    refine Or.inr ⟨spec, regions, reserved, by first | exact hu | rfl, hregions, hlen, hn, ?_⟩
    rw [← hrank.hLabelWidths]
    rcases hrank.hLanes with ⟨hempty, _⟩ | ⟨_, hlane⟩
    · rw [hn] at hempty
      cases hempty
    · exact hlane

private theorem loopSceneSource {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {key : Nat} {box : Box}
    (hbox : res.scene.boxes[key]? = some box) :
    ∃ source, inp.boxes[key]? = some source ∧ box.id = source.id ∧
      box.exclusive = source.exclusive := by
  have hk := (List.getElem?_eq_some_iff.mp hbox).1
  rw [e.boxes_eq_mapR] at hk
  have hkey : key < inp.boxes.length := by
    simpa only [List.length_map, List.length_zipIdx] using hk
  rw [e.boxes_eq_mapR] at hbox
  simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hkey,
    Option.map_some, Nat.zero_add] at hbox
  have heq := (Option.some.inj hbox).symm
  exact ⟨inp.boxes[key], List.getElem?_eq_getElem hkey, congrArg Box.id heq,
    congrArg Box.exclusive heq⟩

private theorem loopExclusiveGraphSource {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hex : source.exclusive = true) :
    ∃ node, e.graph.nodes[key]? = some node ∧ node.border = 0 := by
  have hrole := wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource) hex
  have hlines := e.lines_eq
  unfold boxLines at hlines
  have hlen : e.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
  have hk : key < e.lines.length := by
    rw [hlen]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨n0, hn0, hb0⟩ := measuredGraph_exclusive_node_border_zero e.checked e.graph0_eq
    (List.getElem?_eq_getElem hk) hsource hrole
  obtain ⟨node, hn, hb, _, _⟩ := exactGraph_node_key e.graph_eq hn0
  exact ⟨node, hn, hb.trans hb0⟩

set_option maxHeartbeats 900000 in
private theorem fallbackLoopFootprint_disjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res exactResult : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) (x : SceneExecutionX exactIds inp o exactResult)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hcg : s.cg = componentCandidate e.graph part.1 s.candidate)
    (hrun : componentRunX e.params (exactDecls exactIds inp) s.cg e.measured
      (candidateOrder s.candidate) = .ok s.run)
    {owner j key : Nat} {source : ModelBox} {edge : Edge}
    (hforeign : j ≠ owner) (hedge : edge ∈ loopEdges s.cg.edges owner)
    (htail : edge.tail = owner) (hhead : edge.head = owner)
    (hkey : part.1[j]? = some key) (hsource : inp.boxes[key]? = some source)
    (hex : source.exclusive = true) (hborder : (s.cg.nodes.getD j default).border = 0) :
    Disjoint (loopFootprintExt s.cg s.run e.measured owner) (frameRect e.params s.cg s.run j) := by
  have hp : x.params = e.params := Except.ok.inj (x.checked.symm.trans e.checked)
  have hm : x.metric = e.metric := Except.ok.inj (x.metric_eq.symm.trans e.metric_eq)
  have hl : x.lines = e.lines := by
    have h := x.lines_eq
    rw [hp, hm] at h
    exact Except.ok.inj (h.symm.trans e.lines_eq)
  have hmeas : x.measured = e.measured := by
    have h := x.measured_eq
    rw [hp, hm] at h
    exact Except.ok.inj (h.symm.trans e.measured_eq)
  have hg0 : x.graph0 = e.graph0 := by
    have h := x.graph0_eq
    rw [hp, hl] at h
    exact Except.ok.inj (h.symm.trans e.graph0_eq)
  have hg : x.graph = e.graph := by
    have h := x.graph_eq
    rw [hp, hmeas, hg0] at h
    exact Except.ok.inj (h.symm.trans e.graph_eq)
  have hc : part.1 ∈ components x.graph := by rw [hg]; exact s.hComp
  have hcgX : s.cg = componentCandidate x.graph part.1 s.candidate := by rw [hg]; exact hcg
  have hrX : componentRunX x.params (exactDecls exactIds inp)
      (componentCandidate x.graph part.1 s.candidate) x.measured
      (candidateOrder s.candidate) = .ok s.run := by rw [hp, hmeas, ← hcgX]; exact hrun
  obtain ⟨edgeIndex, hedgeAt⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp hedge).1
  have hedgeX : (componentCandidate x.graph part.1 s.candidate).edges[edgeIndex]? =
      some edge := by rwa [← hcgX]
  have hborderX : ((componentCandidate x.graph part.1 s.candidate).nodes.getD j default).border =
      0 := by rwa [← hcgX]
  obtain ⟨hcovered, hreal, htailScope, hheadScope⟩ :=
    x6_loopSep_nonSelf_scopeB_holds exactIds inp o exactResult x hwf hfp part.1 s.candidate
      s.run owner j edgeIndex edge hc hborderX hrX (Ne.symm hforeign) hedgeX htail hhead
      key source hkey hsource hex
  have hEnvelope : X_LoopEnvelopeMiss exactIds := by
    have hoverlap : XLEM_GroupOverlapMiss exactIds :=
      fun inp o res execution hwf hfp => XLEM_groupOverlapMiss_holdsW exactIds
        (inp := inp) (o := o) (res := res) execution hwf hfp
    have hright := xlem_plainRightNonPlain_holds exactIds
    have hmarker := XLEG_groupMarkerOrderX_of_leaves exactIds
      (xleg_loopMarkerCoreX_holds exactIds) (xleg_loopMarkerLayerOrderX_holds exactIds)
      (xleg_loopMarkerSpanX_holds exactIds)
    exact glue_loopEnvelopeMiss exactIds (XLEM_plainReserve_holds exactIds)
      (XLEM_groupOtherRank_holds exactIds hoverlap) (XLEM_leftNonPlain_holds exactIds)
      (XLEM_plainRightMiss_holds exactIds hright) hmarker
      (glue_loopEnvOtherOwner exactIds hoverlap hright hmarker)
  have hclean := hEnvelope inp o exactResult x hwf hfp
    part.1 s.candidate s.run (candidateOrder s.candidate)
    (componentCandidate x.graph part.1 s.candidate) edgeIndex edge j hc rfl hrX hedgeX
    (htail.trans hhead.symm) hcovered hreal htailScope hheadScope
  rw [← hcgX, hmeas, htail] at hclean
  rw [plain_frame_eq_boxRect _ _ _ _ hcovered (by omega : (s.cg.nodes.getD j default).border ≠ -2)]
  exact hclean

private theorem regionLoopFootprint_rank_overlap {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {order : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp candidate labels order =
      .ok (cg, run))
    {owner j : Nat} {target : Node}
    (htarget : cg.nodes[j]? = some target) (hborder : target.border = 0)
    (hy : max (loopFootprintExt cg run labels owner).y (frameRect P cg run j).y <
      min ((loopFootprintExt cg run labels owner).y + (loopFootprintExt cg run labels owner).h)
        ((frameRect P cg run j).y + (frameRect P cg run j).h)) :
    ∀ ownerNode, cg.nodes[owner]? = some ownerNode → ownerNode.border = 0 →
      (rk run.proper.rank owner).toNat ≤ (rk run.proper.rank j).toNat ∧
      ((rk run.proper.rank owner).toNat = (rk run.proper.rank j).toNat ∨
        (frameRect P cg run owner).h < (loopFootprintExt cg run labels owner).h) := by
  intro ownerNode hnode hplain
  let a := (rk run.proper.rank owner).toNat
  let b := (rk run.proper.rank j).toNat
  let ownFrame := frameRect P cg run owner
  let targetFrame := frameRect P cg run j
  let foot := loopFootprintExt cg run labels owner
  change max foot.y targetFrame.y <
    min (foot.y + foot.h) (targetFrame.y + targetFrame.h) at hy
  have hfy : foot.y = ownFrame.y := rfl
  obtain ⟨hband, horder⟩ := componentRunR_plain_rank_bands hrun
  obtain ⟨left, hownerLayer, _, hlo, hhi⟩ := hband hnode hplain
  obtain ⟨right, htargetLayer, _, hlo', hhi'⟩ := hband htarget hborder
  change run.layers[a]? = some left at hownerLayer
  change run.layers[b]? = some right at htargetLayer
  change run.top.getD a 0 ≤ ownFrame.y at hlo
  change run.top.getD b 0 ≤ targetFrame.y at hlo'
  change ownFrame.y + ownFrame.h ≤
    run.top.getD a 0 + CoordsImpl.layerHeight run.coordinateProper left at hhi
  change targetFrame.y + targetFrame.h ≤
    run.top.getD b 0 + CoordsImpl.layerHeight run.coordinateProper right at hhi'
  have hstart : foot.y < targetFrame.y + targetFrame.h :=
    Int.lt_of_le_of_lt (Int.le_max_left _ _) (Int.lt_of_lt_of_le hy (Int.min_le_right _ _))
  have hend : targetFrame.y < foot.y + foot.h :=
    Int.lt_of_le_of_lt (Int.le_max_right _ _) (Int.lt_of_lt_of_le hy (Int.min_le_left _ _))
  rw [hfy] at hstart hend
  change a ≤ b ∧ (a = b ∨ ownFrame.h < foot.h)
  have hab : a ≤ b := by
    apply Nat.le_of_not_gt
    intro hba
    have hsep := horder hba htargetLayer hownerLayer
    exact Int.not_lt_of_ge (Int.le_trans hhi' (Int.le_trans hsep hlo)) hstart
  refine ⟨hab, ?_⟩
  by_cases hs : a = b
  · exact Or.inl hs
  · have hsep := horder (Nat.lt_of_le_of_ne hab hs) hownerLayer htargetLayer
    have hordered := Int.le_trans hhi (Int.le_trans hsep hlo')
    exact Or.inr (Int.lt_of_add_lt_add_left (Int.lt_of_le_of_lt hordered hend))

structure R6_SelectedPartPairR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {c : Nat} {part : List Nat × Part}
    (_s : R6_SelectedLoopPartR e c part)
    (i routeKey j boxKey : Nat) (pts : List Point) (rect : Rect) : Prop where
  scenePair : ∃ route box,
    res.scene.routes[routeKey]? = some route ∧ res.scene.boxes[boxKey]? = some box ∧
    box.exclusive = true ∧ box.id ∉ LayoutDump.routeScope res.scene.layoutDump route
  routeAt : part.2.routes[i]? = some (routeKey, pts)
  boxAt : (part.1.zip part.2.rects)[j]? = some (boxKey, rect)

private theorem R6_SelectedLoopPartR.edgeAt {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) {i routeKey : Nat} {pts : List Point}
    (hlocal : part.2.routes[i]? = some (routeKey, pts)) :
    ∃ edge, s.cg.edges[i]? = some edge ∧ edge.decl = routeKey := by
  rw [s.hPlaced] at hlocal
  change (placeComponentExact e.params s.cg s.run 0 e.measured s.loops).routes[i]? = _ at hlocal
  unfold placeComponentExact at hlocal
  dsimp only at hlocal
  cases hedge : s.cg.edges[i]? with
  | none =>
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_none, reduceCtorEq] at hlocal
  | some edge =>
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at hlocal
    exact ⟨edge, by first | exact hedge | rfl, hlocal.1⟩

set_option maxHeartbeats 900000 in
theorem R6_SelectedLoopPartR.loopHits_iff {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part)
    {i routeKey j boxKey : Nat} {loop : Nat × LoopPlacement} {pts : List Point} {rect : Rect}
    (hfound : s.loops.find? (fun l => l.1 == routeKey) = some loop)
    (hlocal : part.2.routes[i]? = some (routeKey, pts))
    (hentry : (part.1.zip part.2.rects)[j]? = some (boxKey, rect)) :
    Polyline.hitsRect pts rect ↔
      Polyline.hitsRect loop.2.points (frameRect e.params s.cg s.run j) := by
  obtain ⟨edge, hedge, hdecl⟩ := s.edgeAt hlocal
  have hfoundEdge : s.loops.find? (fun l => l.1 == edge.decl) = some loop := by
    rwa [hdecl]
  let bounds := placeBoundsX e.params s.cg s.run e.measured s.loops
  let dx := 0 - bounds.minX
  let dy := -bounds.minY
  let frame := frameRect e.params s.cg s.run j
  have hlocal' : part.2.routes[i]? = some (routeKey, loop.2.points.map (shiftPoint dx dy)) := by
    rw [s.hPlaced]
    change (placeComponentExact e.params s.cg s.run 0 e.measured s.loops).routes[i]? = _
    unfold placeComponentExact
    dsimp only [dx, dy, bounds, placeBoundsX]
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some, hfoundEdge,
      Option.getD_some]
    rw [hdecl]
  obtain ⟨hkey, hrect⟩ := List.getElem?_zip_eq_some.mp hentry
  have hj : j < s.cg.nodes.length := by
    rw [(selectedGraphR_nodes_slot s.hRun).1, candidateR_nodes]
    change j < (part.1.map (fun v => e.graph.nodes.getD v default)).length
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hkey).1
  have hrect' : part.2.rects[j]? = some (shiftRect dx dy frame) := by
    rw [s.hPlaced]
    change (placeComponentExact e.params s.cg s.run 0 e.measured s.loops).rects[j]? = _
    unfold placeComponentExact
    dsimp only [dx, dy, bounds, frame, placeBoundsX]
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some]
  have hpts : pts = loop.2.points.map (shiftPoint dx dy) :=
    congrArg Prod.snd (Option.some.inj (hlocal.symm.trans hlocal'))
  have hrectEq : rect = shiftRect dx dy frame := Option.some.inj (hrect.symm.trans hrect')
  rw [hpts, hrectEq, hitsRect_shift]

private theorem loopPlainFrame_cross {P : Params} {cg : Graph} {run : Run}
    {v : Nat} {src : Node} {n : ProperNode} (hsrc : cg.nodes[v]? = some src)
    (hplain : src.border = 0) (hn : run.proper.nodes[v]? = some n)
    (hx : run.xs.getD v 0 = run.coordinateXs.getD v 0) :
    (frameRect P cg run v).x = run.coordinateXs.getD v 0 - n.node.w / 2 ∧
    (frameRect P cg run v).w = n.node.w := by
  have hrect : frameRect P cg run v = nodeRect cg run v := by
    unfold frameRect
    simp [List.getD_eq_getElem?_getD, hsrc, hplain]
  rw [hrect, ← hx]
  simp [nodeRect, List.getD_eq_getElem?_getD, hn,
    Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int))]

/-- Two plain boxes in one executed owner bucket and rank. The left-hand case
needs no extent bound; the right-hand case uses the winning run's actual reserve. -/
def R6_PlainLoopSideR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part) (owner j : Nat) : Prop :=
  ∃ (spec : RegionSpec) (ownerNode targetNode : Node) (layer : List Nat) (a b : Nat),
    s.used = some spec ∧
    s.cg.nodes[owner]? = some ownerNode ∧ ownerNode.border = 0 ∧
    s.cg.nodes[j]? = some targetNode ∧ targetNode.border = 0 ∧
    ownerNode.clusterPath.getLast? = targetNode.clusterPath.getLast? ∧
    layer ∈ s.run.layers ∧ layer[a]? = some owner ∧ layer[b]? = some j ∧
    (b < a ∨ a < b ∧ ∃ (n : ProperNode), s.run.coordinateProper.nodes[owner]? = some n ∧
      (loopFootprintExt s.cg s.run e.measured owner).w ≤ (n.node.loopExtent : Int))

set_option maxHeartbeats 900000 in
private theorem plainLoopSide_separated {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    {s : R6_SelectedLoopPartR e c part} {owner j : Nat}
    (hside : R6_PlainLoopSideR s owner j) :
    RectAxisSeparated (loopFootprintExt s.cg s.run e.measured owner)
      (frameRect e.params s.cg s.run j) := by
  obtain ⟨spec, own, target, layer, a, b, hspec, hown, hpOwn, htgt, hpTgt,
    hpath, hlayer, ha, hb, hside⟩ := hside
  have hrun := s.hRun
  rw [hspec] at hrun
  obtain ⟨hgap, hrec⟩ := componentRunR_region_plain_cross_geometry hrun
  obtain ⟨nOwn, hcOwn, hpOwn', _, hxOwn⟩ := hrec hown hpOwn
  obtain ⟨nTgt, hcTgt, hpTgt', _, hxTgt⟩ := hrec htgt hpTgt
  obtain ⟨hleftO, hwidthO⟩ := loopPlainFrame_cross (P := e.params) hown hpOwn hpOwn' hxOwn
  obtain ⟨hleftT, hwidthT⟩ := loopPlainFrame_cross (P := e.params) htgt hpTgt hpTgt' hxTgt
  have heO := Int.natCast_nonneg nOwn.node.loopExtent
  have heT := Int.natCast_nonneg nTgt.node.loopExtent
  have halfWithExtent (w : Int) (extent : Nat) :
      Int.fdiv (w + 2 * (extent : Int)) 2 = w / 2 + (extent : Int) :=
    (Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 2)).trans
      (Int.add_mul_ediv_left w (extent : Int) (by decide : (2 : Int) ≠ 0))
  rcases hside with hleft | ⟨hright, n, hn, hext⟩
  · have hsep := componentRunR_region_same_owner_separated hrun hlayer hleft hb ha
      htgt hown hpTgt hpOwn hpath.symm
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcOwn, hcTgt, halfWithExtent] at hsep
    refine Or.inr (Or.inl ?_)
    change (frameRect e.params s.cg s.run j).x + (frameRect e.params s.cg s.run j).w ≤
      (frameRect e.params s.cg s.run owner).x + (frameRect e.params s.cg s.run owner).w
    rw [hleftO, hwidthO, hleftT, hwidthT]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, yt, _, stages⟩ := componentRunR_stages hrun
    obtain ⟨y, top⟩ := yt
    have hsizes : CoordsImpl.sizesNonneg s.run.coordinateProper = true := by
      rw [stages.hCoordProper]
      exact (CoordsImpl.rankCoordsWith_spec stages.hYt).2.2.2.2.1
    have hownerWidth := (sizesNonneg_lookup hsizes owner nOwn hcOwn).1
    omega
  · have heq := Option.some.inj (hn.symm.trans hcOwn)
    subst n
    have hsep := componentRunR_region_same_owner_separated hrun hlayer hright ha hb
      hown htgt hpOwn hpTgt hpath
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcOwn, hcTgt, halfWithExtent] at hsep
    refine Or.inl ?_
    change (frameRect e.params s.cg s.run owner).x + (frameRect e.params s.cg s.run owner).w +
      (loopFootprintExt s.cg s.run e.measured owner).w ≤ (frameRect e.params s.cg s.run j).x
    rw [hleftO, hwidthO, hleftT]
    omega

def emittedLoopBoundsR (pts : List Point) : Rect :=
  let b := boundsOf [] pts
  ⟨b.minX, b.minY, b.right - b.minX, b.bottom - b.minY⟩

private theorem emittedLoopBoundsR_contains {pts : List Point} {p : Point} (hp : p ∈ pts) :
    PointIn (emittedLoopBoundsR pts) p := by
  obtain ⟨hx, hr, hy, hb⟩ := boundsOf_contains_point [] pts p hp
  unfold PointIn emittedLoopBoundsR
  dsimp only
  exact ⟨hx, by omega, hy, by omega⟩

/-- Only a selected placement's emitted loop points must miss the foreign
frame. The footprint and the point extrema only select unresolved pairs. -/
def R6_SelectedLoopPairResidualR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {c : Nat} {part : List Nat × Part}
    (s : R6_SelectedLoopPartR e c part)
    {i routeKey j boxKey : Nat} {pts : List Point} {rect : Rect}
    (_pair : R6_SelectedPartPairR e s i routeKey j boxKey pts rect)
    {loop : Nat × LoopPlacement}
    (_hfound : s.loops.find? (fun l => l.1 == routeKey) = some loop) : Prop :=
  ∀ {owner : Nat} {origin : Edge},
    origin ∈ loopEdges s.cg.edges owner → loop.1 = origin.decl →
    j ≠ owner → ¬ R6_PlainLoopSideR s owner j →
    (R6_ActiveLoopRoutingR s ∨ ¬ ∃ exactResult, layoutX exactIds inp o = .ok exactResult) →
    ∀ {target : Node}, s.cg.nodes[j]? = some target → target.border = 0 →
    let frame := frameRect e.params s.cg s.run j
    let foot := loopFootprintExt s.cg s.run e.measured owner
    0 < frame.w → 0 < frame.h → foot.meetsInterior frame →
    ¬ RectAxisSeparated (emittedLoopBoundsR loop.2.points) frame →
    (∀ ownerNode, s.cg.nodes[owner]? = some ownerNode → ownerNode.border = 0 →
      (rk s.run.proper.rank owner).toNat ≤ (rk s.run.proper.rank j).toNat ∧
      ((rk s.run.proper.rank owner).toNat = (rk s.run.proper.rank j).toNat ∨
        (frameRect e.params s.cg s.run owner).h < foot.h)) →
    ¬ Polyline.hitsRect loop.2.points frame

def R6_SelectedLoopPolylineClearanceR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ {c : Nat} {part : List Nat × Part} (s : R6_SelectedLoopPartR e c part)
    {i routeKey j boxKey : Nat} {pts : List Point} {rect : Rect}
    (pair : R6_SelectedPartPairR e s i routeKey j boxKey pts rect)
    {loop : Nat × LoopPlacement}
    (hfound : s.loops.find? (fun l => l.1 == routeKey) = some loop),
    R6_SelectedLoopPairResidualR s pair hfound

set_option maxHeartbeats 1200000 in
theorem SceneExecutionR.samePartSelectedLoop_miss
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {c : Nat} {part : List Nat × Part} (s : R6_SelectedLoopPartR e c part)
    {i routeKey j boxKey : Nat} {loop : Nat × LoopPlacement} {pts : List Point} {rect : Rect}
    (pair : R6_SelectedPartPairR e s i routeKey j boxKey pts rect)
    (hfound : s.loops.find? (fun l => l.1 == routeKey) = some loop)
    (hclear : R6_SelectedLoopPairResidualR s pair hfound) :
    ¬ Polyline.hitsRect pts rect := by
  classical
  rw [s.loopHits_iff hfound pair.routeAt pair.boxAt]
  let frame := frameRect e.params s.cg s.run j
  obtain ⟨edge, hedge, _⟩ := s.edgeAt pair.routeAt
  obtain ⟨hkey, _⟩ := List.getElem?_zip_eq_some.mp pair.boxAt
  have hnodes := selectedGraphR_nodes_slot s.hRun
  have hslot : 0 < s.cg.slot := by
    rw [hnodes.2, candidateR_slot]
    exact regionGraph_slot_pos e
  obtain ⟨owner, _, origin, horigin, hloopDecl, htail, hhead, hw, hh, hpoints⟩ :=
    componentLoops_entry_in_footprintExt s.hLoops hslot (List.mem_of_find?_eq_some hfound)
  let foot := loopFootprintExt s.cg s.run e.measured owner
  by_cases howner : j = owner
  · have hsep : RectAxisSeparated foot frame := Or.inr (Or.inl (by
      let rightEdge (v : Nat) := (frameRect e.params s.cg s.run v).x +
        (frameRect e.params s.cg s.run v).w
      change rightEdge j ≤ rightEdge owner
      exact Int.le_of_eq (congrArg rightEdge howner)))
    exact Polyline.not_hits_of_allMiss (allSegsMiss_of_pointIn_of_separated hsep _ hpoints)
  by_cases hpositive : 0 < frame.w ∧ 0 < frame.h
  case neg => exact Polyline.not_hits_of_zero (by omega : frame.w ≤ 0 ∨ frame.h ≤ 0)
  by_cases hside : R6_PlainLoopSideR s owner j
  · exact Polyline.not_hits_of_allMiss
      (allSegsMiss_of_pointIn_of_separated (plainLoopSide_separated hside) _ hpoints)
  by_cases hoverlap : foot.meetsInterior frame
  case neg => exact polyline_in_box_misses_disjoint hw hh hpoints hoverlap
  by_cases hhull : RectAxisSeparated (emittedLoopBoundsR loop.2.points) frame
  · exact Polyline.not_hits_of_allMiss
      (allSegsMiss_of_pointIn_of_separated hhull _ (fun _ hp => emittedLoopBoundsR_contains hp))
  obtain ⟨_, _, _, hbox, hex, _⟩ := pair.scenePair
  obtain ⟨source, hsource, _, hsourceEx⟩ := loopSceneSource e hbox
  have hexSource := hsourceEx.symm.trans hex
  obtain ⟨target, hnode, hzero⟩ := loopExclusiveGraphSource e hwf hsource hexSource
  have htarget : s.cg.nodes[j]? = some target := by
    rw [hnodes.1]
    exact component_node_lookupR hkey hnode
  have hborder : (s.cg.nodes.getD j default).border = 0 := by
    simp only [List.getD_eq_getElem?_getD, htarget, Option.getD_some, hzero]
  have hmiss
      (hbranch : R6_ActiveLoopRoutingR s ∨
        ¬ ∃ exactResult, layoutX exactIds inp o = .ok exactResult) :
      ¬ Polyline.hitsRect loop.2.points frame :=
    hclear horigin hloopDecl howner hside hbranch htarget hzero
      hpositive.1 hpositive.2 hoverlap hhull
      (regionLoopFootprint_rank_overlap s.hRun htarget hzero hoverlap.2)
  rcases s.dispatch hedge with ⟨_, hcg, hrun⟩ | hactive
  · by_cases hx : ∃ exactResult, layoutX exactIds inp o = .ok exactResult
    · obtain ⟨_, h⟩ := hx
      obtain ⟨x⟩ := layoutX_sceneExecution h
      exact polyline_in_box_misses_disjoint hw hh hpoints
        (fallbackLoopFootprint_disjoint s x hwf hfp hcg hrun howner horigin htail hhead
          hkey hsource hexSource hborder)
    · exact hmiss (Or.inr hx)
  · exact hmiss (Or.inl hactive)

/-- The original same-part condition on the non-loop dispatch arm, unchanged
except for requiring the actual failed loop lookup. -/
def R6_SelectedChainPartClearanceR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ {c : Nat} {part : List Nat × Part} (s : R6_SelectedLoopPartR e c part)
    {i routeKey j boxKey : Nat} {pts : List Point} {rect : Rect},
    R6_SelectedPartPairR e s i routeKey j boxKey pts rect →
    s.loops.find? (fun l => l.1 == routeKey) = none →
    ¬ Polyline.hitsRect pts rect

set_option maxHeartbeats 900000 in
theorem SceneExecutionR.selectedChainPartClearance_of_chainCaseW
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hframe : FrameClearanceSeam inp o res)
    (hbridge : R6_RouteScopeBridgeW exactIds idSets)
    (hchain : R6_ChainCaseW exactIds idSets) :
    R6_SelectedChainPartClearanceR e := by
  intro c part s i routeKey j boxKey pts rect pair hfound
  obtain ⟨route, box, hroute, hbox, hex, hscope⟩ := pair.scenePair
  obtain ⟨edge, hedge, hdecl⟩ := s.edgeAt pair.routeAt
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [e.scene_eq]
    exact sceneOf_routes_length e.params inp o e.lines e.packedAcc e.measured
  have hrkey : routeKey < inp.routes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hroute).1
  obtain ⟨packed, hpacked, _⟩ := packAcc_components_disjoint e.packed_eq
  have hcount : packed.boxes.length = e.componentsAcc.parts.length := by
    simpa only [List.length_map] using Pack.pack_count hpacked
  have hc : c < packed.boxes.length := by
    rw [hcount]
    exact (List.getElem?_eq_some_iff.mp s.hPart).1
  have hselected : (e.componentsAcc.parts.zip packed.boxes)[c]? =
      some (part, packed.boxes[c]'hc) :=
    List.getElem?_zip_eq_some.mpr ⟨s.hPart, List.getElem?_eq_getElem hc⟩
  have hchainLookup : s.loops.find? (fun l => l.1 == edge.decl) = none := by
    rwa [hdecl]
  have hmiss := hchain e hwf hfp hframe hbridge
    (List.mem_of_getElem? hroute) (List.mem_of_getElem? hbox) hex hscope hroute hrkey
    s.area hpacked hselected s.hRun s.hLoops s.hPlaced hedge hdecl hchainLookup
  have hpoints := e.chosenPartRoute_points hpacked hselected pair.routeAt hroute
  have hbound := (List.getElem?_eq_some_iff.mp hbox).1
  rw [e.boxes_eq_mapR] at hbound
  have hk : boxKey < inp.boxes.length := by
    simpa only [List.length_map, List.length_zipIdx] using hbound
  have hsize : boxKey < e.componentsAcc.rects.size := by
    rw [e.components_rects_sizeR]
    exact hk
  have hread := actual_components_packed_rect_valueR (by rfl) e.components_eq
    e.packed_eq packed hpacked hselected pair.boxAt hsize default
  rw [e.boxes_eq_mapR] at hbox
  simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hk,
    Option.map_some, Nat.zero_add, hread] at hbox
  have hrect := congrArg Box.rect (Option.some.inj hbox).symm
  rw [hpoints, hrect, hitsRect_shift_orient, hitsRect_shift] at hmiss
  exact hmiss

theorem SceneExecutionR.samePartClearance_iff_selectedChain_loopPolyline
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
    R6_SamePartClearance e ↔
      R6_SelectedChainPartClearanceR e ∧ R6_SelectedLoopPolylineClearanceR e := by
  constructor
  · intro hclear
    have hpair {c : Nat} {part : List Nat × Part} (s : R6_SelectedLoopPartR e c part)
        {i routeKey j boxKey : Nat} {pts : List Point} {rect : Rect}
        (pair : R6_SelectedPartPairR e s i routeKey j boxKey pts rect) :
        ¬ Polyline.hitsRect pts rect := by
      obtain ⟨_, _, hroute, hbox, hex, hscope⟩ := pair.scenePair
      exact hclear hroute hbox hex hscope s.hPart pair.routeAt pair.boxAt
    constructor
    · intro c part s i routeKey j boxKey pts rect p _hfound
      exact hpair s p
    · intro c part s i routeKey j boxKey pts rect p loop hfound
      intro owner origin _horigin _hdecl _howner _hside _hbranch target _htarget _hplain
        _frame _foot _hw _hh _hoverlap _hhull _hrank
      intro hhit
      exact hpair s p ((s.loopHits_iff hfound p.routeAt p.boxAt).mpr hhit)
  · rintro ⟨hchain, hloop⟩ routeKey boxKey route box hroute hbox hex hscope c part hpart
      i j pts rect hlocal hentry
    obtain ⟨s⟩ := e.selectedLoopPartR hpart
    have p : R6_SelectedPartPairR e s i routeKey j boxKey pts rect :=
      ⟨⟨route, box, hroute, hbox, hex, hscope⟩, hlocal, hentry⟩
    cases hfound : s.loops.find? (fun l => l.1 == routeKey) with
    | none => exact hchain s p hfound
    | some _ => exact e.samePartSelectedLoop_miss hwf hfp s p hfound (hloop s p hfound)

def R6_ReindexedSelectedClearance (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    FixedSizesPositive inp → FrameClearanceSeam inp o res →
    layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
    ∀ (e : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res),
      R6_SelectedChainPartClearanceR e ∧ R6_SelectedLoopPolylineClearanceR e

theorem r6_reindexedSamePart_iff_selectedClearance (exactIds : List String)
    (idSets : List (String × List String)) :
    R6_ReindexedSamePartClearance exactIds idSets ↔ R6_ReindexedSelectedClearance exactIds idSets := by
  constructor
  · intro old inp o res hwf hfp hfix hframe hok e
    exact (e.samePartClearance_iff_selectedChain_loopPolyline hwf hfp).mp
      (old inp o res hwf hfp hfix hframe hok e)
  · intro selected inp o res hwf hfp hfix hframe hok e
    exact (e.samePartClearance_iff_selectedChain_loopPolyline hwf hfp).mpr
      (selected inp o res hwf hfp hfix hframe hok e)

theorem flatC6B_layoutRIds_reindex_iff_selectedClearance (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC6B (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) ↔
      R6_ReindexedSelectedClearance exactIds idSets :=
  (flatC6B_layoutRIds_reindex_iff_samePart exactIds idSets).trans
    (r6_reindexedSamePart_iff_selectedClearance exactIds idSets)

end Elegant.Layered.PipelineImpl

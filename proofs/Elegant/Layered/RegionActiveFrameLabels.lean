import Elegant.Layered.RegionBucketBounds
import Elegant.Layered.RegionPartFrameCores
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.RegionC5Boundary
import Elegant.Layered.RegionFlatC8bWProof

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

theorem routeWithLanesR_label_lane_origin {slot : Int} {p : Proper}
    {layers : List (List Nat)} {xs : List Int} {reversed : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {routing : RouteImpl.LaneRouting}
    (h : routeWithLanesR slot p layers xs reversed widths reserved = .ok routing)
    {lane : RouteImpl.ReversedLane} (hm : lane ∈ routing.runs) :
    match reserved.getD lane.original none with
    | some x => lane.lane = x
    | none => RouteImpl.laneRight p xs + slot ≤ lane.lane := by
  obtain ⟨base, _, hs, hplan⟩ := routeWithLanesR_spec h
  rw [hplan] at hm
  change lane ∈ plannedLanesR slot p base xs reversed widths reserved at hm
  obtain ⟨edge, index, _, rfl⟩ := rcbPlannedLanesR_mem hm
  let maxLabel := (List.range reversed.length).foldl (fun m i =>
    if reversed.getD i false then max m (widths.getD i 0) else m) 0
  let fallback : Int := ((RouteImpl.laneOriginals p reversed).take index).foldl (fun n i =>
    if (reserved.getD i none).isNone then n + 1 else n) 0
  have hmax : 0 ≤ maxLabel := by
    unfold maxLabel
    exact OrderImpl.foldl_inv (fun m : Int => 0 ≤ m) _ _ _ (by decide)
      (fun m hm i _ => by split <;> omega)
  have hfallback : 0 ≤ fallback := by
    unfold fallback
    exact OrderImpl.foldl_inv (fun n : Int => 0 ≤ n) _ _ _ (by decide)
      (fun n hn i _ => by split <;> omega)
  change (match reserved.getD edge none with
    | some x => (makeLaneR slot p base xs reversed widths reserved
        (RouteImpl.laneOriginals p reversed) edge index).lane = x
    | none => RouteImpl.laneRight p xs + slot ≤ (makeLaneR slot p base xs reversed widths reserved
        (RouteImpl.laneOriginals p reversed) edge index).lane)
  cases hres : reserved.getD edge none with
  | some x => simp only [makeLaneR, hres]
  | none =>
    have hpad : 0 ≤ fallback * (2 * slot + maxLabel) :=
      Int.mul_nonneg hfallback (by omega)
    simp only [makeLaneR, hres]
    change RouteImpl.laneRight p xs + slot ≤
      RouteImpl.laneRight p xs + slot + fallback * (2 * slot + maxLabel)
    omega

private theorem componentRunR_lane_origin_at {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rs : Option ComponentRegions}
    {ranks : List Int} {budget : Bool} {p0 labeled p : Proper}
    {minimum : Option RegionConstraints} {ord : OrderResult} {widths : List Int}
    {reserved : List (Option Int)} {placed q : Proper}
    {yt : List Int × List Int} {ysMid : List Int}
    (stages : ComponentRunRStages P exact spec inp cg labels orderOptions cg' run rs
      ranks budget p0 labeled p minimum ord widths reserved placed q yt ysMid)
    (hslot : 0 ≤ P.slot) {lane : RouteImpl.ReversedLane} (hlane : lane ∈ run.lanes.runs) :
    match reserved.getD lane.original none with
    | some x => lane.lane = x
    | none => RouteImpl.laneRight run.proper run.xs + P.slot ≤ lane.lane := by
  rcases stages.hLanes with ⟨hempty, hlanes⟩ | ⟨_, hlanes⟩
  · have hnil := List.nil_of_isEmpty hempty
    rw [hnil]
    change RouteImpl.laneRight run.proper run.xs + P.slot ≤ lane.lane
    obtain ⟨_, _, _, heq⟩ := RouteImpl.routeWithLanes_spec hlanes
    rw [heq] at hlane
    exact RouteImpl.plannedLane_right_strict hslot hlane
  · exact routeWithLanesR_label_lane_origin hlanes hlane

theorem componentRunR_active_lane_table {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult)
      (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages P rm cg' labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper,
      1 ≤ P.slot ∧ ∀ lane ∈ run.lanes.runs,
        match stages.allocation.lanes.getD lane.original none with
        | some x => lane.lane = x
        | none => RouteImpl.laneRight run.proper run.xs + P.slot ≤ lane.lane := by
  obtain ⟨rs, _, _, _, _, p, _, ord, _, reserved, _, _, _, _, stages⟩ :=
    componentRunR_stages hrun
  have hrs : rs = some rm := Except.ok.inj (stages.hRs.symm.trans hactive)
  rcases stages.hPlaced with ⟨hnone, _⟩ | ⟨rm', minimum, hsome, _, hcross⟩
  · rw [hrs] at hnone
    cases hnone
  have hrm : rm' = rm := Option.some.inj (hsome.symm.trans hrs)
  subst rm'
  rw [← stages.hCoordProper] at hcross
  obtain ⟨placement⟩ := crossCoordsR_allocation_stages hcross
  have hslot := componentRunR_slot_pos hrun
  refine ⟨p, minimum, ord, reserved, placement, hslot, fun lane hlane => ?_⟩
  rw [← placement.hLanes]
  exact componentRunR_lane_origin_at stages (by omega) hlane

theorem placedLabels_reversed_lane_x {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {index edge : Nat} {rect : Rect}
    {source : MeasuredLabel} {e : Edge}
    (hmem : (index, rect) ∈ placedLabels P cg run labels)
    (huniq : (labels.map (·.index)).Nodup)
    (hsource : source ∈ labels) (hindex : source.index = index)
    (hfind : cg.edges.findIdx? (fun x => x.decl == source.edge) = some edge)
    (hedge : cg.edges[edge]? = some e) (htail : e.tail ≠ e.head) (hrev : e.reversed = true) :
    ∃ (lane : RouteImpl.ReversedLane),
      run.lanes.runs.find? (fun r => r.original == edge) = some lane ∧
      lane.original = edge ∧ rect.x = lane.lane + cg.slot := by
  unfold placedLabels at hmem
  obtain ⟨label, hl, hlook⟩ := List.mem_filterMap.mp hmem
  obtain ⟨found, hfound, hlook⟩ := Option.bind_eq_some_iff.mp hlook
  obtain ⟨actual, hactual, hlook⟩ := Option.bind_eq_some_iff.mp hlook
  obtain ⟨envelope, henv, hlook⟩ := Option.bind_eq_some_iff.mp hlook
  obtain ⟨picked, hpick, hlook⟩ := Option.bind_eq_some_iff.mp hlook
  have hp : (label.index, picked.2) = (index, rect) := Option.some.inj hlook
  have hlabel : label = source := measured_eq_of_index_eq labels huniq label source hl hsource
    ((congrArg Prod.fst hp).trans hindex.symm)
  subst label
  have heq : found = edge := Option.some.inj (hfound.symm.trans hfind)
  subst found
  have heq : actual = e := Option.some.inj (hactual.symm.trans hedge)
  subst actual
  obtain ⟨_, lane, _, hlane, hex⟩ := reversed_envelope_eq htail hrev henv
  have hstack := (List.of_mem_zip (List.mem_of_find?_eq_some hpick)).2
  have hx := (Labels.stackRects_mem _ _ _ _ _ hstack).1
  have horig : lane.original = edge := by
    have hpred := List.find?_some hlane
    simpa only [beq_iff_eq] using hpred
  refine ⟨lane, hlane, horig, ?_⟩
  calc
    rect.x = picked.2.x := congrArg Rect.x (congrArg Prod.snd hp).symm
    _ = envelope.x := hx
    _ = lane.lane + cg.slot := congrArg Rect.x hex

private theorem groupFrame_right_le_laneRight {P : Params} {cg : Graph} {run : Run}
    {pos : Nat} {group : Node} (hnode : cg.nodes[pos]? = some group)
    (hgroup : group.border = -2) :
    (frameRect P cg run pos).x + (frameRect P cg run pos).w ≤
      RouteImpl.laneRight run.proper run.xs := by
  have hright : (boundsOf (groupBorderRects cg run group.decl) []).right ≤
      RouteImpl.laneRight run.proper run.xs := by
    apply boundsOf_right_le_of_all (RouteImpl.laneRight_nonneg _ _)
    intro r hr
    obtain ⟨v, _, hv, _, _, rfl⟩ := groupBorderRects_inv hr
    have h := RouteImpl.laneRight_bound run.proper run.xs (List.getElem?_eq_some_iff.mp hv).1
    have he : 0 ≤ ((run.proper.nodes.getD v default).node.loopExtent : Int) := Int.natCast_nonneg _
    change RouteImpl.xAt run.xs v - Int.fdiv (RouteImpl.nodeW run.proper v) 2 +
      RouteImpl.nodeW run.proper v ≤ _
    omega
  rw [frameRect_group_span hnode hgroup]
  dsimp only
  omega

private theorem outerReversedLabel_disjoint_at_lane {P : Params} {cg : Graph} {run : Run}
    {pos : Nat} {group : Node} {rect : Rect} {lane : RouteImpl.ReversedLane}
    (hnode : cg.nodes[pos]? = some group) (hgroup : group.border = -2)
    (hslot : 0 ≤ P.slot) (hcgSlot : 0 ≤ cg.slot)
    (hx : rect.x = lane.lane + cg.slot)
    (houter : RouteImpl.laneRight run.proper run.xs + P.slot ≤ lane.lane) :
    Disjoint (frameRect P cg run pos) rect := by
  have hright := groupFrame_right_le_laneRight (P := P) (run := run) hnode hgroup
  exact rect_disjoint_of_x (Or.inl (by omega))

theorem componentRunR_active_outerReversedLabel_disjoint {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions} {index pos edge : Nat}
    {rect : Rect} {group : Node} {source : MeasuredLabel} {e : Edge}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm))
    (hslot : 0 ≤ cg'.slot)
    (hmem : (index, rect) ∈ placedLabels P cg' run labels)
    (huniq : (labels.map (·.index)).Nodup)
    (hsource : source ∈ labels) (hindex : source.index = index)
    (hfind : cg'.edges.findIdx? (fun x => x.decl == source.edge) = some edge)
    (hedge : cg'.edges[edge]? = some e) (htail : e.tail ≠ e.head) (hrev : e.reversed = true)
    (hnode : cg'.nodes[pos]? = some group) (hgroup : group.border = -2) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult)
      (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages P rm cg' labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper,
      (∃ lane, run.lanes.runs.find? (fun r => r.original == edge) = some lane ∧
        lane.original = edge ∧ rect.x = lane.lane + cg'.slot) ∧
        (stages.allocation.lanes.getD edge none = none → Disjoint (frameRect P cg' run pos) rect) := by
  obtain ⟨p, minimum, ord, reserved, stages, hpos, horigin⟩ :=
    componentRunR_active_lane_table hrun hactive
  obtain ⟨lane, hlane, horig, hx⟩ :=
    placedLabels_reversed_lane_x hmem huniq hsource hindex hfind hedge htail hrev
  refine ⟨p, minimum, ord, reserved, stages, ⟨lane, hlane, horig, hx⟩, ?_⟩
  intro hnone
  have hlower := horigin lane (List.mem_of_find?_eq_some hlane)
  rw [horig, hnone] at hlower
  change RouteImpl.laneRight run.proper run.xs + P.slot ≤ lane.lane at hlower
  exact outerReversedLabel_disjoint_at_lane hnode hgroup (by omega) hslot hx hlower

theorem regionC8b_samePart_emitted_routeLabel_disjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {cg : Graph} {run : Run} {loops : List (Nat × LoopPlacement)}
    {part : List Nat × Part} {area : Int} {pos key index : Nat}
    {rect packBox partFrame partLabel : Rect}
    {srcBox : ModelBox} {srcLabel : ModelLabel} {label : MeasuredLabel}
    (hpart : part.2 = { placeComponentExact execution.params cg run 0
      execution.measured loops with area := area })
    (hkey : part.1[pos]? = some key) (hpos : pos < cg.nodes.length)
    (hbox : inp.boxes[key]? = some srcBox) (hgroup : srcBox.role = .group)
    (hlabel : inp.labels[index]? = some srcLabel)
    (hnotHidden : (inp.boxes.any fun b => b.id == srcLabel.owner && b.exclusive) = false)
    (hfind : execution.measured.find? (fun l => l.index == index) = some label)
    (hpartFrame : part.2.rects[pos]? = some partFrame)
    (hpartLabel : let b := placeBoundsX execution.params cg run execution.measured loops
      partLabel = shiftRect (0 - b.minX) (-b.minY) rect)
    (hpackBox : part.1[pos]? = some key → part.2.rects[pos]? = some partFrame →
      execution.packedAcc.rects.getD key default = shiftRect packBox.x packBox.y partFrame)
    (hpackLabel : (index, partLabel) ∈ part.2.labels →
      execution.packedAcc.labels.getD index default = shiftRect packBox.x packBox.y partLabel)
    (hmem : (index, rect) ∈ placedLabels execution.params cg run execution.measured)
    (hclear : Disjoint (frameRect execution.params cg run pos) rect) :
    ∃ (g : Box) (l : SceneLabel), g ∈ res.scene.boxes ∧ l ∈ res.scene.labels ∧
      g.id = srcBox.id ∧ g.role = "group" ∧ l.id = srcLabel.id ∧ Disjoint g.rect l.rect := by
  let P := execution.params
  let b := placeBoundsX P cg run execution.measured loops
  let shift := shiftRect (0 - b.minX) (-b.minY)
  let packed := execution.packedAcc
  let sceneRect := fun r => shiftRect P.canvasMargin P.canvasMargin (orientRect o.direction packed.canvasH r)
  let g : Box := ⟨srcBox.id, srcBox.role.id, sceneRect (packed.rects.getD key default),
    srcBox.parent, srcBox.exclusive⟩
  let l : SceneLabel :=
    { id := srcLabel.id
      owner := srcLabel.owner
      text := srcLabel.text
      rect := sceneRect (packed.labels.getD index default)
      lines := label.lines.map fun line => String.ofList line.text }
  have hlabelIndex : label.index = index := by
    have hpred := List.find?_some hfind
    simpa only [beq_iff_eq] using hpred
  have hrole : g.role = "group" := congrArg BoxRole.id hgroup
  refine ⟨g, l, ?_, ?_, rfl, hrole, rfl, ?_⟩
  · rw [execution.boxes_eq_mapR]
    exact List.mem_map.mpr ⟨(srcBox, key), List.mk_mem_zipIdx_iff_getElem?.mpr hbox, rfl⟩
  · rw [execution.scene_eq]
    dsimp only [sceneOf]
    apply List.mem_filterMap.mpr
    refine ⟨(srcLabel, index), List.mk_mem_zipIdx_iff_getElem?.mpr hlabel, ?_⟩
    rw [hnotHidden, ite_eq_right (by decide : ¬ ((false : Bool) = true))]
    simp only [hfind, hlabelIndex] <;> rfl
  · have hbeforeBox : part.2.rects[pos]? = some (shift (frameRect P cg run pos)) := by
      rw [hpart]
      unfold placeComponentExact
      change (((List.range cg.nodes.length).map (frameRect P cg run)).map shift)[pos]? = _
      simp only [List.getElem?_map, List.getElem?_range hpos, Option.map_some]
    have hbeforeLabel : (index, shift rect) ∈ part.2.labels := by
      rw [hpart]
      change (index, shift rect) ∈ (placedLabels P cg run execution.measured).map
        (fun q => (q.1, shift q.2))
      exact List.mem_map.mpr ⟨(index, rect), hmem, rfl⟩
    change Disjoint (sceneRect (execution.packedAcc.rects.getD key default))
      (sceneRect (execution.packedAcc.labels.getD index default))
    have hframeShift : shift (frameRect P cg run pos) = partFrame :=
      Option.some.inj (hbeforeBox.symm.trans hpartFrame)
    have hlabelShift : partLabel = shift rect := hpartLabel
    have hpartMem : (index, partLabel) ∈ part.2.labels := by rwa [hlabelShift]
    rw [hpackBox hkey hpartFrame, hpackLabel hpartMem, ← hframeShift, hlabelShift]
    exact disjoint_sceneTransport (disjoint_shiftRect (disjoint_shiftRect hclear))

private theorem rankEquivalentR_slot_kept {rm : ComponentRegions} {cg cg' : Graph}
    {ranks : List Int} {budget : Bool}
    (h : rankEquivalentR rm cg = .ok (ranks, cg', budget)) : cg'.slot = cg.slot := by
  unfold rankEquivalentR at h
  dsimp only at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    exact (congrArg (fun q : List Int × Graph × Bool => q.2.1.slot) (Except.ok.inj h)).symm

private theorem activeGraph_slot {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {part : List Nat × Part} {candidate : Nat} {spec : RegionSpec}
    {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) (some spec) inp
      (componentCandidateR (some spec) execution.graph part.1 candidate)
      execution.measured (candidateOrder candidate) = .ok (cg, run))
    (hactive : newComponentRegions (some spec) execution.params inp
      (componentCandidateR (some spec) execution.graph part.1 candidate) = .ok (some rm)) :
    cg.slot = execution.params.slot := by
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hslot := rankEquivalentR_slot_kept hrank
  change cg.slot = execution.graph.slot at hslot
  obtain ⟨_, _, hg⟩ := bind_ok execution.graph_eq
  have hslot0 : execution.graph.slot = execution.graph0.slot :=
    (congrArg Graph.slot (Except.ok.inj hg)).symm
  obtain ⟨_, _, _, hgraph0, _, _⟩ := measuredGraph_prepared_source execution.graph0_eq
  rw [hslot, hslot0, hgraph0] <;> rfl

theorem regionC8b_selectedActive_outerReversed_emitted {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {part : List Nat × Part} {pk candidate : Nat} {s : RegionSpec}
    {cg : Graph} {run : Run} {rm : ComponentRegions} {loops : List (Nat × LoopPlacement)}
    {area : Int} {pos key index edge : Nat} {rect packBox partFrame partLabel : Rect}
    {srcBox : ModelBox} {srcLabel : ModelLabel} {label : MeasuredLabel} {e : Edge} {group : Node}
    (hselected : execution.componentsAcc.parts[pk]? = some part)
    (hrun : componentRunR execution.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) execution.graph part.1 candidate)
      execution.measured (candidateOrder candidate) = .ok (cg, run))
    (hactive : newComponentRegions (some s) execution.params inp
      (componentCandidateR (some s) execution.graph part.1 candidate) = .ok (some rm))
    (hpart : part.2 = { placeComponentExact execution.params cg run 0
      execution.measured loops with area := area })
    (hkey : part.1[pos]? = some key)
    (hbox : inp.boxes[key]? = some srcBox) (hgroup : srcBox.role = .group)
    (hlabel : inp.labels[index]? = some srcLabel)
    (hnotHidden : (inp.boxes.any fun b => b.id == srcLabel.owner && b.exclusive) = false)
    (hfind : execution.measured.find? (fun l => l.index == index) = some label)
    (hpartFrame : part.2.rects[pos]? = some partFrame)
    (hpartLabel : let b := placeBoundsX execution.params cg run execution.measured loops
      partLabel = shiftRect (0 - b.minX) (-b.minY) rect)
    (hpackBox : execution.componentsAcc.parts[pk]? = some part →
      part.1[pos]? = some key → part.2.rects[pos]? = some partFrame →
      execution.packedAcc.rects.getD key default = shiftRect packBox.x packBox.y partFrame)
    (hpackLabel : execution.componentsAcc.parts[pk]? = some part →
      (index, partLabel) ∈ part.2.labels →
      execution.packedAcc.labels.getD index default = shiftRect packBox.x packBox.y partLabel)
    (hmem : (index, rect) ∈ placedLabels execution.params cg run execution.measured)
    (hedgeFind : cg.edges.findIdx? (fun x => x.decl == label.edge) = some edge)
    (hedge : cg.edges[edge]? = some e) (htail : e.tail ≠ e.head) (hrev : e.reversed = true)
    (hnode : cg.nodes[pos]? = some group) (hborder : group.border = -2) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult) (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages execution.params rm cg execution.measured p minimum
        ord.layers run.layers run.coordinateXs reserved run.coordinateProper,
      stages.allocation.lanes.getD edge none = none →
      ∃ (g : Box) (l : SceneLabel), g ∈ res.scene.boxes ∧ l ∈ res.scene.labels ∧
        g.id = srcBox.id ∧ g.role = "group" ∧ l.id = srcLabel.id ∧ Disjoint g.rect l.rect := by
  have hslot : 0 ≤ cg.slot := by
    rw [activeGraph_slot execution (part := part) hrun hactive]
    have := componentRunR_slot_pos hrun
    omega
  have hlabelIndex : label.index = index := by
    have hpred := List.find?_some hfind
    simpa only [beq_iff_eq] using hpred
  have hlabelMem := List.mem_of_find?_eq_some hfind
  have huniq := measureLabels_index_nodup execution.measured_eq
  obtain ⟨p, minimum, ord, reserved, stages, _, hclear⟩ :=
    componentRunR_active_outerReversedLabel_disjoint hrun hactive hslot hmem huniq
      hlabelMem hlabelIndex hedgeFind hedge htail hrev hnode hborder
  refine ⟨p, minimum, ord, reserved, stages, fun hnone => ?_⟩
  exact regionC8b_samePart_emitted_routeLabel_disjoint execution hpart hkey
    (List.getElem?_eq_some_iff.mp hnode).1 hbox hgroup hlabel hnotHidden hfind
    hpartFrame hpartLabel (hpackBox hselected) (hpackLabel hselected)
    hmem (hclear hnone)

private abbrev r8bLayoutSpec (idSets : List (String × List String))
    (o : Options) (P : Params) (lines : List (List Measure.Line)) : Option RegionSpec :=
  if idSets.isEmpty then none
  else some (RegionSpec.mk idSets (lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)))

structure R8b_ChosenPart {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (part : List Nat × Part) where
  candidate : Nat
  chosen : Portfolio.Candidate (Graph × Run)
  trial : Portfolio.Candidate (Graph × Run)
  spec : Option RegionSpec
  regions : Option ComponentRegions
  cg : Graph
  run : Run
  loops : List (Nat × LoopPlacement)
  area : Int
  candidate_bound : candidate < 5
  portfolio_eq : Portfolio.portfolio o.thoroughness
    (componentTrialR execution.params exactIds
      (r8bLayoutSpec idSets o execution.params execution.lines)
      inp o execution.graph part.1 execution.measured) = .ok chosen
  trial_eq : componentTrialR execution.params exactIds
    (r8bLayoutSpec idSets o execution.params execution.lines)
    inp o execution.graph part.1 execution.measured candidate = .ok trial
  trial_value_eq : chosen.value = trial.value
  trial_scene_eq : chosen.scene = trial.scene
  winner_eq : chosen.value = (cg, run)
  regions_eq : newComponentRegions (r8bLayoutSpec idSets o execution.params execution.lines)
    execution.params inp (componentGraph execution.graph part.1) = .ok regions
  effective_eq : spec = if regions.isSome
    then r8bLayoutSpec idSets o execution.params execution.lines else none
  run_eq : componentRunR execution.params (exactDecls exactIds inp) spec inp
    (componentCandidateR spec execution.graph part.1 candidate)
    execution.measured (candidateOrder candidate) = .ok (cg, run)
  loops_eq : componentLoops execution.params cg run execution.measured = .ok loops
  part_eq : part.2 = { placeComponentExact execution.params cg run 0 execution.measured loops with
    area := area }

theorem r8b_chosenPart {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    Nonempty (R8b_ChosenPart execution part) := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨_, hall⟩ := actual_components_parts_geometryR hempty execution.components_eq
  obtain ⟨_, chosen, cg, run, loops, area, spec, _, hportfolio, hwinner,
    ⟨regions, hregions, heffective⟩, _, hloops, hplaced⟩ := hall part hpart
  obtain ⟨index, trial, hindex, htrial, hvalue, hscene⟩ :=
    Portfolio.portfolio_selected hportfolio
  have hsteps := htrial
  unfold componentTrialR at hsteps
  obtain ⟨regions', hregions', hsteps⟩ := bind_ok hsteps
  have hre : regions' = regions := Except.ok.inj (hregions'.symm.trans hregions)
  subst regions'
  obtain ⟨⟨trialGraph, trialRun⟩, htrialRun, hsteps⟩ := bind_ok hsteps
  obtain ⟨_, _, hsteps⟩ := bind_ok hsteps
  have htrialValue : (trialGraph, trialRun) = trial.value :=
    congrArg (fun c : Portfolio.Candidate (Graph × Run) => c.value) (Except.ok.inj hsteps)
  have hpair := htrialValue.trans (hvalue.symm.trans hwinner)
  rw [hpair] at htrialRun
  refine ⟨⟨index, chosen, trial, spec, regions, cg, run, loops, area, hindex, hportfolio,
    htrial, hvalue, hscene, hwinner, hregions, heffective, ?_, hloops, hplaced⟩⟩
  rw [heffective]
  exact htrialRun

def R8b_ActualUnreservedLane {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (edge : Nat) : Prop :=
  ∃ (s : RegionSpec) (rm : ComponentRegions), selected.spec = some s ∧
    ∃ (ranks : List Int) (budget : Bool) (p0 labeled p : Proper)
      (minimum : Option RegionConstraints) (ord : OrderResult) (widths : List Int)
      (reserved : List (Option Int)) (placed q : Proper) (yt : List Int × List Int)
      (ysMid : List Int),
      ComponentRunRStages execution.params (exactDecls exactIds inp) selected.spec inp
        (componentCandidateR selected.spec execution.graph part.1 selected.candidate)
        execution.measured (candidateOrder selected.candidate) selected.cg selected.run
        (some rm) ranks budget p0 labeled p minimum ord widths reserved placed q yt ysMid ∧
      reserved.getD edge none = none

private theorem r8b_laneRight_of_unreserved {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    {selected : R8b_ChosenPart execution part} {edge : Nat} {lane : RouteImpl.ReversedLane}
    (houter : R8b_ActualUnreservedLane selected edge)
    (hlane : lane ∈ selected.run.lanes.runs) (horiginal : lane.original = edge) :
    0 ≤ selected.cg.slot ∧ 0 ≤ execution.params.slot ∧
      RouteImpl.laneRight selected.run.proper selected.run.xs + execution.params.slot ≤
        lane.lane := by
  obtain ⟨s, _, hspec, _, _, _, _, _, _, _, _, _, _, _, _, _, stages, hnone⟩ := houter
  have hrun := selected.run_eq
  have hactive := stages.hRs
  rw [hspec] at hrun hactive
  have hpositive := componentRunR_slot_pos hrun
  have hcgSlot := activeGraph_slot execution (part := part) hrun hactive
  refine ⟨by omega, by omega, ?_⟩
  have h := componentRunR_lane_origin_at stages (by omega) hlane
  rw [horiginal, hnone] at h
  exact h

/-- An emitted reversed label on the global unreserved lane, paired with a
selected border frame at any depth. "Outer" describes the lane, not the frame. -/
def R8b_EmittedOuterReversedAt {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (index : Nat) (stored : Rect) (pos : Nat) : Prop :=
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
    selected.cg.nodes[pos]? = some group ∧ group.border = -2 ∧
    R8b_ActualUnreservedLane selected edge

theorem r8b_emittedOuter_part_disjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    {selected : R8b_ChosenPart execution part} {index pos : Nat} {stored frame : Rect}
    (hframe : part.2.rects[pos]? = some frame)
    (houter : R8b_EmittedOuterReversedAt selected index stored pos) :
    Disjoint frame stored := by
  obtain ⟨_, label, raw, group, edge, e, _, _, hfind, hraw, hstored, hedgeFind,
    hedge, htail, hrev, hnode, hborder, hreserve⟩ := houter
  have hlabelIndex : label.index = index := by
    have hpred := List.find?_some hfind
    simpa only [beq_iff_eq] using hpred
  obtain ⟨lane, hlane, horiginal, hx⟩ :=
    placedLabels_reversed_lane_x hraw (measureLabels_index_nodup execution.measured_eq)
      (List.mem_of_find?_eq_some hfind) hlabelIndex hedgeFind hedge htail hrev
  obtain ⟨hcgSlot, hslot, hlower⟩ :=
    r8b_laneRight_of_unreserved hreserve (List.mem_of_find?_eq_some hlane) horiginal
  have hclear := outerReversedLabel_disjoint_at_lane hnode hborder hslot hcgSlot hx hlower
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

/-- Same-part clearance outside the emitted active unreserved reversed branch
for border frames, including nested ones. This cut does not remove demoted
frames, fallback runs, active reserved lanes, forward labels, loops, or
non-emitted labels. Stored-title captions keep their original conjunct. -/
def R_ExecutedPartFrameCoresB8OuterRemainder (exactIds : List String)
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
        Disjoint frame stored ∨ frame.StrictInside stored) ∧
      PartCaptionFrameClear execution.params inp o execution.lines part

theorem R_executedPartFrameCoresB8_iff_outerRemainder (exactIds : List String)
    (idSets : List (String × List String)) :
    R_ExecutedPartFrameCoresB8 exactIds idSets ↔
      R_ExecutedPartFrameCoresB8OuterRemainder exactIds idSets := by
  classical
  constructor
  · intro old inp o res execution part hpart
    obtain ⟨hroute, hcap⟩ := old execution part hpart
    refine ⟨?_, hcap⟩
    intro _ index stored pos key src frame hlabel hkey hsrc hgroup hframe _
    exact hroute index stored pos key src frame hlabel hkey hsrc hgroup hframe
  · intro remaining inp o res execution part hpart
    obtain ⟨hroute, hcap⟩ := remaining execution part hpart
    obtain ⟨selected⟩ := r8b_chosenPart execution hpart
    refine ⟨?_, hcap⟩
    intro index stored pos key src frame hlabel hkey hsrc hgroup hframe
    by_cases houter : R8b_EmittedOuterReversedAt selected index stored pos
    · exact Or.inl (r8b_emittedOuter_part_disjoint hframe houter)
    · exact hroute selected index stored pos key src frame hlabel hkey hsrc hgroup hframe houter

theorem flatC8bB_layoutRIds_outerRemainder (exactIds : List String)
    (idSets : List (String × List String))
    (hcores : R_ExecutedPartFrameCoresB8OuterRemainder exactIds idSets)
    (hfallW : R_FallbackCaptionClearBW exactIds idSets)
    (hres : R_PartSizingRResidual exactIds idSets)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    FlatC8bB (PipelineImpl.layoutRIds exactIds idSets) :=
  flatC8bB_layoutRIds_Wf exactIds idSets
    ((R_executedPartFrameCoresB8_iff_outerRemainder exactIds idSets).mpr hcores) hfallW hres hcap

theorem R_reindexedPartFrameCoresB8_iff_outerRemainder (exactIds : List String)
    (idSets : List (String × List String)) :
    (∀ sub : Input, R_ExecutedPartFrameCoresB8 exactIds (reindexRegionSets idSets sub)) ↔
      (∀ sub : Input, R_ExecutedPartFrameCoresB8OuterRemainder exactIds
        (reindexRegionSets idSets sub)) := by
  constructor
  · intro h sub
    exact (R_executedPartFrameCoresB8_iff_outerRemainder exactIds
      (reindexRegionSets idSets sub)).mp (h sub)
  · intro h sub
    exact (R_executedPartFrameCoresB8_iff_outerRemainder exactIds
      (reindexRegionSets idSets sub)).mpr (h sub)

end Elegant.Layered.PipelineImpl

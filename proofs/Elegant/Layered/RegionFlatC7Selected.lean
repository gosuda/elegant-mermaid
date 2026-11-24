import Elegant.Layered.RegionC7SettledPlainLoops

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

def r7SelectedTransport {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (shelf : Rect) (cg : Graph) (run : Run) (loops : List (Nat × LoopPlacement))
    (r : Rect) : Rect :=
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH
      (shiftRect (shelf.x + (0 - bounds.minX)) (shelf.y + (-bounds.minY)) r))

structure R7_SelectedRoutePair {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (label : SceneLabel) (box : Box) where
  part : List Nat × Part
  packed : Pack.State
  shelfIndex : Nat
  shelf : Rect
  chosen : Portfolio.Candidate (Graph × Run)
  candidate : Nat
  rs : Option ComponentRegions
  cg : Graph
  run : Run
  loops : List (Nat × LoopPlacement)
  area : Int
  sourceIndex : Nat
  source : ModelLabel
  measured : MeasuredLabel
  edgeIndex : Nat
  edge : Edge
  envelope : Rect
  rect : Rect
  target : Nat
  pack_eq : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
    execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
    (LayoutConst.component_aspect_den.get o.profile)
    (execution.componentsAcc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed
  shelf_eq : (execution.componentsAcc.parts.zip packed.boxes)[shelfIndex]? = some (part, shelf)
  comp_mem : part.1 ∈ components execution.graph
  chosen_eq : Portfolio.portfolio o.thoroughness
    (componentTrialR execution.params exactIds (r7Spec idSets o execution.params execution.lines)
      inp o execution.graph part.1 execution.measured) = .ok chosen
  value_eq : chosen.value = (cg, run)
  regions_eq : newComponentRegions (r7Spec idSets o execution.params execution.lines)
    execution.params inp (componentGraph execution.graph part.1) = .ok rs
  run_eq :
    let spec := r7Eff idSets o execution.params execution.lines rs
    componentRunR execution.params (exactDecls exactIds inp) spec inp
      (componentCandidateR spec execution.graph part.1 candidate)
      execution.measured (candidateOrder candidate) = .ok (cg, run)
  loops_eq : componentLoops execution.params cg run execution.measured = .ok loops
  part_eq : part.2 = { placeComponentExact execution.params cg run 0
    execution.measured loops with area := area }
  source_eq : inp.labels[sourceIndex]? = some source
  id_eq : label.id = source.id
  measured_eq : execution.measured.find? (fun item => item.index == sourceIndex) = some measured
  placed_mem : (measured.index, rect) ∈ placedLabels execution.params cg run execution.measured
  edge_eq : cg.edges[edgeIndex]? = some edge
  envelope_eq : labelEnvelope execution.params cg run execution.measured edgeIndex edge = some envelope
  stack : (measured, rect) ∈ (routeLabels execution.measured edge.decl).zip
    (Labels.stackRects envelope.x envelope.y cg.slot
      ((routeLabels execution.measured edge.decl).map fun q => (q.width, q.height)))
  target_size : target < run.proper.nodes.length
  target_real : RouteImpl.IsReal run.proper target
  target_tail_scope : RouteImpl.nodeDecl run.proper target ∉
    ((cg.nodes[edge.tail]?).map (·.clusterPath)).getD []
  target_head_scope : RouteImpl.nodeDecl run.proper target ∉
    ((cg.nodes[edge.head]?).map (·.clusterPath)).getD []
  label_rect : label.rect = r7SelectedTransport execution shelf cg run loops rect
  box_rect : box.rect = r7SelectedTransport execution shelf cg run loops
    (RouteImpl.boxRect run.proper run.xs run.ys target)

def R7_SelectedSettledLoop {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b) : Prop :=
  pair.edge.tail = pair.edge.head ∧
    R7_SettledPlainLoopPair (r7Eff idSets o execution.params execution.lines pair.rs)
      pair.cg pair.run pair.edge.tail pair.target

def R7_OverlapRowsXGap (a b : Rect) : Prop :=
  max a.y b.y < min (a.y + a.h) (b.y + b.h) → 0 < a.w → 0 < b.w →
    a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x

private theorem r7Gap_iff_clear (a b : Rect) :
    R7_OverlapRowsXGap a b ↔ ¬ a.meetsInterior b := by
  unfold R7_OverlapRowsXGap Rect.meetsInterior
  constructor
  · rintro gap ⟨hx, hy⟩
    have hgap := gap hy (by omega) (by omega)
    omega
  · intro h hy hw₁ hw₂
    omega

def R7_SelectedRouteWithPlainTarget {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (pair : R7_SelectedRoutePair execution l b),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    (∃ node : Node, pair.cg.nodes[pair.target]? = some node ∧ node.border = 0) →
    ¬ R7_SelectedSettledLoop pair →
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target)

structure R7_SelectedClearance {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) : Prop where
  route : R7_SelectedRouteWithPlainTarget execution
  caption : ∀ (l : SceneLabel) (b : Box) (index : Nat) (source : ModelLabel),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    inp.labels[index]? = some source → l.id = source.id →
    execution.measured.find? (fun item => item.index == index) = none →
    (∃ ownerIndex, inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex) →
    R7_OverlapRowsXGap l.rect b.rect

private theorem r7SelectedTransport_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (shelf : Rect) (cg : Graph) (run : Run) (loops : List (Nat × LoopPlacement))
    (a b : Rect) :
    (¬ (r7SelectedTransport execution shelf cg run loops a).meetsInterior
        (r7SelectedTransport execution shelf cg run loops b)) ↔ ¬ a.meetsInterior b := by
  constructor
  · intro h hm
    apply h
    cases hd : o.direction <;>
      simp only [r7SelectedTransport, hd, Rect.meetsInterior, shiftRect, orientRect] at hm ⊢ <;>
      omega
  · intro h
    unfold r7SelectedTransport
    exact not_meetsInterior_transport h

private theorem r7Selected_slot_nonneg {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    0 ≤ cg'.slot := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hRest⟩ := componentRunR_specR h
  obtain ⟨_, _, hNorm, _⟩ := hRest
  unfold NormalizeImpl.normalize at hNorm
  split at hNorm
  · simp at hNorm
  · rename_i slot hs
    split at hNorm
    · rename_i hc
      by_cases hz : cg'.slot = 0
      · omega
      · have he : cg'.slot = slot := by
          simpa [NormalizeImpl.slotOf, hz] using hs
        rw [he]
        exact hc.2.2
    · simp at hNorm

private theorem r7Selected_settled_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (settled : R7_SelectedSettledLoop pair) :
    ¬ pair.rect.meetsInterior (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  obtain ⟨hloop, hplain⟩ := settled
  have hfoot := r7_loopEnvelopeMiss_of_settledPlainPair execution
    (candidate := pair.candidate) pair.comp_mem rfl pair.run_eq hplain
  have hs := r7Selected_slot_nonneg pair.run_eq
  have hn := SceneExecutionR.measured_nonnegR execution
  have henv := pair.envelope_eq
  unfold labelEnvelope at henv
  obtain ⟨_, _, hrest⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (pair.edge.tail == pair.edge.head) = true := by simp [hloop]
  have hcont : (loopFootprintExt pair.cg pair.run execution.measured pair.edge.tail).Contained
      pair.envelope := by
    cases he : pair.run.exact.contains pair.edge.tail with
    | false =>
      simp only [hb, he] at hrest
      exact X_loopEnvelope_containedExt hs hn he pair.edge_eq hloop (Option.some.inj hrest).symm
    | true =>
      simp only [hb, he] at hrest
      exact X_loopExactEnvelope_containedExt hs hn pair.edge_eq hloop (Option.some.inj hrest).symm he
  exact Elegant.Layered.loop_branch_clear pair.edge_eq hloop pair.envelope_eq hs hn
    (List.of_mem_zip pair.stack).2 (Elegant.Layered.not_meetsInterior_of_contained hcont hfoot)

private theorem r7Selected_source {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {l : SceneLabel} (hl : l ∈ res.scene.labels) :
    ∃ (index : Nat) (source : ModelLabel), inp.labels[index]? = some source ∧ l.id = source.id ∧
      ((∃ measured, execution.measured.find? (fun q => q.index == index) = some measured) ∨
       (execution.measured.find? (fun q => q.index == index) = none ∧
        ∃ ownerIndex, inp.boxes.findIdx?
          (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex)) := by
  rw [execution.scene_eq] at hl
  obtain ⟨q, hq, hemitted⟩ := List.mem_filterMap.mp hl
  have hsource := List.mem_zipIdx_iff_getElem?.mp hq
  cases hex : inp.boxes.any (fun box => box.id == q.1.owner && box.exclusive) with
  | true => simp only [hex, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hex, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hm : execution.measured.find? (fun q' => q'.index == q.2) with
    | some measured =>
      simp only [hm, Option.some.injEq] at hemitted
      subst l
      exact ⟨q.2, q.1, hsource, rfl, Or.inl ⟨measured, hm⟩⟩
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx? (fun box => box.id == q.1.owner && !box.exclusive) with
      | none => simp only [ho] at hemitted; cases hemitted
      | some ownerIndex =>
        simp only [ho, Option.some.injEq] at hemitted
        subst l
        exact ⟨q.2, q.1, hsource, rfl, Or.inr ⟨hm, ownerIndex, ho⟩⟩

private theorem r7Selected_packed_contained {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {parts : List (List Nat × Part)} {packed : Pack.State} {i : Nat}
    {part : List Nat × Part} {shelf r : Rect}
    (hp : Pack.pack maxWidth gap margin aspectNum aspectDen
      (parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    (hi : parts[i]? = some part) (hs : packed.boxes[i]? = some shelf)
    (hr : (Rect.mk 0 0 part.2.width part.2.height).Contained r) :
    shelf.Contained (shiftRect shelf.x shelf.y r) := by
  obtain ⟨hpi, hpart⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hsi, hshelf⟩ := List.getElem?_eq_some_iff.mp hs
  have hmi : i < (parts.map fun q => Pack.Item.mk q.2.width q.2.height q.2.area).length := by
    simpa only [List.length_map] using hpi
  obtain ⟨hw, hh⟩ := packShelfDims hp hsi hmi
  rw [hshelf, List.getElem_map, hpart] at hw hh
  change shelf.w = part.2.width at hw
  change shelf.h = part.2.height at hh
  change 0 ≤ r.x ∧ r.x + r.w ≤ 0 + part.2.width ∧
    0 ≤ r.y ∧ r.y + r.h ≤ 0 + part.2.height at hr
  change shelf.x ≤ r.x + shelf.x ∧ r.x + shelf.x + r.w ≤ shelf.x + shelf.w ∧
    shelf.y ≤ r.y + shelf.y ∧ r.y + shelf.y + r.h ≤ shelf.y + shelf.h
  omega

theorem r7_c7_of_selectedClearance {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (execution : SceneExecutionR exactIds idSets inp o res)
    (clearance : R7_SelectedClearance execution) : Validator.C7 res.scene.layoutDump := by
  intro label hdump b hb hex hscope
  change label ∈ res.scene.labels.map SceneLabel.toLabel at hdump
  obtain ⟨l, hl, hlabel⟩ := List.mem_map.mp hdump
  subst label
  obtain ⟨index, source, hsource, hid, hbranch⟩ := r7Selected_source execution hl
  rcases hbranch with ⟨measured, hmeasured⟩ | ⟨hnone, howner⟩
  · obtain ⟨_comp, _candidate, _run, _order, _initial, _graph, _edgeIndex, _decl, _edge,
      _px, _py, _margin, _height, _direction, packed, shelfIndex, part, shelf, _loops, _area,
      stored, _rs, _compMem, _new, _initialEq, _runEq, _orderEq, _edgeEq, _declEq,
      _routeMem, _labelRect, _marginEq, _heightEq, _directionEq, hpacked, hselected,
      _partComp, _loopsEq, _partEq, _pxEq, _pyEq, hstoredIndex, hstored, hlStored⟩ :=
      r7_labelBelongsToRun hwf execution l index source measured hl hsource hid hmeasured
    have hp := List.mem_of_getElem? (List.getElem?_zip_eq_some.mp hselected).1
    obtain ⟨hkeys, hactual⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
    have hcomp : part.1 ∈ components execution.graph := by
      rw [← hkeys]
      exact List.mem_map_of_mem hp
    obtain ⟨candidate, chosen, cg, run, loops, area, spec, _, hchosen, hvalue,
      ⟨rs, hnew, hspec⟩, hrun, hloops, hpart⟩ := hactual part hp
    change newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph part.1) = .ok rs at hnew
    change spec = r7Eff idSets o execution.params execution.lines rs at hspec
    subst spec
    let effective := r7Eff idSets o execution.params execution.lines rs
    let original := componentCandidateR effective execution.graph part.1 candidate
    let bounds := placeBoundsX execution.params cg run execution.measured loops
    have hmap := hstored
    have hlabels : part.2.labels = (placedLabels execution.params cg run execution.measured).map
        (fun q => (q.1, shiftRect (0 - bounds.minX) (-bounds.minY) q.2)) := by
      rw [hpart]
      exact X_placeComponentExact_labels_eq
    rw [hlabels] at hmap
    obtain ⟨⟨k, rect⟩, hplaced, hstoredEq⟩ := List.mem_map.mp hmap
    have hk : k = measured.index := (congrArg Prod.fst hstoredEq).trans hstoredIndex
    subst k
    have hnd := measureLabels_index_nodup execution.measured_eq
    obtain ⟨ml, edgeIndex, edge, envelope, r, hml, hmi, _, he, henv, hstack, hrect⟩ :=
      placedLabels_pair_inv hnd hplaced
    subst r
    have hm : ml = measured := measured_eq_of_index_eq execution.measured hnd ml measured
      hml (List.mem_of_find?_eq_some hmeasured) hmi
    subst ml
    have hstackMem := List.mem_of_find?_eq_some hstack
    have hroute := (List.of_mem_zip hstackMem).1
    have hstep : componentRunR execution.params (exactDecls exactIds inp) effective inp
        original execution.measured (candidateOrder candidate) = .ok (cg, run) := hrun
    rcases r7_exclusiveBoxInLabelRun hwf hfp execution l index source measured part.1
      candidate run (candidateOrder candidate) original cg edgeIndex edge.decl edge packed
      shelfIndex part shelf loops area stored hl hsource hid hmeasured hcomp rs hnew rfl hstep
      he (by simp only [he, Option.map_some]) hroute hpacked hselected rfl hpart hstored
      hlStored b hb hex hscope with ⟨v, hv, hreal, hplain, htail, hhead, hbrect⟩ | hother
    · have hlrect : l.rect = r7SelectedTransport execution shelf cg run loops rect := by
        have hshift : shiftRect (0 - bounds.minX) (-bounds.minY) rect = stored.2 :=
          congrArg Prod.snd hstoredEq
        rw [hlStored, ← hshift, shiftRect_shiftRect]
        rfl
      let pair : R7_SelectedRoutePair execution l b :=
        ⟨part, packed, shelfIndex, shelf, chosen, candidate, rs, cg, run, loops, area,
          index, source, measured, edgeIndex, edge, envelope, rect, v,
          hpacked, hselected, hcomp, hchosen, hvalue, hnew, hstep, hloops, hpart,
          hsource, hid, hmeasured, hplaced, he, henv, hstackMem, hv, hreal, htail,
          hhead, hlrect, hbrect⟩
      have hclear : ¬ pair.rect.meetsInterior
          (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
        by_cases hs : R7_SelectedSettledLoop pair
        · exact r7Selected_settled_clear pair hs
        · exact (r7Gap_iff_clear _ _).mp (clearance.route l b pair hl hb hex hscope hplain hs)
      change ¬ l.rect.meetsInterior b.rect
      rw [pair.label_rect, pair.box_rect]
      exact (r7SelectedTransport_clear _ _ _ _ _ _ _).mpr hclear
    · obtain ⟨otherPacked, c, d, lp, bp, cs, ds, rl, r, hpack, hc, hcs, hd, hds,
        hcd, hrl, hr, hlrect, hbrect⟩ := hother
      have hbounds := exactComponentPlacementR_bounded_of_residual execution
        (R_partSizingRResidual_holds exactIds idSets)
      obtain ⟨_, _, _, _, _, hrlBound⟩ := hbounds lp (List.mem_of_getElem? hc)
      obtain ⟨_, _, hrBound, _, _, _⟩ := hbounds bp (List.mem_of_getElem? hd)
      have hlWithin := r7Selected_packed_contained hpack hc hcs
        (r := rl.2) (by have h := hrlBound rl hrl; unfold Rect.Contained; dsimp; omega)
      have hbWithin := r7Selected_packed_contained hpack hd hds
        (r := r) (by have h := hrBound r hr; unfold Rect.Contained; dsimp; omega)
      obtain ⟨hci, hcEq⟩ := List.getElem?_eq_some_iff.mp hcs
      obtain ⟨hdi, hdEq⟩ := List.getElem?_eq_some_iff.mp hds
      have hsep := Pack.pack_boxes_disjoint hpack c d hci hdi hcd
      rw [hcEq, hdEq] at hsep
      change ¬ l.rect.meetsInterior b.rect
      rw [hlrect, hbrect]
      exact not_meetsInterior_shiftRect (not_meetsInterior_orientRect
        (not_meetsInterior_of_contained hsep hlWithin hbWithin))
  · exact (r7Gap_iff_clear _ _).mp
      (clearance.caption l b index source hl hb hex hscope hsource hid hnone howner)

private theorem r7_selectedClearance_of_c7 {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (h : Validator.C7 res.scene.layoutDump) : R7_SelectedClearance execution where
  route := by
    intro l b pair hl hb hex hscope _ _
    have hmem : l.toLabel ∈ res.scene.layoutDump.labels := List.mem_map.mpr ⟨l, hl, rfl⟩
    have hclear := h l.toLabel hmem b hb hex hscope
    change ¬ l.rect.meetsInterior b.rect at hclear
    rw [pair.label_rect, pair.box_rect] at hclear
    exact (r7Gap_iff_clear _ _).mpr ((r7SelectedTransport_clear _ _ _ _ _ _ _).mp hclear)
  caption l b _ _ hl hb hex hscope _ _ _ _ := by
    have hmem : l.toLabel ∈ res.scene.layoutDump.labels := List.mem_map.mpr ⟨l, hl, rfl⟩
    exact (r7Gap_iff_clear _ _).mpr (h l.toLabel hmem b hb hex hscope)

def R7_ReindexedSelectedClearance (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
    Elegant.Layered.PartsSeparated inp o res → LabelRunsClearExclusiveBoxes inp o res →
    SceneCaptionBoxContainment inp o res →
    layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
    ∀ execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res,
      R7_SelectedClearance execution

theorem flatC7B_layoutRIds_reindex_of_selected (exactIds : List String)
    (idSets : List (String × List String)) (hselected : R7_ReindexedSelectedClearance exactIds idSets) :
    FlatC7B (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) := by
  intro inp o res hwf hfp hfit hsep hruns hcap hok
  obtain ⟨execution⟩ := layoutRIds_sceneExecution hok
  exact r7_c7_of_selectedClearance hwf hfp execution
    (hselected inp o res hwf hfp hfit hsep hruns hcap hok execution)

theorem flatC7B_layoutRIds_reindex_iff_selected (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC7B (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) ↔
      R7_ReindexedSelectedClearance exactIds idSets := by
  constructor
  · intro hflat inp o res hwf hfp hfit hsep hruns hcap hok execution
    exact r7_selectedClearance_of_c7 execution (hflat inp o res hwf hfp hfit hsep hruns hcap hok)
  · exact flatC7B_layoutRIds_reindex_of_selected exactIds idSets

end Elegant.Layered.PipelineImpl

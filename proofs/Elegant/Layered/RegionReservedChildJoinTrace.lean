import Elegant.Layered.RegionReservedLaneStability
import Elegant.Layered.RegionReservedChildMarkerHull

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

def activeReservedChildCrossInput (P : Params) (exact : List Nat)
    (s : RegionSpec) (rm : ComponentRegions) (candidate : Graph)
    (labels : List MeasuredLabel) : Except LayoutError Proper := do
  let ranked ← rankEquivalentR rm candidate
  let p0 ← normalize ranked.2.1 ranked.1
  let labeled ← Labels.addLabelNodes ranked.2.1 p0 (componentLabels ranked.2.1 labels)
  return coordinateGraphR P exact (some s) labeled

private theorem reservedChild_ranked_slot {rm : ComponentRegions} {candidate cg : Graph}
    {ranks : List Int} {budget : Bool}
    (h : rankEquivalentR rm candidate = .ok (ranks, cg, budget)) :
    cg.slot = candidate.slot := by
  unfold rankEquivalentR at h
  dsimp only at h
  split at h
  · simp [bind, Except.bind] at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    exact (congrArg (fun q : List Int × Graph × Bool => q.2.1.slot) (Except.ok.inj h)).symm

/-- A selected reversed label uses the actual reserved lane of the selected frame's
parent. The crossing result, child origin, lane write, and frame hull all come
from the same successful run and crossing witness. Clearance is preserved in the
stored part when both rectangles are the outputs of that run's exact placement. -/
theorem componentRunR_active_reservedChildReversedLabel_disjoint_traced
    {P : Params} {exact : List Nat} {s : RegionSpec} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph cg : Graph}
    {labels : List MeasuredLabel} {run : Run} {comp : List Nat} {candidate : Nat}
    {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraph : exactGraph P exactIds inp o labels graph0 = .ok graph)
    (hcomp : comp ∈ components graph)
    (hparams : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P exact (some s) inp
      (componentCandidateR (some s) graph comp candidate) labels orderOptions = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp
      (componentCandidateR (some s) graph comp candidate) = .ok (some rm)) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult)
      (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages P rm cg labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper,
      crossCoordsR P rm cg labels p minimum ord.layers =
        .ok (run.coordinateXs, run.layers, reserved, run.coordinateProper) ∧
      activeReservedChildCrossInput P exact s rm
        (componentCandidateR (some s) graph comp candidate) labels = .ok p ∧
      (∃ (ranks : List Int) (budget : Bool),
        rankEquivalentR rm (componentCandidateR (some s) graph comp candidate) =
          .ok (ranks, cg, budget)) ∧
      ∀ {owner child k edge pos index : Nat} {rect : Rect} {source : MeasuredLabel}
        {e : Edge} {c : RegionCluster} {frame : Node},
        owner < rm.clusters.length →
        edgeOwnerOf rm stages.groups rm.clusters.length e.tail e.head = owner →
        (stages.placement.children.getD owner [])[k]? = some child →
        rm.clusters[child]? = some c →
        cg.nodes[pos]? = some frame → frame.border = -2 → frame.decl = c.decl →
        (index, rect) ∈ placedLabels P cg run labels → (labels.map (·.index)).Nodup →
        source ∈ labels → source.index = index →
        cg.edges.findIdx? (fun x => x.decl == source.edge) = some edge →
        cg.edges[edge]? = some e → e.tail ≠ e.head → e.reversed = true →
        ∃ laneX, reserved.getD edge none = some laneX ∧
          ActiveReservedChildCoordinates P stages.placement stages.allocation cg run
            owner child k edge pos laneX ∧
          Disjoint (frameRect P cg run pos) rect ∧
          ∀ (loops : List (Nat × LoopPlacement)) {part : Part}
            {area : Int} {storedFrame storedLabel : Rect},
            part = { placeComponentExact P cg run 0 labels loops with area := area } →
            part.rects[pos]? = some storedFrame →
            (let bounds := placeBoundsX P cg run labels loops
             storedLabel = shiftRect (0 - bounds.minX) (-bounds.minY) rect) →
            Disjoint storedFrame storedLabel := by
  obtain ⟨rs, ranks, budget, p0, labeled, p, _, ord, _, reserved, _, _, _, _, trace⟩ :=
    componentRunR_stages hrun
  have hrs : rs = some rm := Except.ok.inj (trace.hRs.symm.trans hactive)
  rcases trace.hPlaced with ⟨hnone, _⟩ | ⟨region, minimum, hsome, hm, hcross⟩
  · rw [hrs] at hnone
    cases hnone
  have hregion : region = rm := Option.some.inj (hsome.symm.trans hrs)
  subst region
  rw [← trace.hCoordProper] at hcross
  obtain ⟨stages⟩ := crossCoordsR_allocation_stages hcross
  have hmin : constrainR rm P p = .ok minimum := by
    rcases trace.hMin with ⟨hnone, _⟩ | ⟨region, m, hsome, hm', hconstrain⟩
    · rw [hrs] at hnone
      cases hnone
    have hrm : region = rm := Option.some.inj (hsome.symm.trans hrs)
    have he : m = minimum := Option.some.inj (hm'.symm.trans hm)
    simpa only [hrm, he] using hconstrain
  have hrank : rankEquivalentR rm (componentCandidateR (some s) graph comp candidate) =
      .ok (ranks, cg, budget) := by
    rcases trace.hRank with ⟨_, hnone, _⟩ | ⟨region, hsome, h⟩
    · rw [hrs] at hnone
      cases hnone
    have he : region = rm := Option.some.inj (hsome.symm.trans hrs)
    simpa only [he] using h
  have hchains : p.chains.length = cg.edges.length := by
    have hc : p.chains = labeled.chains := by
      rw [← trace.hCoord]
      exact rcbCoordinateR_chains
    rw [hc, (Labels.addLabelNodes_metadata trace.hLabels).2.2.1]
    exact normalize_chains_length (p := p0) trace.hNorm
  have hslot : 0 ≤ P.slot := by
    have h := componentRunR_slot_pos hrun
    omega
  have hcgSlot : 0 ≤ cg.slot := by
    have hc := reservedChild_ranked_slot hrank
    change cg.slot = graph.slot at hc
    have hg := hgraph
    unfold exactGraph at hg
    obtain ⟨_, _, hg⟩ := bind_ok hg
    have he : graph.slot = graph0.slot := by rw [← Except.ok.inj hg]
    obtain ⟨_, _, _, hp, _, _⟩ := measuredGraph_prepared_source hgraph0
    have hs := congrArg Graph.slot hp
    change graph0.slot = P.slot at hs
    rwa [hc, he, hs]
  have hinput : activeReservedChildCrossInput P exact s rm
      (componentCandidateR (some s) graph comp candidate) labels = .ok p := by
    unfold activeReservedChildCrossInput
    rw [hrank]
    change (normalize cg ranks).bind (fun q =>
      (Labels.addLabelNodes cg q (componentLabels cg labels)).bind (fun l =>
        .ok (coordinateGraphR P exact (some s) l))) = .ok p
    rw [trace.hNorm]
    change (Labels.addLabelNodes cg p0 (componentLabels cg labels)).bind
      (fun l => .ok (coordinateGraphR P exact (some s) l)) = .ok p
    rw [trace.hLabels]
    exact congrArg Except.ok trace.hCoord
  refine ⟨p, minimum, ord, reserved, stages, hcross, hinput, ⟨ranks, budget, hrank⟩, ?_⟩
  intro owner child k edge pos index rect source e c frame howner hownerOf hchild hc hn hb hd
    hmem huniq hsource hindex hfind hedge htail hrev
  obtain ⟨_, laneX, _, htable, hband⟩ := stages.reserved_lane_of_edge
    (activeRegion_parent_count hactive) hmin hchains hslot howner hedge htail hrev hownerOf
  have hleft := stages.childBudget_left_from_allocation hactive hmin (Nat.le_of_lt howner) hchild
  rw [ite_eq_right (Nat.ne_of_lt howner)] at hleft
  have hframe := (stages.activeChild_frame_within_reservation hgraph0 hgraph hcomp hrun hactive
    hrank trace.hNorm trace.hLabels trace.hCoord hparams hmin hc hn hb hd).2
  have hreserved : reserved.getD edge none = some laneX := by
    rw [stages.hLanes]
    exact htable
  have hrouter : routeWithLanesR P.slot run.proper run.layers run.xs (cg.edges.map (·.reversed))
      (cg.edges.map fun ed => (stackSize cg.slot (routeLabels labels ed.decl)).width)
      reserved = .ok run.lanes := by
    rcases trace.hLanes with ⟨hempty, _⟩ | ⟨_, hroute⟩
    · have hnil := hreserved
      rw [List.nil_of_isEmpty hempty] at hnil
      cases hnil
    · simpa only [trace.hLabelWidths] using hroute
  have hcoords : ActiveReservedChildCoordinates P stages.placement stages.allocation cg run
      owner child k edge pos laneX := ⟨hleft, htable, hband, hframe⟩
  have hclear := stages.reservedChildReversedLabel_disjoint hrun hactive hparams hmin
    howner hchild hcgSlot hmem huniq hsource hindex hfind hedge htail hrev hrouter hcoords
  refine ⟨laneX, hreserved, hcoords, hclear, ?_⟩
  intro loops part area storedFrame storedLabel hpart hstoredFrame hstoredLabel
  let bounds := placeBoundsX P cg run labels loops
  let translate := shiftRect (0 - bounds.minX) (-bounds.minY)
  have hpos := (List.getElem?_eq_some_iff.mp hn).1
  have hframeLookup : part.rects[pos]? = some (translate (frameRect P cg run pos)) := by
    rw [hpart]
    unfold placeComponentExact
    change (((List.range cg.nodes.length).map (frameRect P cg run)).map translate)[pos]? = _
    simp only [List.getElem?_map, List.getElem?_range hpos, Option.map_some]
  change storedLabel = translate rect at hstoredLabel
  rw [Option.some.inj (hstoredFrame.symm.trans hframeLookup), hstoredLabel]
  exact disjoint_shiftRect hclear

end Elegant.Layered.PipelineImpl

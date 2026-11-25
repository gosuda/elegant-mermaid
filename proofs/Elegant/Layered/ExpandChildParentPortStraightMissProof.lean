import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ExactFlatC5ChosenPart

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem straightPortMisses {P Q : Point} {x : Int}
    {r : Rect} (hbelow : r.y + r.h ≤ P.y ∧ r.y + r.h ≤ Q.y) :
    RouteImpl.pairsAll (fun a b => Polyline.segMisses a b r) [P, ⟨x, P.y⟩, Q] :=
  ⟨RouteImpl.miss_below (by dsimp; omega),
    RouteImpl.miss_below (by dsimp; omega), trivial⟩

private theorem straightPortMissesAbove {P Q : Point} {x : Int}
    {r : Rect} (habove : P.y ≤ r.y ∧ Q.y ≤ r.y) :
    RouteImpl.pairsAll (fun a b => Polyline.segMisses a b r) [P, ⟨x, P.y⟩, Q] :=
  ⟨RouteImpl.miss_above (by dsimp; omega),
    RouteImpl.miss_above (by dsimp; omega), trivial⟩

/-- An exact run's forward straight route consisting of one proper edge misses the
    open interior of either plain endpoint frame. The branch tests select the
    actual route constructor; no endpoint-boundary or clearance premise is needed. -/
theorem componentRunX_directStraight_attached_frame_miss
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {rt : EdgeRoute} (hrt : rt ∈ run.routes)
    (hf : run.lanes.runs.find? (fun lane => lane.original == rt.original) = none)
    {i : Nat} (hchain : RouteImpl.edgesOf run.proper rt.original = [i])
    (hstraight : RouteImpl.runOf run.lanes.routing i = run.lanes.routing.targetX.getD i 0)
    {v : Nat} (hend : (v = (RouteImpl.edgeAt run.proper i).tail ∧
      RouteImpl.frameKind run.proper v ≠ -2) ∨ v = (RouteImpl.edgeAt run.proper i).head)
    (hplain : (cg.nodes.getD v default).border ≠ -2) :
    ¬ Polyline.hitsRect rt.points (frameRect P cg run v) := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, hr, _, hpoints⟩ := componentRunX_spec hrun
  obtain ⟨_, hrank, hlen, _, hlookup, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]
    exact hrank
  have hnodes : run.proper.nodes = q0.nodes := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hi : i < run.proper.edges.length :=
    RouteImpl.mem_edgesOf (o := rt.original) (by rw [hchain]; simp)
  obtain ⟨_, hsizes, _, hcovered, hedges⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hr).1
  let tail := (RouteImpl.edgeAt run.proper i).tail
  let head := (RouteImpl.edgeAt run.proper i).head
  have htail : tail < run.proper.nodes.length := (hedges i hi).1
  have hhead : head < run.proper.nodes.length := (hedges i hi).2.1
  have hstep : rk run.proper.rank head = rk run.proper.rank tail + 1 := (hedges i hi).2.2
  obtain ⟨hinBand, hdisjBands⟩ := X_ReserveBands_holds exactIds hrun
  have hband : ∀ u, u < run.proper.nodes.length →
      ∃ l, run.layers[(rk run.proper.rank u).toNat]? = some l ∧
        0 ≤ rk run.proper.rank u ∧
        run.top.getD (rk run.proper.rank u).toNat 0 ≤ run.ys.getD u 0 ∧
        run.ys.getD u 0 + RouteImpl.nodeH run.proper u ≤
          run.top.getD (rk run.proper.rank u).toNat 0 +
            CoordsImpl.layerHeight run.coordinateProper l := by
    intro u hu
    obtain ⟨l, hl, hmem, hnn⟩ := hcovered u hu
    have hc : u < run.coordinateProper.nodes.length := by rw [← hlen, ← hnodes]; exact hu
    obtain ⟨coord, hcoord⟩ : ∃ nd, run.coordinateProper.nodes[u]? = some nd :=
      ⟨_, List.getElem?_eq_getElem hc⟩
    obtain ⟨routed, hrouted, _, _, hheight⟩ := hlookup u coord hcoord
    have hn : run.proper.nodes[u]? = some routed := by rw [hnodes]; exact hrouted
    have hcoordRank : rk run.coordinateProper.rank u = ((rk run.proper.rank u).toNat : Int) := by
      rw [← hranks, Int.toNat_of_nonneg hnn]
    obtain ⟨hlo, hhi⟩ := hinBand _ l u hl hmem hc hcoordRank
    exact ⟨l, hl, hnn, hlo, by simpa only [CoordsImpl.nodeH, RouteImpl.nodeH, hcoord, hn, hheight] using hhi⟩
  obtain ⟨tl, htl, htailNN, _, htailBottom⟩ := hband tail htail
  obtain ⟨hl, hhl, _, hheadTop, _⟩ := hband head hhead
  have horders := hdisjBands _ _ tl hl (by omega) htl hhl
  have hbottomTop : run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail ≤ run.ys.getD head 0 := by
    omega
  obtain ⟨_, he⟩ := RouteImpl.routePointsWithLanes_mem hpoints hrt
  simp only [RouteImpl.laneRouteOf, hf, RouteImpl.routeOf, hchain] at he
  split at he
  · simp at he
  · next pcs hpcs =>
    have hzip := RouteImpl.mapOk_zipped _ _ _ hpcs
    obtain ⟨piece, hpiece, hflatten⟩ : ∃ piece,
        RouteImpl.pieceOf run.proper P.slot run.ys run.top
          (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing i = .ok piece ∧
        pcs.flatten = piece := by
      cases pcs with
      | nil => exact False.elim hzip
      | cons piece rest =>
        cases rest with
        | nil => exact ⟨piece, hzip.1, by simp⟩
        | cons other rest => exact False.elim hzip.2
    simp only [Except.ok.injEq] at he
    have hpts : rt.points = RouteImpl.dedup piece := by
      rw [← he, hflatten]
    rcases RouteImpl.pieceOf_cases hpiece with ⟨hpc, _⟩ | ⟨_, hturn⟩
    · rw [hpts, hpc]
      have hv : v < run.proper.nodes.length := by
        rcases hend with ⟨rfl, _⟩ | rfl
        · exact htail
        · exact hhead
      rw [plain_frame_eq_boxRect P cg run v hv hplain]
      apply Polyline.not_hits_of_allMiss
      rw [RouteImpl.allSegsMiss_iff]
      apply RouteImpl.pairsAll_dedup
      rcases hend with ⟨rfl, hnotTop⟩ | rfl
      · apply straightPortMisses
        have hstart : (RouteImpl.pieceStart run.proper run.ys run.lanes.routing i).y =
            run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail := by
          simp [tail, RouteImpl.pieceStart, RouteImpl.yAt, hnotTop]
        have hfinish : (RouteImpl.pieceEnd run.proper run.ys run.lanes.routing i).y =
            run.ys.getD head 0 := rfl
        simp only [RouteImpl.boxRect, hstart, hfinish, RouteImpl.yAt]
        exact ⟨Int.le_refl _, hbottomTop⟩
      · apply straightPortMissesAbove
        have hstart : (RouteImpl.pieceStart run.proper run.ys run.lanes.routing i).y ≤
            run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail := by
          change (if RouteImpl.frameKind run.proper tail = -2 then run.ys.getD tail 0
            else run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail) ≤ _
          split
          · have hh := (hsizes tail htail).2
            omega
          · exact Int.le_refl _
        exact ⟨Int.le_trans hstart hbottomTop, Int.le_refl _⟩
    · exact False.elim (hturn hstraight)

/-- Transport a component route and its endpoint's frame through the same placement,
    orientation and canvas offset. This also applies when the route and box are
    identified at their final scene emission equations. -/
theorem parent_port_miss_transport {points : List Point} {r : Rect}
    (hmiss : ¬ Polyline.hitsRect points r)
    (margin : Int) (d : Direction) (canvasH boxX boxY minX minY : Int) :
    ¬ Polyline.hitsRect (points.map (routePointTransport margin d canvasH boxX boxY minX minY))
      (shiftRect margin margin (orientRect d canvasH (shiftRect (boxX - minX) (boxY - minY) r))) := by
  have hmap : points.map (routePointTransport margin d canvasH boxX boxY minX minY) =
      points.map (fun x => shiftPoint margin margin
        (orientPoint d canvasH (shiftPoint (boxX - minX) (boxY - minY) x))) := by
    apply List.map_congr_left
    intro x _
    rfl
  rw [hmap]
  simpa only [List.map_map, Function.comp_def] using
    not_hitsRect_shift_orient d canvasH margin margin _ _
      (not_hitsRect_shift (boxX - minX) (boxY - minY) _ _ hmiss)
/-- In an executed flat exact parent, the emitted forward straight route misses
    its selected endpoint's plain frame, in scene coordinates. Both lookups
    are tied to the same chosen component and actual packing. -/
theorem X_chosen_part_directStraight_attached_frame_miss
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hloop : ∀ l ∈ loops, l.1 ≠ edge.decl)
    (hf : run.lanes.runs.find? (fun lane => lane.original == i) = none)
    {j : Nat} (hchain : RouteImpl.edgesOf run.proper i = [j])
    (hstraight : RouteImpl.runOf run.lanes.routing j = run.lanes.routing.targetX.getD j 0)
    {v key : Nat} (hkey : q.1.1[v]? = some key)
    {src : ModelBox} (hsrc : inp.boxes[key]? = some src)
    (hend : (v = (RouteImpl.edgeAt run.proper j).tail ∧
      RouteImpl.frameKind run.proper v ≠ -2) ∨ v = (RouteImpl.edgeAt run.proper j).head)
    (hplain : ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v
      default).border ≠ -2)
    {pr : Route} (hpr : res.scene.routes[edge.decl]? = some pr)
    {frame : Box} (hframe : res.scene.layoutDump.box? src.id = some frame) :
    ¬ Polyline.hitsRect pr.points frame.rect := by
  obtain ⟨_, native, _, hnative, horig, hscene⟩ :=
    X_chosen_part_route_entry execution packed hpacked hselected hrun hpart hedge hloop
  have hbox :=
    X_DumpLookup_holds exactIds execution hwf packed hpacked hselected hpart hkey hsrc
  have hrEq := Option.some.inj (hpr.symm.trans hscene)
  have hbEq := Option.some.inj (hframe.symm.trans hbox)
  have hmem : native ∈ run.routes := List.mem_of_getElem? hnative
  have hmiss := componentRunX_directStraight_attached_frame_miss
    (exactIds := exactIds) (inp := inp) hrun hmem
    (by rw [horig]; exact hf) (by rw [horig]; exact hchain) hstraight hend hplain
  rw [hrEq, hbEq]
  let bounds := placeBoundsX execution.params
    (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops
  exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
    execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY

end Elegant.Layered.PipelineImpl

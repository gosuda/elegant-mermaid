import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ExactFlatC5ChosenPart
import Elegant.Layered.ForwardLane
import Elegant.Layered.LaneMetadata

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

private theorem turnPortMisses {P Q : Point} {x mid : Int}
    {r : Rect} (hbelow : r.y + r.h ≤ P.y ∧ r.y + r.h ≤ mid ∧ r.y + r.h ≤ Q.y) :
    RouteImpl.pairsAll (fun a b => Polyline.segMisses a b r)
      [P, ⟨x, P.y⟩, ⟨x, mid⟩, ⟨Q.x, mid⟩, Q] :=
  ⟨RouteImpl.miss_below (by dsimp; omega),
    RouteImpl.miss_below (by dsimp; omega),
    RouteImpl.miss_below (by dsimp; omega),
    RouteImpl.miss_below (by dsimp; omega), trivial⟩

private theorem turnPortMissesAbove {P Q : Point} {x mid : Int}
    {r : Rect} (habove : P.y ≤ r.y ∧ mid ≤ r.y ∧ Q.y ≤ r.y) :
    RouteImpl.pairsAll (fun a b => Polyline.segMisses a b r)
      [P, ⟨x, P.y⟩, ⟨x, mid⟩, ⟨Q.x, mid⟩, Q] :=
  ⟨RouteImpl.miss_above (by dsimp; omega),
    RouteImpl.miss_above (by dsimp; omega),
    RouteImpl.miss_above (by dsimp; omega),
    RouteImpl.miss_above (by dsimp; omega), trivial⟩

private theorem componentRunX_forward_turn_gap
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hP : P.Valid)
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < run.proper.edges.length)
    (hrev : (cg.edges.map (·.reversed)).getD (RouteImpl.edgeAt run.proper i).original false = false)
    (hne : RouteImpl.runOf run.lanes.routing i ≠ run.lanes.routing.targetX.getD i 0) :
    run.top.getD (RouteImpl.gapOf run.proper i) 0 +
        (run.layers.map (RouteImpl.layerHeight run.proper)).getD (RouteImpl.gapOf run.proper i) 0 ≤
      RouteImpl.midOf run.proper P.slot run.top (run.layers.map (RouteImpl.layerHeight run.proper))
        run.lanes.routing i ∧
    RouteImpl.midOf run.proper P.slot run.top (run.layers.map (RouteImpl.layerHeight run.proper))
        run.lanes.routing i ≤ run.top.getD (RouteImpl.gapOf run.proper i + 1) 0 := by
  have hrunG : componentRunGen P (sizeProperPortsX P (exactDecls exactIds inp))
      (reserveExactRanks cg (exactDecls exactIds inp) labels)
      (cg.nodes.zipIdx.filterMap fun q => if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none)
      cg labels orderOptions = .ok run := by
    rw [← componentRunX_eq_gen]
    exact hrun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, _, _⟩ := componentRunX_spec hrun
  obtain ⟨base, hb, _, _⟩ := RouteImpl.routeWithLanes_spec hr
  have hk := (RouteImpl.route_segment_facts hb hi).1
  have hstep := componentRunGen_rank_step_lower (runHooksShift_exact P exactIds inp cg labels)
    hrunG hk
  obtain ⟨_, hgap, hslot, hhalf⟩ := hP
  exact RouteImpl.forward_mid_bounds hr hslot
    (CoordsImpl.half_slot_le_rankGapAt hgap hhalf run.proper run.layers _)
    hi hrev hne hstep

/-- A one-edge forward route misses the open interior of either plain endpoint frame.
    A turn requires valid layout parameters; the straight case needs no such premise. -/
theorem componentRunX_direct_attached_frame_miss
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {rt : EdgeRoute} (hrt : rt ∈ run.routes)
    (hf : run.lanes.runs.find? (fun lane => lane.original == rt.original) = none)
    {i : Nat} (hchain : RouteImpl.edgesOf run.proper rt.original = [i])
    (hvalid : RouteImpl.runOf run.lanes.routing i ≠ run.lanes.routing.targetX.getD i 0 → P.Valid)
    {v : Nat} (hend : (v = (RouteImpl.edgeAt run.proper i).tail ∧
      RouteImpl.frameKind run.proper v ≠ -2) ∨ v = (RouteImpl.edgeAt run.proper i).head)
    (hplain : (cg.nodes.getD v default).border ≠ -2) :
    ¬ Polyline.hitsRect rt.points (frameRect P cg run v) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, _, hpoints⟩ := componentRunX_spec hrun
  have hi : i < run.proper.edges.length :=
    RouteImpl.mem_edgesOf (o := rt.original) (by rw [hchain]; simp)
  obtain ⟨_, hsizes, _, _, hedges⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hr).1
  let tail := (RouteImpl.edgeAt run.proper i).tail
  let head := (RouteImpl.edgeAt run.proper i).head
  have htail : tail < run.proper.nodes.length := (hedges i hi).1
  have hhead : head < run.proper.nodes.length := (hedges i hi).2.1
  have hgap := componentRunX_edge_rank_gap hrun hi
  have hbottomTop : run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail ≤ run.ys.getD head 0 :=
    Int.le_trans hgap.1 (Int.le_trans hgap.2.1 hgap.2.2)
  obtain ⟨ho, he⟩ := RouteImpl.routePointsWithLanes_mem hpoints hrt
  have hoi : (RouteImpl.edgeAt run.proper i).original = rt.original :=
    (mem_edgesOf.mp (by rw [hchain]; simp)).2
  have hrev : (cg.edges.map (·.reversed)).getD (RouteImpl.edgeAt run.proper i).original false = false := by
    rw [hoi]
    apply Classical.byContradiction
    intro hn
    have ht : (cg.edges.map (·.reversed)).getD rt.original false = true := by
      cases he : (cg.edges.map (·.reversed)).getD rt.original false <;> simp_all
    have hne : (RouteImpl.edgesOf run.proper rt.original).isEmpty = false := by
      rw [hchain]
      rfl
    obtain ⟨base, _, _, hlr⟩ := RouteImpl.routeWithLanes_spec hr
    obtain ⟨lane, hm, hor⟩ := RouteImpl.plannedLane_exists (base := base)
      (x := run.xs) (widths := cg.edges.map fun edge =>
        (stackSize cg.slot (routeLabels labels edge.decl)).width) ho ht hne
    have hm' : lane ∈ run.lanes.runs := by rw [hlr]; exact hm
    have hn := List.find?_eq_none.mp hf lane hm'
    exact hn (by simp only [hor, beq_self_eq_true])
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
    rcases RouteImpl.pieceOf_cases hpiece with ⟨hpc, _⟩ | ⟨hpc, hturn⟩
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
    · have hmidGap := componentRunX_forward_turn_gap (hvalid hturn) hrun hi hrev hturn
      have hmid' : run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail ≤
          RouteImpl.midOf run.proper P.slot run.top
            (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing i ∧
          RouteImpl.midOf run.proper P.slot run.top
            (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing i ≤
          run.ys.getD head 0 := ⟨Int.le_trans hgap.1 hmidGap.1, Int.le_trans hmidGap.2 hgap.2.2⟩
      rw [hpts, hpc]
      have hv : v < run.proper.nodes.length := by
        rcases hend with ⟨rfl, _⟩ | rfl
        · exact htail
        · exact hhead
      rw [plain_frame_eq_boxRect P cg run v hv hplain]
      apply Polyline.not_hits_of_allMiss
      rw [RouteImpl.allSegsMiss_iff]
      apply RouteImpl.pairsAll_dedup
      have hx : (RouteImpl.pieceEnd run.proper run.ys run.lanes.routing i).x =
          run.lanes.routing.targetX.getD i 0 := rfl
      rw [← hx]
      rcases hend with ⟨rfl, hnotTop⟩ | rfl
      · apply turnPortMisses
        have hstart : (RouteImpl.pieceStart run.proper run.ys run.lanes.routing i).y =
            run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail := by
          simp [tail, RouteImpl.pieceStart, RouteImpl.yAt, hnotTop]
        have hfinish : (RouteImpl.pieceEnd run.proper run.ys run.lanes.routing i).y =
            run.ys.getD head 0 := rfl
        simp only [RouteImpl.boxRect, hstart, hfinish, RouteImpl.yAt]
        exact ⟨Int.le_refl _, hmid'.1, hbottomTop⟩
      · apply turnPortMissesAbove
        have hstart : (RouteImpl.pieceStart run.proper run.ys run.lanes.routing i).y ≤
            run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail := by
          change (if RouteImpl.frameKind run.proper tail = -2 then run.ys.getD tail 0
            else run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail) ≤ _
          split
          · have hh := (hsizes tail htail).2
            omega
          · exact Int.le_refl _
        exact ⟨Int.le_trans hstart hbottomTop, hmid'.2, Int.le_refl _⟩

private theorem exact_tailPortY_eq_bottom {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {y : List Int} {v : Nat} (hv : v < run.proper.nodes.length) :
    RouteImpl.tailPortY run.proper y v = RouteImpl.yAt y v + RouteImpl.nodeH run.proper v := by
  by_cases htop : RouteImpl.frameKind run.proper v = -2
  · obtain ⟨_, _, labeled, q, _, _, hcoord, _, _, hproxy, hdrop, _, _, _⟩ :=
      componentRunX_spec hrun
    obtain ⟨_, _, hlen, _, hlookup, _⟩ := proxyWidths_rel hproxy
    have hnodes : run.proper.nodes = q.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
    have hvc : v < run.coordinateProper.nodes.length := by rwa [hnodes, hlen] at hv
    obtain ⟨src, hsrc⟩ : ∃ src, run.coordinateProper.nodes[v]? = some src :=
      ⟨_, List.getElem?_eq_getElem hvc⟩
    obtain ⟨dst, hdst, _, hborder, hheight⟩ := hlookup v src hsrc
    have hd : run.proper.nodes[v]? = some dst := by rwa [hnodes]
    have hb := ((isTop_iff hd).mp htop).2
    rw [hborder] at hb
    rw [← hcoord] at hsrc
    unfold coordinateGraphX at hsrc
    obtain ⟨base, hbase, _, hbBase, hhBase, _⟩ := materialize_lookup _ hsrc
    obtain ⟨_, hborders, hside⟩ :=
      addClusterBorders_extra (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
    rw [clearProxyExtents_nodes, hborders] at hbase
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hbase)
    have hbRaw := (clearF_keys raw).2.1.symm.trans (hbBase.symm.trans hb)
    have hhRaw : raw.node.h = 0 := by
      rcases List.mem_append.mp hraw with htitle | hextra
      · rw [titleReservations_nodes] at htitle
        rcases List.mem_append.mp htitle with hbody | hcopy
        · obtain ⟨origin, _, rfl⟩ := List.mem_map.mp hbody
          exact (titleF_keys origin).2.2.2
            (Or.inl ((titleF_keys origin).2.1.symm.trans hbRaw))
        · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hcopy
          change (3 : Int) = -2 at hbRaw
          omega
      · have hsideBorder := (hside raw hextra).2
        omega
    have hzero := hheight.trans (hhBase.trans ((clearF_keys raw).2.2.2.trans hhRaw))
    simp only [RouteImpl.tailPortY, ite_eq_left htop, RouteImpl.nodeH, hd, hzero, Int.add_zero]
  · rw [RouteImpl.tailPortY, ite_eq_right htop]

private theorem reversePortMissAbove {r : Rect} {sx lane tx tr sy ty cs ct : Int}
    (h : sy ≤ r.y ∧ cs ≤ r.y ∧ ct ≤ r.y ∧ ty ≤ r.y) :
    RouteImpl.pairsAll (fun a b => Polyline.segMisses a b r)
      [⟨sx, sy⟩, ⟨sx, cs⟩, ⟨lane, cs⟩, ⟨lane, ct⟩,
        ⟨tr, ct⟩, ⟨tr, ty⟩, ⟨tx, ty⟩] :=
  ⟨RouteImpl.miss_above (by dsimp; omega), RouteImpl.miss_above (by dsimp; omega),
    RouteImpl.miss_above (by dsimp; omega), RouteImpl.miss_above (by dsimp; omega),
    RouteImpl.miss_above (by dsimp; omega), RouteImpl.miss_above (by dsimp; omega), trivial⟩

private theorem reversePortMissBelow {r : Rect} {sx lane tx tr sy ty cs ct : Int}
    (h : r.y + r.h ≤ sy ∧ r.y + r.h ≤ cs ∧ r.y + r.h ≤ ct ∧ r.y + r.h ≤ ty) :
    RouteImpl.pairsAll (fun a b => Polyline.segMisses a b r)
      [⟨sx, sy⟩, ⟨sx, cs⟩, ⟨lane, cs⟩, ⟨lane, ct⟩,
        ⟨tr, ct⟩, ⟨tr, ty⟩, ⟨tx, ty⟩] :=
  ⟨RouteImpl.miss_below (by dsimp; omega), RouteImpl.miss_below (by dsimp; omega),
    RouteImpl.miss_below (by dsimp; omega), RouteImpl.miss_below (by dsimp; omega),
    RouteImpl.miss_below (by dsimp; omega), RouteImpl.miss_below (by dsimp; omega), trivial⟩

theorem componentRunX_reverse_direct_attached_frame_miss
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hP : P.Valid)
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {rt : EdgeRoute} (hrt : rt ∈ run.routes)
    {lane : RouteImpl.ReversedLane}
    (hf : run.lanes.runs.find? (fun candidate => candidate.original == rt.original) = some lane)
    {i : Nat} (hchain : RouteImpl.edgesOf run.proper rt.original = [i])
    {v : Nat} (hend : v = (RouteImpl.edgeAt run.proper i).tail ∨
      v = (RouteImpl.edgeAt run.proper i).head)
    (hplain : (cg.nodes.getD v default).border ≠ -2) :
    ¬ Polyline.hitsRect rt.points (frameRect P cg run v) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, _, hpoints⟩ := componentRunX_spec hrun
  have hi : i < run.proper.edges.length :=
    RouteImpl.mem_edgesOf (o := rt.original) (by rw [hchain]; simp)
  obtain ⟨_, hsizes, _, _, hedges⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hr).1
  let tail := (RouteImpl.edgeAt run.proper i).tail
  let head := (RouteImpl.edgeAt run.proper i).head
  have htail : tail < run.proper.nodes.length := (hedges i hi).1
  have hhead : head < run.proper.nodes.length := (hedges i hi).2.1
  have hm := List.mem_of_find?_eq_some hf
  have hor : lane.original = rt.original := by
    simpa only [beq_iff_eq] using List.find?_some hf
  obtain ⟨base, _, _, hlr⟩ := RouteImpl.routeWithLanes_spec hr
  have hplanned : lane ∈ RouteImpl.plannedLanes P.slot run.proper base run.xs
      (cg.edges.map (·.reversed))
      (cg.edges.map fun edge => (stackSize cg.slot (routeLabels labels edge.decl)).width) := by
    rw [hlr] at hm
    exact hm
  have hends := RouteImpl.plannedLane_endpoints (i₀ := i) (i₁ := i) hplanned
    (by rw [hor, hchain]; rfl) (by rw [hor, hchain]; rfl)
  obtain ⟨_, _, hsource, htarget, hsg, htg, _⟩ := hends
  have hlane : v = lane.sourceNode ∨ v = lane.targetNode := by
    rcases hend with htail' | hhead'
    · exact Or.inr (htail'.trans htarget.symm)
    · exact Or.inl (hhead'.trans hsource.symm)
  have hmem : lane ∈ run.lanes.runs := List.mem_of_find?_eq_some hf
  have hrunG : componentRunGen P (sizeProperPortsX P (exactDecls exactIds inp))
      (reserveExactRanks cg (exactDecls exactIds inp) labels)
      (cg.nodes.zipIdx.filterMap fun q =>
        if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none)
      cg labels orderOptions = .ok run := by
    rw [← componentRunX_eq_gen]
    exact hrun
  obtain ⟨_, hgap, hslot, hhalf⟩ := hP
  have hmids := RouteImpl.laneRun_mid_bounds hr hslot
    (CoordsImpl.half_slot_le_rankGapAt hgap hhalf run.proper run.layers)
    (fun _ hk => componentRunGen_rank_step_lower (runHooksShift_exact P exactIds inp cg labels)
      hrunG hk) hmem
  rw [hsg, htg] at hmids
  have hband := componentRunX_edge_rank_gap hrun hi
  have hsourceLow := Int.le_trans hband.1 hmids.1.1
  have hsourceHigh := Int.le_trans hmids.1.2 hband.2.2
  have htargetLow := Int.le_trans hband.1 hmids.2.1
  have htargetHigh := Int.le_trans hmids.2.2 hband.2.2
  have hbottomTop : run.ys.getD tail 0 + RouteImpl.nodeH run.proper tail ≤ run.ys.getD head 0 :=
    Int.le_trans hsourceLow hsourceHigh
  obtain ⟨_, he⟩ := RouteImpl.routePointsWithLanes_mem hpoints hrt
  simp only [RouteImpl.laneRouteOf, hf] at he
  split at he
  · simp only [Except.ok.injEq] at he
    have hpts : rt.points = RouteImpl.dedup
        (RouteImpl.reversedPoints P.slot run.proper run.ys run.top
          (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing lane) := by
      exact congrArg EdgeRoute.points he.symm
    have hv : v < run.proper.nodes.length := by
      rcases hlane with rfl | rfl
      · rw [hsource]; exact hhead
      · rw [htarget]; exact htail
    rw [plain_frame_eq_boxRect P cg run v hv hplain, hpts]
    apply Polyline.not_hits_of_allMiss
    rw [RouteImpl.allSegsMiss_iff]
    apply RouteImpl.pairsAll_dedup
    unfold RouteImpl.reversedPoints
    rcases hlane with rfl | rfl
    · apply reversePortMissAbove
      simp only [RouteImpl.boxRect, RouteImpl.yAt, hsource, htarget, hsg, htg]
      exact ⟨Int.le_refl _, hsourceHigh, htargetHigh,
        Int.le_trans (RouteImpl.tailPortY_le_bottom (y := run.ys) (hsizes tail htail).2)
          hbottomTop⟩
    · apply reversePortMissBelow
      have hport := exact_tailPortY_eq_bottom (y := run.ys)
        (v := (RouteImpl.edgeAt run.proper i).tail) hrun htail
      simp only [RouteImpl.boxRect, RouteImpl.yAt, hsource, htarget, hsg, htg, hport]
      exact ⟨hbottomTop, hsourceLow, htargetLow, Int.le_refl _⟩
  · simp at he

theorem componentRunX_oneEdge_attached_frame_miss
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hP : P.Valid)
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {rt : EdgeRoute} (hrt : rt ∈ run.routes)
    {i : Nat} (hchain : RouteImpl.edgesOf run.proper rt.original = [i])
    {v : Nat} (hend : (v = (RouteImpl.edgeAt run.proper i).tail ∧
      RouteImpl.frameKind run.proper v ≠ -2) ∨ v = (RouteImpl.edgeAt run.proper i).head)
    (hplain : (cg.nodes.getD v default).border ≠ -2) :
    ¬ Polyline.hitsRect rt.points (frameRect P cg run v) := by
  cases hf : run.lanes.runs.find? (fun lane => lane.original == rt.original) with
  | none =>
    exact componentRunX_direct_attached_frame_miss hrun hrt hf hchain (fun _ => hP) hend hplain
  | some lane =>
    have hend' : v = (RouteImpl.edgeAt run.proper i).tail ∨
        v = (RouteImpl.edgeAt run.proper i).head := by
      rcases hend with ⟨h, _⟩ | h
      · exact Or.inl h
      · exact Or.inr h
    exact componentRunX_reverse_direct_attached_frame_miss hP hrun hrt hf hchain hend' hplain

/-- In an executed flat exact parent, a one-edge route misses its selected
    endpoint's plain frame after packing and scene transport. -/
theorem X_chosen_part_oneEdge_attached_frame_miss
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
    {j : Nat} (hchain : RouteImpl.edgesOf run.proper i = [j])
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
  have hmiss := componentRunX_oneEdge_attached_frame_miss
    (exactIds := exactIds) (inp := inp) (checkedParams_valid execution.checked) hrun hmem
    (by rw [horig]; exact hchain) hend hplain
  rw [hrEq, hbEq]
  let bounds := placeBoundsX execution.params
    (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops
  exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
    execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY

end Elegant.Layered.PipelineImpl

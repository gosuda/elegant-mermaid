import Elegant.Layered.ExpandChildParentPortMissProof
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactStraightenFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RouteImpl

private theorem ordered_chain_intervals {p : Proper} {entry exit : Nat → Int}
    (hjoin : ∀ i j, ChainLink p i j → exit i ≤ entry j) :
    ∀ indices : List Nat, chainRel (ChainLink p) indices →
      (∀ i ∈ indices, entry i ≤ exit i) →
      ∀ first last, indices.head? = some first → indices.getLast? = some last →
        ∀ i ∈ indices, entry first ≤ entry i ∧ exit i ≤ exit last
  | [], _, _, _, _, hf, _, _, _ => by simp at hf
  | [a], _, _, first, last, hf, hl, i, hi => by
    have he : i = a := List.mem_singleton.mp hi
    rw [he, ← Option.some.inj hf, ← Option.some.inj hl]
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  | a :: b :: rest, hc, hspan, first, last, hf, hl, i, hi => by
    have he : a = first := Option.some.inj hf
    subst first
    have hlast : (b :: rest).getLast? = some last := by
      simpa only [List.getLast?_cons_cons] using hl
    have ih := ordered_chain_intervals hjoin (b :: rest) hc.2
      (fun j hj => hspan j (List.mem_cons_of_mem a hj)) b last rfl hlast
    have hab := hjoin a b hc.1
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ⟨Int.le_refl _, Int.le_trans hab
        (Int.le_trans (hspan b (by simp)) (ih b (by simp)).2)⟩
    · obtain ⟨hlo, hhi⟩ := ih i hi
      exact ⟨Int.le_trans (hspan a (by simp)) (Int.le_trans hab hlo), hhi⟩

private theorem pairsMiss_of_y_interval (rect : Rect) (lo hi : Int)
    (hside : rect.y + rect.h ≤ lo ∨ hi ≤ rect.y) :
    ∀ points : List Point, (∀ pt ∈ points, lo ≤ pt.y ∧ pt.y ≤ hi) →
      pairsAll (fun a b => Polyline.segMisses a b rect) points
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, hin => by
    refine ⟨?_, pairsMiss_of_y_interval rect lo hi hside (b :: rest)
      (fun pt hp => hin pt (List.mem_cons_of_mem a hp))⟩
    have ha := hin a (by simp)
    have hb := hin b (by simp)
    rcases hside with hbelow | habove
    · apply miss_below
      omega
    · apply miss_above
      omega

private theorem dedup_misses_of_y_interval {rect : Rect} {lo hi : Int} {points : List Point}
    (hside : rect.y + rect.h ≤ lo ∨ hi ≤ rect.y)
    (hin : ∀ pt ∈ points, lo ≤ pt.y ∧ pt.y ≤ hi) :
    ¬ Polyline.hitsRect (dedup points) rect := by
  apply Polyline.not_hits_of_allMiss
  rw [allSegsMiss_iff]
  exact pairsAll_dedup _ points (pairsMiss_of_y_interval rect lo hi hside points hin)

private theorem exact_plain_endpoint_kind {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node) (hborder : node.border = 0) :
    frameKind run.proper v = 0 := by
  obtain ⟨_, _, _, _, hn, hl, hc, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨out, hout, _, hb, _, _⟩ :=
    coordinateGraphX_plain_anchor_dims P (exact := exact) hsource hborder
  have hcoord : run.coordinateProper.nodes[v]? = some out := by
    rw [← hc]
    exact hout
  have hproper := ((proxyWidths_rel hproxy).2.2.2.2.2 v out hcoord (by rw [hb]; decide)).1
  have hout' : run.proper.nodes[v]? = some out := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
    exact hproper
  simp only [frameKind, hout', hb, ite_self]

/-- For any non-self exact route, including a chain of multiple proper edges, the native
    route misses the open interior of either plain endpoint. The ordinary route visits
    the chain in order; the reversed lane uses gaps at the chain's two ends. -/
theorem componentRunX_nonloop_attached_frame_miss
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hP : P.Valid)
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge) (hne : edge.tail ≠ edge.head)
    {rt : EdgeRoute} (hrt : rt ∈ run.routes) (horig : rt.original = i)
    {v : Nat} (hend : v = edge.tail ∨ v = edge.head)
    (hplain : (cg.nodes.getD v default).border = 0) :
    ¬ Polyline.hitsRect rt.points (frameRect P cg run v) := by
  obtain ⟨_, _, _, _, hn, _, _, _, _, _, _, hroute, _, hpoints⟩ := componentRunX_spec hrun
  obtain ⟨ho, hrouteOf⟩ := routePointsWithLanes_mem hpoints hrt
  obtain ⟨first, last, hf, hl, ht, hh⟩ := X_componentRun_chain_endpoints hrun hedge hne
  let indices := edgesOf run.proper rt.original
  have hfirst : indices.head? = some first := by simpa only [indices, horig] using hf
  have hlast : indices.getLast? = some last := by simpa only [indices, horig] using hl
  have hmFirst : first ∈ indices := List.mem_of_head? hfirst
  have hmLast : last ∈ indices := List.mem_of_getLast? hlast
  have hshape : chainRel (ChainLink run.proper) indices := componentRunX_properShape hrun _
  obtain ⟨_, hsizes, _, _, hedges⟩ := layersOk_spec (routeWithLanes_geometry hroute).1
  have hends : v = (edgeAt run.proper first).tail ∨ v = (edgeAt run.proper last).head := by
    simpa only [ht, hh] using hend
  have hv : v < run.proper.nodes.length := by
    rcases hends with he | he
    · rw [he]
      exact (hedges first (RouteImpl.mem_edgesOf hmFirst)).1
    · rw [he]
      exact (hedges last (RouteImpl.mem_edgesOf hmLast)).2.1
  have hvGraph : v < cg.nodes.length := by
    have hbounds := RankImpl.wellformed_spec (normalize_node_rank_alignment hn).2
      edge (List.mem_of_getElem? hedge)
    rcases hend with he | he
    · rw [he]; exact hbounds.1
    · rw [he]; exact hbounds.2.1
  have hnode := List.getElem?_eq_getElem hvGraph
  have hborder : (cg.nodes[v]'hvGraph).border = 0 := by
    simpa only [List.getD_eq_getElem?_getD, hnode, Option.getD_some] using hplain
  have hkind := exact_plain_endpoint_kind hrun hnode hborder
  rw [plain_frame_eq_boxRect P cg run v hv (by rw [hplain]; decide)]
  let rect := boxRect run.proper run.xs run.ys v
  let tailY := fun j => yAt run.ys (edgeAt run.proper j).tail
  let bottom := fun j => tailY j + nodeH run.proper (edgeAt run.proper j).tail
  let finish := fun j => yAt run.ys (edgeAt run.proper j).head
  let start := fun j => (pieceStart run.proper run.ys run.lanes.routing j).y
  have hheight (j : Nat) (hj : j < run.proper.edges.length) : tailY j ≤ bottom j :=
    Int.le_add_of_nonneg_right (hsizes _ (hedges j hj).1).2
  have hstart (j : Nat) (hj : j < run.proper.edges.length) :
      tailY j ≤ start j ∧ start j ≤ bottom j := by
    change tailY j ≤ (if frameKind run.proper (edgeAt run.proper j).tail = -2 then
      tailY j else bottom j) ∧
      (if frameKind run.proper (edgeAt run.proper j).tail = -2 then tailY j else bottom j) ≤ bottom j
    by_cases ht : frameKind run.proper (edgeAt run.proper j).tail = -2
    · simpa only [ite_eq_left ht] using And.intro (Int.le_refl (tailY j)) (hheight j hj)
    · simpa only [ite_eq_right ht] using And.intro (hheight j hj) (Int.le_refl (bottom j))
  have hband (j : Nat) (hj : j < run.proper.edges.length) :=
    componentRunX_edge_rank_gap hrun hj
  have hbottom (j : Nat) (hj : j < run.proper.edges.length) : bottom j ≤ finish j := by
    obtain ⟨hlo, hgap, hhi⟩ := hband j hj
    exact Int.le_trans hlo (Int.le_trans hgap hhi)
  have hjoin (a b : Nat) (hab : ChainLink run.proper a b) : finish a = tailY b := by
    change yAt run.ys (edgeAt run.proper a).head = yAt run.ys (edgeAt run.proper b).tail
    rw [hab.2.2.1]
  have hgen : componentRunGen P (sizeProperPortsX P (exactDecls exactIds inp))
      (reserveExactRanks cg (exactDecls exactIds inp) labels)
      (cg.nodes.zipIdx.filterMap fun q =>
        if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none)
      cg labels orderOptions = .ok run := by
    rw [← componentRunX_eq_gen]
    exact hrun
  obtain ⟨_, hgap, hslot, hhalf⟩ := hP
  have hhalfGap := CoordsImpl.half_slot_le_rankGapAt hgap hhalf run.proper run.layers
  have hstep := fun k hk =>
    componentRunGen_rank_step_lower (runHooksShift_exact P exactIds inp cg labels) hgen (k := k) hk
  obtain ⟨base, _, _, hlas⟩ := routeWithLanes_spec hroute
  cases hfind : run.lanes.runs.find? (fun lane => lane.original == rt.original) with
  | none =>
    have hrev : (cg.edges.map (·.reversed)).getD rt.original false = false := by
      apply Bool.eq_false_iff.mpr
      intro hr
      have hnonempty : (edgesOf run.proper rt.original).isEmpty = false :=
        List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hmFirst)
      obtain ⟨lane, hm, hor⟩ := plannedLane_exists (slot := P.slot) (p := run.proper) (base := base)
        (x := run.xs) (widths := cg.edges.map fun e =>
          (stackSize cg.slot (routeLabels labels e.decl)).width) ho hr hnonempty
      have hmem : lane ∈ run.lanes.runs := by rw [hlas]; exact hm
      exact (List.find?_eq_none.mp hfind lane hmem) (by simp only [hor, beq_self_eq_true])
    have horder := ordered_chain_intervals (entry := start) (exit := finish)
      (fun a b hab => by rw [hjoin a b hab]; exact (hstart b hab.2.1).1)
      indices hshape (fun j hj =>
        Int.le_trans (hstart j (RouteImpl.mem_edgesOf hj)).2 (hbottom j (RouteImpl.mem_edgesOf hj)))
      first last hfirst hlast
    simp only [laneRouteOf, hfind, routeOf] at hrouteOf
    split at hrouteOf
    · simp at hrouteOf
    · next pieces hpieces =>
      rw [congrArg EdgeRoute.points (Except.ok.inj hrouteOf).symm]
      apply dedup_misses_of_y_interval (rect := rect) (lo := start first) (hi := finish last)
      · rcases hends with he | he
        · left
          have hk : frameKind run.proper (edgeAt run.proper first).tail = 0 := by
            rw [← he]; exact hkind
          change yAt run.ys v + nodeH run.proper v ≤ start first
          rw [he]
          simp [start, pieceStart, hk]
        · right
          change finish last ≤ yAt run.ys v
          simpa only [he] using (Int.le_refl (finish last))
      · intro pt hpt
        obtain ⟨piece, hp, hpt⟩ := List.mem_flatten.mp hpt
        obtain ⟨j, hj, hpiece⟩ := mapOk_mem _ _ _ hpieces piece hp
        have hj' := RouteImpl.mem_edgesOf hj
        obtain ⟨hlo, hhi⟩ := horder j hj
        have hlocal := Int.le_trans (hstart j hj').2 (hbottom j hj')
        have hstartIn := And.intro hlo (Int.le_trans hlocal hhi)
        have hendIn := And.intro (Int.le_trans hlo hlocal) hhi
        rcases pieceOf_cases hpiece with ⟨rfl, _⟩ | ⟨rfl, hturn⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpt
          rcases hpt with rfl | rfl | rfl
          · exact hstartIn
          · exact hstartIn
          · exact hendIn
        · have hrevJ : (cg.edges.map (·.reversed)).getD
              (edgeAt run.proper j).original false = false := by
            rw [(PipelineImpl.mem_edgesOf.mp hj).2]
            exact hrev
          have hmid := forward_mid_bounds hroute hslot (hhalfGap (gapOf run.proper j)) hj'
            hrevJ hturn (hstep _ (forward_gap_valid hroute hj'))
          obtain ⟨hb, _, he⟩ := hband j hj'
          have hmidIn := And.intro
            (Int.le_trans hlo (Int.le_trans (hstart j hj').2 (Int.le_trans hb hmid.1)))
            (Int.le_trans hmid.2 (Int.le_trans he hhi))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpt
          rcases hpt with rfl | rfl | rfl | rfl | rfl
          · exact hstartIn
          · exact hstartIn
          · exact hmidIn
          · exact hmidIn
          · exact hendIn
  | some lane =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hor : lane.original = rt.original := by
      simpa only [beq_iff_eq] using List.find?_some hfind
    have hplanned : lane ∈ plannedLanes P.slot run.proper base run.xs
        (cg.edges.map (·.reversed))
        (cg.edges.map fun e => (stackSize cg.slot (routeLabels labels e.decl)).width) := by
      rw [hlas] at hmem
      exact hmem
    have hmem' : lane ∈ run.lanes.runs := List.mem_of_find?_eq_some hfind
    obtain ⟨_, _, hsource, htarget, hsg, htg, _⟩ := plannedLane_endpoints hplanned
      (by rw [hor]; exact hfirst) (by rw [hor]; exact hlast)
    have hmids := laneRun_mid_bounds hroute hslot hhalfGap hstep hmem'
    rw [hsg, htg] at hmids
    have horder := ordered_chain_intervals (entry := bottom) (exit := finish)
      (fun a b hab => by rw [hjoin a b hab]; exact hheight b hab.2.1)
      indices hshape (fun j hj => hbottom j (RouteImpl.mem_edgesOf hj)) first last hfirst hlast
    have hport : tailPortY run.proper run.ys (edgeAt run.proper first).tail ≤ bottom first :=
      tailPortY_le_bottom (hsizes _ (hedges first (RouteImpl.mem_edgesOf hmFirst)).1).2
    have hchannel {j : Nat} (hj : j ∈ indices) {z : Int}
        (hz₀ : run.top.getD (gapOf run.proper j) 0 +
          (run.layers.map (RouteImpl.layerHeight run.proper)).getD (gapOf run.proper j) 0 ≤ z)
        (hz₁ : z ≤ run.top.getD (gapOf run.proper j + 1) 0) :
        tailPortY run.proper run.ys (edgeAt run.proper first).tail ≤ z ∧ z ≤ finish last := by
      obtain ⟨hlo, hhi⟩ := horder j hj
      obtain ⟨hb, _, he⟩ := hband j (RouteImpl.mem_edgesOf hj)
      exact ⟨Int.le_trans (Int.le_trans hport hlo) (Int.le_trans hb hz₀),
        Int.le_trans hz₁ (Int.le_trans he hhi)⟩
    have hcs := hchannel hmLast hmids.1.1 hmids.1.2
    have hct := hchannel hmFirst hmids.2.1 hmids.2.2
    have hspan := Int.le_trans hcs.1 hcs.2
    simp only [laneRouteOf, hfind] at hrouteOf
    split at hrouteOf
    · rw [congrArg EdgeRoute.points (Except.ok.inj hrouteOf).symm]
      change ¬ Polyline.hitsRect
        (dedup (reversedPoints P.slot run.proper run.ys run.top
          (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes.routing lane)) rect
      apply dedup_misses_of_y_interval (rect := rect)
        (lo := tailPortY run.proper run.ys (edgeAt run.proper first).tail) (hi := finish last)
      · rcases hends with he | he
        · left
          have hk : frameKind run.proper (edgeAt run.proper first).tail = 0 := by
            rw [← he]
            exact hkind
          change yAt run.ys v + nodeH run.proper v ≤
            tailPortY run.proper run.ys (edgeAt run.proper first).tail
          rw [he]
          simp [tailPortY, hk]
        · right
          change finish last ≤ yAt run.ys v
          simpa only [he] using (Int.le_refl (finish last))
      · intro pt hpt
        simp only [reversedPoints, hsource, htarget, hsg, htg,
          List.mem_cons, List.not_mem_nil, or_false] at hpt
        rcases hpt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hspan, Int.le_refl _⟩
        · exact hcs
        · exact hcs
        · exact hct
        · exact hct
        · exact ⟨Int.le_refl _, hspan⟩
        · exact ⟨Int.le_refl _, hspan⟩
    · simp at hrouteOf

/-- Selected-part transport for a fixed endpoint frame in a flat exact parent.
    Its fixed-size entry gives the plain graph node; ordinary routes cannot select a loop placement. -/
theorem X_chosen_part_nonloop_attached_frame_miss
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
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head)
    {v key : Nat} (hkey : q.1.1[v]? = some key)
    {src : ModelBox} (hsrc : inp.boxes[key]? = some src)
    {entry : String × Size} (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == src.id) = some entry)
    (hend : v = edge.tail ∨ v = edge.head)
    {pr : Route} (hpr : res.scene.routes[edge.decl]? = some pr)
    {frame : Box} (hframe : res.scene.layoutDump.box? src.id = some frame) :
    ¬ Polyline.hitsRect pr.points frame.rect := by
  let cg := componentCandidate execution.graph q.1.1 candidate
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup execution.graph q.1.1 candidate
      (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
  have hloop := componentLoops_excludes_ordinary_decl hloops hnd hedge hne
  obtain ⟨route0, native, hrouteD, hnative, horig, hscene⟩ :=
    X_chosen_part_route_entry execution packed hpacked hselected hrun hpart hedge hloop
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    have hlen := (mapM_getElem? _ _ _ h).1
    simpa only [List.length_zipIdx] using hlen
  have hk : key < execution.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hsrc).1
  obtain ⟨_, _, base, _, _, hbase, hb, _⟩ :=
    measuredGraph_fixed_loop_reservation execution.graph0_eq hk hsrc hfixed
  obtain ⟨node, hnode, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hbase
  have hplain : (cg.nodes.getD v default).border = 0 := by
    dsimp only [cg]
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.getD_eq_getElem?_getD, List.getElem?_map, hkey,
      Option.map_some, Option.getD_some, hnode]
    exact hborder.trans hb
  have hmiss := componentRunX_nonloop_attached_frame_miss (exactIds := exactIds) (inp := inp)
    (checkedParams_valid execution.checked) hrun hedge hne (List.mem_of_getElem? hnative)
    horig hend hplain
  have hbox :=
    X_DumpLookup_holds exactIds execution hwf packed hpacked hselected hpart hkey hsrc
  have hsuff : res.scene.routes[edge.decl]? =
      some (Route.mk route0.id route0.fromId route0.toId route0.orthogonal
        (native.points.map (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY))) →
      ¬ Polyline.hitsRect pr.points frame.rect := by
    intro hscene0
    have hrEq := Option.some.inj (hpr.symm.trans hscene0)
    have hbEq := Option.some.inj (hframe.symm.trans hbox)
    have hmem : native ∈ run.routes := List.mem_of_getElem? hnative
    rw [hrEq, hbEq]
    let bounds := placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops
    exact parent_port_miss_transport hmiss execution.params.canvasMargin o.direction
      execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY
  simp only at hscene
  rcases hscene with hscene | ⟨pts, hcor, hrouteC⟩
  · exact hsuff hscene
  · -- Corridor case: the scene route is a straightened corridor.
    have hgetD : execution.straightAcc.routes.getD edge.decl [] = pts :=
      ExactStraighten.straight_points_of_scene execution hrouteC
    obtain ⟨cx0, y0, y1, hltCor, hptsCor⟩ := hcor
    have hptsNe : pts ≠ [] := by
      rw [hptsCor]
      intro hcon
      simp at hcon
    have hpts : execution.straightAcc.routes[edge.decl]? = some pts := by
      have hgd : (execution.straightAcc.routes[edge.decl]?.getD []) = pts := by
        have h := hgetD
        rw [Array.getD_eq_getD_getElem?] at h
        exact h
      cases ho : execution.straightAcc.routes[edge.decl]? with
      | none =>
        simp only [ho, Option.getD_none] at hgd
        exact absurd hgd.symm hptsNe
      | some v =>
        simp only [ho, Option.getD_some] at hgd
        exact congrArg Option.some hgd
    rcases ExactStraighten.route_cases execution X_componentRun_normalized_source hpts with hpackedPts | hinst
    · -- Packed subcase: the corridor coincides with the packed route; bridge to hsuff.
      have hi : i < (componentCandidate execution.graph q.1.1 candidate).edges.length :=
        (List.getElem?_eq_some_iff.mp hedge).1
      have he : (componentCandidate execution.graph q.1.1 candidate).edges[i]'hi = edge :=
        (List.getElem?_eq_some_iff.mp hedge).2
      have hlo : ∀ l ∈ loops, l.1 ≠ ((componentCandidate execution.graph q.1.1 candidate).edges[i]).decl := by
        simpa only [he] using hloop
      have hgetP := X_placeComponentExact_route_entry_of_producer hrun 0 loops i hi hlo
      have hpartRoutes : q.1.2.routes =
          (placeComponentExact execution.params (componentCandidate execution.graph q.1.1 candidate)
            run 0 execution.measured loops).routes := by
        rw [hpart]
      rw [← hpartRoutes] at hgetP
      have hndP : ((componentCandidate execution.graph q.1.1 candidate).edges.map (·.decl)).Nodup :=
        componentCandidate_decls_nodup execution.graph q.1.1 candidate
          (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
      have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
        rw [hpartRoutes]
        exact ExactStraighten.placeComponentExact_routes_decls_nodup execution.params
          (componentCandidate execution.graph q.1.1 candidate) run 0
          execution.measured loops hndP
      have hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
        rw [← packAcc_routes_size execution.packed_eq]
        exact (Array.getElem?_eq_some_iff.mp hpackedPts).1
      have heP := (List.getElem?_eq_some_iff.mp hedge).2
      have hpackedRoute := ExactStraighten.actual_components_packAcc_routes_getD
        (by rfl) execution.components_eq (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
        packed execution.packed_eq hpacked c q hselected i _ _ [] hgetP hpartNodup (by rw [heP]; exact hrouteSize)
      have hnativeGet := (List.getElem?_eq_some_iff.mp hnative).2
      have hk' : edge.decl < inp.routes.length := (List.getElem?_eq_some_iff.mp hrouteD).1
      have hmodelEq : inp.routes[edge.decl]'hk' = route0 :=
        Option.some.inj ((List.getElem?_eq_getElem hk').symm.trans hrouteD)
      have hbridge : execution.packedAcc.routes.getD edge.decl [] =
          execution.straightAcc.routes.getD edge.decl [] := by
        rw [hgetD, Array.getD_eq_getD_getElem?, hpackedPts, Option.getD_some]
      have hneg : -(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
          run execution.measured loops).minY =
          0 - (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
          run execution.measured loops).minY := by omega
      have hstraight0 := sceneOf_routes_getElem? execution.params inp o execution.lines
        execution.straightAcc execution.measured edge.decl hk'
      rw [← execution.scene_eq] at hstraight0
      rw [ExactStraighten.straight_canvasH execution] at hstraight0
      rw [heP, hbridge] at hpackedRoute
      rw [hneg] at hpackedRoute
      rw [hmodelEq] at hstraight0
      rw [hpackedRoute, routePointTransport_eq, hnativeGet] at hstraight0
      exact hsuff hstraight0
    · -- Installed subcase: the corridor belongs to our part; it misses the endpoint frame.
      obtain ⟨tailKey, headKey, tailRect, headRect, span,
          hEdgeTailLt, hEdgeHeadLt, htailLt, hheadLt, hKeyT, hKeyH,
          htailRect, hheadRect, h0tail, h0head,
          htxT, htwT, htxH, htwH, hxT1, hxT2, hxH1, hxH2, hy0eq, hy1eq, hptsEq⟩ :=
        execution.installed_part_edge_rects hinst hselected hedge rfl hrun hpart
      have hptsEq2 : pts = [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] := by
        rw [hptsEq]
        rfl
      have htopLt : span.top < span.bottom := by
        have heq : ([⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] : List Point) =
            ([⟨cx0, y0⟩, ⟨cx0, y1⟩] : List Point) := by
          rw [← hptsEq2, hptsCor]
        have h0 := congrArg List.head? heq
        have h1 := congrArg (fun l : List Point => l[1]?) heq
        simp only [List.head?_cons, List.getElem?_cons_succ] at h0 h1
        have hy0 : span.top = y0 := congrArg Point.y (Option.some.inj h0)
        have hy1 : span.bottom = y1 := congrArg Point.y (Option.some.inj h1)
        rw [hy0, hy1]
        exact hltCor
      have hprEq : pr.points =
          (([⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] : List Point).map fun p =>
            shiftPoint execution.params.canvasMargin execution.params.canvasMargin
              (orientPoint o.direction execution.packedAcc.canvasH p)) := by
        have heq := congrArg Route.points (Option.some.inj (hpr.symm.trans hrouteC))
        rw [hptsEq2] at heq
        exact heq
      rcases hend with hvT | hvH
      · -- Tail endpoint: corridor starts on the frame bottom edge.
        have hkeyEq : key = tailKey := by
          rw [hvT] at hkey
          exact Option.some.inj (hkey.symm.trans hKeyT)
        have hsrcLt : key < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsrc).1
        have hcompSize : execution.componentsAcc.rects.size = inp.boxes.length := by
          rw [execution.components_rects_size]
        have hsize : key < execution.componentsAcc.rects.size := by
          rw [hcompSize]
          exact hsrcLt
        have hiCg : v < (componentCandidate execution.graph q.1.1 candidate).nodes.length := by
          have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length = q.1.1.length := by
            rw [componentCandidate_nodes]
            simp only [componentGraph, List.length_map]
          rw [hlen]
          exact (List.getElem?_eq_some_iff.mp hkey).1
        have hrect : q.1.2.rects[v]? =
            some (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minX)
              (-(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minY)
              (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v)) := by
          have hp : q.1.2 = { placeComponentExact execution.params
              (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
              with area := area } := hpart
          rw [hp]
          unfold placeComponentExact placeBoundsX
          simp only [List.getElem?_map, List.getElem?_range hiCg, Option.map_some]
        have hentry : (q.1.1.zip q.1.2.rects)[v]? = some (key, shiftRect
            (0 - (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
              run execution.measured loops).minX)
            (-(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
              run execution.measured loops).minY)
            (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v)) :=
          List.getElem?_zip_eq_some.mpr ⟨hkey, hrect⟩
        have hpackV := actual_components_packed_rect_valueX (by rfl) execution.components_eq
          execution.packed_eq packed hpacked hselected hentry hsize default
        have htailGet : execution.packedAcc.rects.getD tailKey default = tailRect := by
          simp only [Array.getD_eq_getD_getElem?, htailRect, Option.getD_some]
        have hpackTail : tailRect =
            shiftRect q.2.x q.2.y (shiftRect
              (0 - (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minX)
              (-(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minY)
              (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v)) := by
          have h1 := hpackV
          rw [hkeyEq] at h1
          rw [Array.getD_eq_getD_getElem?] at h1
          rw [htailRect, Option.getD_some] at h1
          exact h1
        have hframeEq : frame.rect =
            shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH tailRect) := by
          have hb := hbox
          have hshift : shiftRect q.2.x q.2.y (shiftRect
              (0 - (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minX)
              (-(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minY)
              (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v)) =
              shiftRect (q.2.x - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minX)
                (q.2.y - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minY)
                (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v) := by
            dsimp only [shiftRect]
            congr 1 <;> omega
          have htailEq2 : tailRect =
              shiftRect (q.2.x - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minX)
                (q.2.y - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minY)
                (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v) :=
            hpackTail.trans hshift
          rw [← htailEq2] at hb
          have hbBox := Option.some.inj (hframe.symm.trans hb)
          exact congrArg Box.rect hbBox
        have hmissPack : ¬ Polyline.hitsRect [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] tailRect := by
          have htopEq : span.top = tailRect.y + tailRect.h := hy0eq
          exact ExactStraighten.corridor_misses_tail htopEq htopLt
        have hmissScene : ¬ Polyline.hitsRect
            (([⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] : List Point).map fun p =>
              shiftPoint execution.params.canvasMargin execution.params.canvasMargin
                (orientPoint o.direction execution.packedAcc.canvasH p))
            (shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH tailRect)) :=
          not_hitsRect_shift_orient o.direction execution.packedAcc.canvasH
            execution.params.canvasMargin execution.params.canvasMargin _ _ hmissPack
        rw [hprEq, hframeEq]
        exact hmissScene
      · -- Head endpoint: corridor ends on the frame top edge.
        have hkeyEq : key = headKey := by
          rw [hvH] at hkey
          exact Option.some.inj (hkey.symm.trans hKeyH)
        have hsrcLt : key < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsrc).1
        have hcompSize : execution.componentsAcc.rects.size = inp.boxes.length := by
          rw [execution.components_rects_size]
        have hsize : key < execution.componentsAcc.rects.size := by
          rw [hcompSize]
          exact hsrcLt
        have hiCg : v < (componentCandidate execution.graph q.1.1 candidate).nodes.length := by
          have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length = q.1.1.length := by
            rw [componentCandidate_nodes]
            simp only [componentGraph, List.length_map]
          rw [hlen]
          exact (List.getElem?_eq_some_iff.mp hkey).1
        have hrect : q.1.2.rects[v]? =
            some (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minX)
              (-(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minY)
              (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v)) := by
          have hp : q.1.2 = { placeComponentExact execution.params
              (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
              with area := area } := hpart
          rw [hp]
          unfold placeComponentExact placeBoundsX
          simp only [List.getElem?_map, List.getElem?_range hiCg, Option.map_some]
        have hentry : (q.1.1.zip q.1.2.rects)[v]? = some (key, shiftRect
            (0 - (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
              run execution.measured loops).minX)
            (-(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
              run execution.measured loops).minY)
            (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v)) :=
          List.getElem?_zip_eq_some.mpr ⟨hkey, hrect⟩
        have hpackV := actual_components_packed_rect_valueX (by rfl) execution.components_eq
          execution.packed_eq packed hpacked hselected hentry hsize default
        have hheadGet : execution.packedAcc.rects.getD headKey default = headRect := by
          simp only [Array.getD_eq_getD_getElem?, hheadRect, Option.getD_some]
        have hpackHead : headRect =
            shiftRect q.2.x q.2.y (shiftRect
              (0 - (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minX)
              (-(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minY)
              (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v)) := by
          have h1 := hpackV
          rw [hkeyEq] at h1
          rw [Array.getD_eq_getD_getElem?] at h1
          rw [hheadRect, Option.getD_some] at h1
          exact h1
        have hframeEq : frame.rect =
            shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH headRect) := by
          have hb := hbox
          have hshift : shiftRect q.2.x q.2.y (shiftRect
              (0 - (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minX)
              (-(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
                run execution.measured loops).minY)
              (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v)) =
              shiftRect (q.2.x - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minX)
                (q.2.y - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minY)
                (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v) := by
            dsimp only [shiftRect]
            congr 1 <;> omega
          have hheadEq2 : headRect =
              shiftRect (q.2.x - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minX)
                (q.2.y - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured loops).minY)
                (frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run v) :=
            hpackHead.trans hshift
          rw [← hheadEq2] at hb
          have hbBox := Option.some.inj (hframe.symm.trans hb)
          exact congrArg Box.rect hbBox
        have hmissPack : ¬ Polyline.hitsRect [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] headRect := by
          have hbotEq : span.bottom = headRect.y := hy1eq
          exact ExactStraighten.corridor_misses_head hbotEq htopLt
        have hmissScene : ¬ Polyline.hitsRect
            (([⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] : List Point).map fun p =>
              shiftPoint execution.params.canvasMargin execution.params.canvasMargin
                (orientPoint o.direction execution.packedAcc.canvasH p))
            (shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH headRect)) :=
          not_hitsRect_shift_orient o.direction execution.packedAcc.canvasH
            execution.params.canvasMargin execution.params.canvasMargin _ _ hmissPack
        rw [hprEq, hframeEq]
        exact hmissScene

end Elegant.Layered.PipelineImpl

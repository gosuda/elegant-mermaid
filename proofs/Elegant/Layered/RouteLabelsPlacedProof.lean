import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExecutedPortsFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- A `findIdx?` hit exposes its index, element, and predicate value. -/
theorem sweep_findIdx_lookup {α : Type} {p : α → Bool}
    {l : List α} {n : Nat} (h : l.findIdx? p = some n) :
    n < l.length ∧ ∃ a, l[n]? = some a ∧ p a = true := by
  induction l generalizing n with
  | nil =>
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons a as ih =>
    rw [List.findIdx?_cons] at h
    by_cases hp : p a = true
    · rw [ite_eq_left hp] at h
      have hn : n = 0 := (Option.some.inj h).symm
      subst hn
      exact ⟨Nat.zero_lt_succ _, a, rfl, hp⟩
    · rw [ite_eq_right hp] at h
      obtain ⟨m, hmfind, hmn⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hmlen, x, hxget, hpx⟩ := ih hmfind
      rw [← hmn]
      exact ⟨Nat.succ_lt_succ hmlen, x, (List.getElem?_cons_succ).trans hxget, hpx⟩

/-- A matching `getElem?` rules out `findIdx? = none`. -/
theorem sweep_findIdx_some_of_mem {α : Type} {p : α → Bool}
    {l : List α} {edge : Nat} {e : α}
    (hget : l[edge]? = some e) (hp : p e = true) :
    ∃ n, l.findIdx? p = some n := by
  cases hq : l.findIdx? p with
  | some n => exact ⟨n, rfl⟩
  | none =>
    have hmem : e ∈ l := List.mem_of_getElem? hget
    have hfalse : p e = false := List.findIdx?_eq_none_iff.mp hq e hmem
    rw [hp] at hfalse
    exact Bool.noConfusion hfalse

/-- Membership in `routeLabels` pins the edge key. -/
theorem sweep_routeLabels_edge {labels : List MeasuredLabel} {l : MeasuredLabel}
    {decl : Nat} (h : l ∈ routeLabels labels decl) : (l.edge == decl) = true := by
  have hmem := (List.mem_filter.mp h).2
  exact hmem

/-- Membership in `routeLabels` lifts to the full label list. -/
theorem sweep_mem_of_routeLabels {labels : List MeasuredLabel} {l : MeasuredLabel}
    {decl : Nat} (h : l ∈ routeLabels labels decl) : l ∈ labels :=
  (List.mem_filter.mp h).1

/-- `stackRects` preserves length. -/
theorem sweep_stackRects_length (x y gap : Int) (sizes : List (Int × Int)) :
    (Labels.stackRects x y gap sizes).length = sizes.length := by
  induction sizes generalizing y with
  | nil => rfl
  | cons _ rest ih =>
    simp only [Labels.stackRects, List.length_cons, ih]

/-- The index-keyed `find?` over a zipped stack always hits. -/
theorem sweep_zip_find_some {labels : List MeasuredLabel} {rects : List Rect}
    {l : MeasuredLabel}
    (hmem : l ∈ labels) (hlen : rects.length = labels.length) :
    ∃ pr, (labels.zip rects).find? (fun q => q.1.index == l.index) = some pr := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  have hilt : i < labels.length := (List.getElem?_eq_some_iff.mp hi).1
  have hirt : i < rects.length := by omega
  have hr : rects[i]? = some rects[i] := List.getElem?_eq_getElem hirt
  have hzip : (labels.zip rects)[i]? = some (l, rects[i]) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨hi, hr⟩
  have hmemz : (l, rects[i]) ∈ labels.zip rects := List.mem_of_getElem? hzip
  have hpred : (((l, rects[i]).1.index == l.index)) = true := by simp
  cases hq : (labels.zip rects).find? (fun q => q.1.index == l.index) with
  | some pr => exact ⟨pr, rfl⟩
  | none =>
    have hcontra := List.find?_eq_none.mp hq (l, rects[i]) hmemz
    exact absurd hpred hcontra

/-- Nonempty `routeLabels` has a head. -/
theorem sweep_routeLabels_head {labels : List MeasuredLabel} {decl : Nat}
    {l : MeasuredLabel} (hmem : l ∈ routeLabels labels decl) :
    ∃ first, (routeLabels labels decl).head? = some first := by
  cases hr : routeLabels labels decl with
  | nil => rw [hr] at hmem; simp at hmem
  | cons first _ => exact ⟨first, rfl⟩

/-- Loop envelopes always exist. -/
theorem sweep_envelope_loop {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge}
    (hloop : e.tail = e.head)
    (hmem : ∃ l, l ∈ routeLabels labels e.decl) :
    ∃ env, labelEnvelope P cg run labels k e = some env := by
  obtain ⟨l, hl⟩ := hmem
  obtain ⟨first, hfirst⟩ := sweep_routeLabels_head hl
  unfold labelEnvelope
  rw [hfirst]
  have hb : (e.tail == e.head) = true := by simp [hloop]
  simp [hb]

/-- Forward envelopes exist on successful runs via the executed anchor. -/
theorem sweep_envelope_forward {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {k : Nat} {e : Edge} {first : MeasuredLabel}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hk : cg.edges[k]? = some e) (hne : e.tail ≠ e.head) (hrev : e.reversed = false)
    (hfirst : (routeLabels labels e.decl).head? = some first) :
    ∃ env, labelEnvelope P cg run labels k e = some env := by
  obtain ⟨ranks, p0, labeled, projected, hn, hl, hc, _, _, hproxy, hdrop, _,
    _, _, _, _⟩ := componentRun_spec hrun
  obtain ⟨halign0, hwf⟩ := normalize_node_rank_alignment hn
  obtain ⟨hlrank, hlkeys⟩ := addLabelNodes_anchor_keys hl
  have hlen : labeled.nodes.length = p0.nodes.length := by
    have he := congrArg List.length hlkeys
    simpa only [List.length_map] using he
  have halign : labeled.nodes.length = labeled.rank.length := by
    rw [hlen, hlrank, halign0]
  have hedgeBounds := RankImpl.wellformed_spec hwf e (List.mem_of_getElem? hk)
  have htailBound : e.tail < labeled.rank.length := by
    rw [hlrank]
    have hlt : e.tail < cg.nodes.length := hedgeBounds.1
    have hle := normalize_nodes_length_le hn
    omega
  have hheadBound : e.head < labeled.rank.length := by
    rw [hlrank]
    have hlt : e.head < cg.nodes.length := hedgeBounds.2.1
    have hle := normalize_nodes_length_le hn
    omega
  obtain ⟨index, nd, hi, hnode, _, _⟩ :=
    componentLabels_selected_size hk hne hfirst hl
  have hedge : nd.edge = some k := labelAnchorIndex_node_edge hi hnode
  have hplain : EdgeAnchorsPlain labeled :=
    addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain hn) hl
  have hborder : nd.node.border = 0 :=
    hplain nd (List.mem_of_getElem? hnode) (by rw [hedge]; simp)
  obtain ⟨out, hout, hedgeOut, hborderOut, _, _⟩ :=
    coordinateGraph_plain_anchor_dims P hnode hborder
  have hkeysPrefix := (coordinateGraph_anchor_prefix P labeled).1
  have hrankPrefix := (coordinateGraph_anchor_prefix P labeled).2
  have hicoord := labelAnchorIndex_prefix halign hkeysPrefix hrankPrefix hi
  rw [hc] at hout hicoord hrankPrefix
  obtain ⟨_, hprank, _, _, _, hpreserve⟩ := proxyWidths_rel hproxy
  have hne2 : ¬ (out.node.border = -2 ∨ out.node.border = 2) := by
    rw [hborderOut]
    omega
  obtain ⟨hpnode, _⟩ := hpreserve index out hout hne2
  have hlookup : run.proper.nodes[index]? = some out := by
    rw [← hdrop]
    exact hpnode
  obtain ⟨_, hcrank⟩ := hrankPrefix
  have hfinalrank : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]
    exact hprank
  have htail : rk run.proper.rank e.tail = rk labeled.rank e.tail := by
    rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left htailBound]
  have hhead : rk run.proper.rank e.head = rk labeled.rank e.head := by
    rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left hheadBound]
  have hanchor : labelAnchorIndex run.proper k
      (rk run.proper.rank e.tail +
        Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) =
        some index := by
    rw [htail, hhead, ← hdrop]
    change labelAnchorIndex projected k _ = some index
    unfold labelAnchorIndex
    rw [proxyWidths_edge_keys hproxy, hprank]
    exact hicoord
  have hfind : ∃ q, run.proper.nodes.zipIdx.find? (fun qq =>
      qq.1.edge == some k &&
        rk run.proper.rank qq.2 ==
          (rk run.proper.rank e.tail +
            Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2)) =
      some q := by
    have heq := labelAnchorIndex_eq run.proper k
      (rk run.proper.rank e.tail +
        Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2)
    rw [hanchor] at heq
    cases hq : run.proper.nodes.zipIdx.find? (fun qq =>
        qq.1.edge == some k &&
          rk run.proper.rank qq.2 ==
            (rk run.proper.rank e.tail +
              Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2)) with
    | some q => exact ⟨q, rfl⟩
    | none => simp [hq] at heq
  obtain ⟨q, hq⟩ := hfind
  unfold labelEnvelope
  rw [hfirst]
  have hb : (e.tail == e.head) = false := by simp [hne]
  simp only [hb, hrev, hq]
  exact ⟨_, rfl⟩

/-- Reversed envelopes exist on successful runs via the lane routing. -/
theorem sweep_envelope_reversed {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {k : Nat} {e : Edge} {first : MeasuredLabel}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hk : cg.edges[k]? = some e) (hne : e.tail ≠ e.head) (hrev : e.reversed = true)
    (hfirst : (routeLabels labels e.decl).head? = some first) :
    ∃ env, labelEnvelope P cg run labels k e = some env := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hc, hord, hxs, hproxy, hdrop, hrLanes,
    _, _, _, _⟩ := componentRun_spec hrun
  have hklen : k < cg.edges.length := (List.getElem?_eq_some_iff.mp hk).1
  have hchains : k < run.proper.chains.length := by
    rw [componentRun_proper_chains_length hrun]
    exact hklen
  have hrevGet : (cg.edges.map (fun x => x.reversed))[k]? = some true := by
    rw [List.getElem?_map, hk]
    simp [hrev]
  have hrevD : (cg.edges.map (fun x => x.reversed)).getD k false = true := by
    rw [List.getD_eq_getElem?_getD, hrevGet]
    rfl
  obtain ⟨rnorm, norm, hnorm, hedgeEq, hchainEq⟩ :=
    componentRun_normalized_source hrun
  have hnormOk := normalize_ok hnorm
  have hfact := hnormOk.2.2 k hklen e hk
  unfold NormalizeImpl.ChainFact at hfact
  obtain ⟨_, hch⟩ := hfact
  rw [ite_eq_right hne] at hch
  obtain ⟨chl, hchl, hclen, _, _, hconsec⟩ := hch
  have h0 : 0 < chl.length := by omega
  have h1 : 1 < chl.length := by omega
  obtain ⟨pe, hpeMem, hpeOrig, _, _, _⟩ := hconsec 0 h0 h1
  have hpeMemRun : pe ∈ run.proper.edges := by
    rw [hedgeEq]
    exact hpeMem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpeMemRun
  have hilt : i < run.proper.edges.length := (List.getElem?_eq_some_iff.mp hi).1
  have hedgeAt : RouteImpl.edgeAt run.proper i = pe := by
    simp [RouteImpl.edgeAt, List.getD_eq_getElem?_getD, hi]
  have hpred : ((RouteImpl.edgeAt run.proper i).original == k) = true := by
    rw [hedgeAt, hpeOrig, beq_self_eq_true]
  have hmemRange : i ∈ List.range run.proper.edges.length :=
    List.mem_range.mpr hilt
  have hmemEdges : i ∈ RouteImpl.edgesOf run.proper k := by
    unfold RouteImpl.edgesOf
    exact List.mem_filter.mpr ⟨hmemRange, hpred⟩
  have hneEmpty : (RouteImpl.edgesOf run.proper k).isEmpty = false := by
    cases he : RouteImpl.edgesOf run.proper k with
    | nil => simp [he] at hmemEdges
    | cons _ _ => rfl
  have hmemLane : k ∈ RouteImpl.laneOriginals run.proper
      (cg.edges.map (fun x => x.reversed)) := by
    unfold RouteImpl.laneOriginals
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true]
    exact ⟨hchains, hrevD, by simpa using hneEmpty⟩
  obtain ⟨base, _, _, hlr⟩ := RouteImpl.routeWithLanes_spec hrLanes
  have hplanned : ∃ laneRun ∈ RouteImpl.plannedLanes P.slot run.proper base
      run.xs (cg.edges.map (fun x => x.reversed))
      ((cg.edges.map fun edge => (stackSize cg.slot (routeLabels labels edge.decl)).width))
      , laneRun.original = k := by
    apply RouteImpl.plannedLane_exists hchains hrevD
    simpa using hneEmpty
  obtain ⟨laneRun, hmlane, hmor⟩ := hplanned
  have hrunMem : laneRun ∈ run.lanes.runs := by
    rw [hlr]
    unfold RouteImpl.assembleLaneRouting
    simp only
    exact hmlane
  have hfindLane : ∃ lane, run.lanes.runs.find?
      (fun lane => lane.original == k) = some lane := by
    have hpredLane : (fun lane : RouteImpl.ReversedLane => lane.original == k) laneRun = true := by
      simp [hmor]
    cases hq : run.lanes.runs.find? (fun lane => lane.original == k) with
    | some lane => exact ⟨lane, rfl⟩
    | none =>
      have hcontra := List.find?_eq_none.mp hq laneRun hrunMem
      exact absurd hpredLane hcontra
  obtain ⟨lane, hlane⟩ := hfindLane
  unfold labelEnvelope
  rw [hfirst]
  have hb : (e.tail == e.head) = false := by simp [hne]
  simp only [hb, hrev, hlane]
  exact ⟨_, rfl⟩

/-- Every measured label on a successful run has a placed entry. -/
theorem routeLabelsPlaced : RouteLabelsPlaced := by
  intro P cg labels orderOptions run l edge e hrun hedge hmem
  have hedge_eq : (l.edge == e.decl) = true := sweep_routeLabels_edge hmem
  have hlab : l ∈ labels := sweep_mem_of_routeLabels hmem
  have heq : l.edge = e.decl := of_decide_eq_true hedge_eq
  have hpred : ((fun x : Edge => x.decl == l.edge) e) = true := by
    simp only
    rw [← heq]
    exact beq_self_eq_true _
  obtain ⟨edge', hfind⟩ :=
    sweep_findIdx_some_of_mem (p := fun x : Edge => x.decl == l.edge) hedge hpred
  obtain ⟨_, e', hget', hpred'⟩ := sweep_findIdx_lookup hfind
  have heq' : e'.decl = l.edge := of_decide_eq_true hpred'
  have hdeclEq : e'.decl = e.decl := heq'.trans heq
  have hmem' : l ∈ routeLabels labels e'.decl := by
    apply List.mem_filter.mpr
    refine ⟨hlab, ?_⟩
    have hll : l.edge = e'.decl := heq.trans hdeclEq.symm
    simp [hll]
  obtain ⟨first, hfirst⟩ := sweep_routeLabels_head hmem'
  obtain ⟨env, henv⟩ : ∃ env, labelEnvelope P cg run labels edge' e' = some env := by
    by_cases hloop : e'.tail = e'.head
    · exact sweep_envelope_loop hloop ⟨l, hmem'⟩
    · by_cases hrev : e'.reversed = true
      · exact sweep_envelope_reversed hrun hget' hloop hrev hfirst
      · have hrevF : e'.reversed = false := Bool.eq_false_of_ne_true hrev
        exact sweep_envelope_forward hrun hget' hloop hrevF hfirst
  have hlenStack : (Labels.stackRects env.x env.y cg.slot
      ((routeLabels labels e'.decl).map fun q => (q.width, q.height))).length =
      (routeLabels labels e'.decl).length := by
    rw [sweep_stackRects_length]
    simp
  obtain ⟨pr, hpr⟩ := sweep_zip_find_some (labels := routeLabels labels e'.decl)
    (rects := Labels.stackRects env.x env.y cg.slot
      ((routeLabels labels e'.decl).map fun q => (q.width, q.height)))
    hmem' hlenStack
  have hbind : (do
      let edge ← cg.edges.findIdx? (fun e => e.decl == l.edge)
      let e ← cg.edges[edge]?
      let envelope ← labelEnvelope P cg run labels edge e
      let siblings := routeLabels labels e.decl
      let rectangles := Labels.stackRects envelope.x envelope.y cg.slot
        (siblings.map fun q => (q.width, q.height))
      let placed ← (siblings.zip rectangles).find? (fun q => q.1.index == l.index)
      pure (l.index, placed.2)) = some (l.index, pr.2) := by
    simp [hfind, hget', henv, hpr]
  have hmemPlaced : (l.index, pr.2) ∈ placedLabels P cg run labels := by
    unfold placedLabels
    exact List.mem_filterMap.mpr ⟨l, hlab, hbind⟩
  exact ⟨pr.2, hmemPlaced⟩
end PipelineImpl
end Layered
end Elegant

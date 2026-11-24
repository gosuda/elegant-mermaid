import Elegant.Layered.RegionFlatC7
import Elegant.Layered.RegionFlatC4
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RouteLabelsPlacedProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem labelEdgeKey_set (nodes : Array ProperNode) (i : Nat) (n : ProperNode)
    (hkey : n.edge = (nodes.getD i default).edge) :
    (nodes.set! i n).toList.map ProperNode.edge = nodes.toList.map ProperNode.edge := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList]
  rw [Array.set!_eq_setIfInBounds]
  by_cases heq : i = j
  · subst j
    by_cases hi : i < nodes.size
    · rw [Array.getElem?_setIfInBounds_self_of_lt hi, Array.getElem?_eq_getElem hi]
      have hget : nodes.getD i default = nodes[i]'hi := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
      simpa only [Option.map_some, hget] using congrArg Option.some hkey
    · have hn : nodes[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_gt hi)
      have hs : (nodes.setIfInBounds i n)[i]? = none := by
        rw [Array.getElem?_setIfInBounds_self]
        simp [hi]
      rw [hs, hn]
  · rw [Array.getElem?_setIfInBounds_ne heq]

private theorem reservedLabelKeys_fold (pl : RegionPlacement) (cg : Graph)
    (labels : List MeasuredLabel) (clusters : List (RegionCluster × Nat))
    {start finish : List Int × Array ProperNode}
    (h : clusters.foldlM (fun acc q => do
      let c := q.1
      let footprint := max c.titleH
        (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
      if c.titleW < 0 ∨ footprint < 0 then throw LayoutError.domain
      else
        let x ← clusterPortR pl q.2 c.top acc.1
        let x ← clusterPortR pl q.2 c.bottom x
        let top := acc.2.getD c.top default
        let nodes := acc.2.set! c.top
          { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
        pure (x, nodes)) start = .ok finish) :
    finish.2.toList.map ProperNode.edge = start.2.toList.map ProperNode.edge := by
  induction clusters generalizing start with
  | nil =>
    have he : start = finish := Except.ok.inj h
    rw [he]
  | cons q rest ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok h
    dsimp only at hmid
    split at hmid
    · simp at hmid
    · obtain ⟨_, _, hmid⟩ := bind_ok hmid
      obtain ⟨_, _, hmid⟩ := bind_ok hmid
      rw [ih hrest]
      rw [← congrArg Prod.snd (Except.ok.inj hmid)]
      exact labelEdgeKey_set _ _ _ rfl

private theorem reservedLabelMetadata {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {x : List Int} {out : List Int × Proper}
    (h : reservedPortsR pl cg labels x = .ok out) :
    out.2.nodes.map ProperNode.edge = pl.p.nodes.map ProperNode.edge ∧
      out.2.rank = pl.p.rank ∧ out.2.edges = pl.p.edges ∧ out.2.chains = pl.p.chains := by
  unfold reservedPortsR at h
  obtain ⟨finish, hfold, hret⟩ := bind_ok h
  have hout : (finish.1, { pl.p with nodes := finish.2.toList }) = out := Except.ok.inj hret
  rw [← hout]
  refine ⟨?_, rfl, rfl, rfl⟩
  change finish.2.toList.map ProperNode.edge = pl.p.nodes.map ProperNode.edge
  rw [reservedLabelKeys_fold pl cg labels pl.rm.clusters.zipIdx hfold, List.toList_toArray]

theorem crossCoordsR_label_metadata {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)} {out : List Int × List (List Nat) × List (Option Int) × Proper}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok out) :
    out.2.2.2.nodes.map ProperNode.edge = p.nodes.map ProperNode.edge ∧
      out.2.2.2.rank = p.rank ∧ out.2.2.2.edges = p.edges ∧ out.2.2.2.chains = p.chains := by
  unfold crossCoordsR at h
  obtain ⟨_, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    exact absurd h (by simp)
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
    obtain ⟨⟨_, _⟩, hreserved, hret⟩ := bind_ok h
    rw [← Except.ok.inj hret]
    exact reservedLabelMetadata hreserved

private theorem mapLabelEdgeKeys (nodes : List ProperNode) (f : ProperNode → ProperNode)
    (h : ∀ n, (f n).edge = n.edge) :
    (nodes.map f).map ProperNode.edge = nodes.map ProperNode.edge := by
  simp only [List.map_map]
  exact congrArg (fun g => nodes.map g) (funext h)

theorem coordinateGraphR_label_prefix (P : Params) (exact : List Nat)
    (spec : Option RegionSpec) (p : Proper) :
    (∃ extra, (coordinateGraphR P exact spec p).nodes.map ProperNode.edge =
      p.nodes.map ProperNode.edge ++ extra) ∧
    (∃ extra, (coordinateGraphR P exact spec p).rank = p.rank ++ extra) := by
  cases spec with
  | none => exact coordinateGraphX_anchor_prefix P exact p
  | some s =>
    let sized := sizeProperPortsX P exact p
    let titled := titleReservationsR s.titles P.clusterPad sized
    have htrim : ((sized.nodes.map fun n =>
        if n.node.border == -2 || n.node.border == 2 then
          { n with node := { n.node with w := 0, h := 0 } } else n).map ProperNode.edge) =
        sized.nodes.map ProperNode.edge := by
      apply mapLabelEdgeKeys
      intro n
      split <;> rfl
    have ht : ∃ extra, titled.nodes.map ProperNode.edge = p.nodes.map ProperNode.edge ++ extra := by
      dsimp only [titled, titleReservationsR]
      rw [List.map_append, htrim, sizeProperPortsX_edge P exact p]
      exact ⟨_, rfl⟩
    have hr : ∃ extra, titled.rank = p.rank ++ extra := ⟨_, rfl⟩
    have hc (q : Proper) : (clearProxyExtents q).nodes.map ProperNode.edge =
        q.nodes.map ProperNode.edge := by
      rw [clearProxyExtents_nodes]
      apply mapLabelEdgeKeys
      intro n
      unfold clearF
      split <;> rfl
    have hm (q : Proper) : (materializeDummyPaths q).nodes.map ProperNode.edge =
        q.nodes.map ProperNode.edge := by
      unfold materializeDummyPaths
      apply map_edge_of_zipIdxMap
      intro n
      split <;> rfl
    obtain ⟨extraNodes, hn, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    obtain ⟨extraKeys, ht⟩ := ht
    obtain ⟨extraRanks, hr⟩ := hr
    obtain ⟨extraBorderRanks, hb⟩ := addClusterBorders_rank_prefix titled P.clusterBorderW
    constructor
    · change ∃ extra, (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders titled P.clusterBorderW))).nodes.map ProperNode.edge = _ ++ extra
      refine ⟨extraKeys ++ extraNodes.map ProperNode.edge, ?_⟩
      rw [hm, hc, hn, List.map_append, ht, List.append_assoc]
    · change ∃ extra, (OrderImpl.addClusterBorders titled P.clusterBorderW).rank = _ ++ extra
      refine ⟨extraRanks ++ extraBorderRanks, ?_⟩
      rw [hb, hr, List.append_assoc]

private theorem coordinateGraphR_routed_edges (P : Params) (exact : List Nat)
    (spec : Option RegionSpec) (p : Proper)
    (hclean : ∀ e ∈ p.edges, e.synthetic = false) :
    (OrderImpl.dropSynthetic (coordinateGraphR P exact spec p)).edges = p.edges := by
  cases spec with
  | none =>
    exact OrderImpl.dropSynthetic_addClusterBorders_edges
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW hclean
  | some s =>
    exact OrderImpl.dropSynthetic_addClusterBorders_edges
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact p)) P.clusterBorderW hclean

private theorem regionLabel_nonloop_edge {cg : Graph} {ranks : List Int}
    {normalized p : Proper} {k : Nat} {e : Edge}
    (hnorm : normalize cg ranks = .ok normalized) (hedges : p.edges = normalized.edges)
    (hk : cg.edges[k]? = some e) (hne : e.tail ≠ e.head) :
    (RouteImpl.edgesOf p k).isEmpty = false := by
  have hklen := (List.getElem?_eq_some_iff.mp hk).1
  have hchain := (normalize_ok hnorm).2.2 k hklen e hk
  unfold NormalizeImpl.ChainFact at hchain
  obtain ⟨_, hchain⟩ := hchain
  rw [ite_eq_right hne] at hchain
  obtain ⟨chain, _, hlen, _, _, hsegments⟩ := hchain
  obtain ⟨segment, hmem, horiginal, _, _, _⟩ :=
    hsegments 0 (by omega) (by omega)
  have hmem' : segment ∈ p.edges := by
    rw [hedges]
    exact hmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem'
  have hilt : i < p.edges.length := (List.getElem?_eq_some_iff.mp hi).1
  have hat : RouteImpl.edgeAt p i = segment := by
    simp [RouteImpl.edgeAt, List.getD_eq_getElem?_getD, hi]
  have hm : i ∈ RouteImpl.edgesOf p k := by
    unfold RouteImpl.edgesOf
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hilt, by simp [hat, horiginal]⟩
  cases hp : RouteImpl.edgesOf p k with
  | nil => simp [hp] at hm
  | cons _ _ => rfl

private theorem regionLabel_find_some {α : Type} {xs : List α} {f : α → Bool}
    {a : α} (ha : a ∈ xs) (hf : f a = true) : ∃ b, xs.find? f = some b := by
  cases hh : xs.find? f with
  | some b => exact ⟨b, rfl⟩
  | none => exact absurd hf (List.find?_eq_none.mp hh a ha)

theorem regionLabel_envelope_of_run {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {run : Run} {k : Nat} {e : Edge} {l : MeasuredLabel}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    (hk : cg'.edges[k]? = some e) (hl : l ∈ routeLabels labels e.decl) :
    ∃ env, labelEnvelope P cg' run labels k e = some env := by
  by_cases hloop : e.tail = e.head
  · exact sweep_envelope_loop hloop ⟨l, hl⟩
  obtain ⟨first, hfirst⟩ := sweep_routeLabels_head hl
  obtain ⟨_, _, _, p0, labeled, pCoord, _, _, labelWidths, reserved, placed, q0,
    _, _, hs⟩ := componentRunR_stages hrun
  have hmeta : placed.nodes.map ProperNode.edge = pCoord.nodes.map ProperNode.edge ∧
      placed.rank = pCoord.rank ∧ placed.edges = pCoord.edges ∧ placed.chains = pCoord.chains := by
    rcases hs.hPlaced with ⟨_, _, _, _, hp⟩ | ⟨_, _, _, _, hp⟩
    · rw [hp]; exact ⟨rfl, rfl, rfl, rfl⟩
    · exact crossCoordsR_label_metadata hp
  have hb : (e.tail == e.head) = false := by simp [hloop]
  by_cases hrev : e.reversed = true
  · have hlabeledEdges := (Labels.addLabelNodes_metadata hs.hLabels).1
    have hclean : ∀ pe ∈ labeled.edges, pe.synthetic = false := by
      rw [hlabeledEdges]
      exact normalize_clean hs.hNorm
    have hedges : run.proper.edges = p0.edges := by
      rw [← hs.hDrop]
      change q0.edges.filter (fun pe => !pe.synthetic) = _
      rw [(proxyWidths_rel hs.hProxy).1, hmeta.2.2.1]
      change (OrderImpl.dropSynthetic pCoord).edges = _
      rw [← hs.hCoord, coordinateGraphR_routed_edges P exact spec labeled hclean, hlabeledEdges]
    have hnonempty := regionLabel_nonloop_edge hs.hNorm hedges hk hloop
    have hchains : k < run.proper.chains.length := by
      have hc : pCoord.chains = labeled.chains := by
        rw [← hs.hCoord]
        cases spec with
        | none => exact coordinateGraphX_chains P exact labeled
        | some s =>
          exact (OrderImpl.addClusterBorders_metadata
            (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
            P.clusterBorderW).2.1
      rw [← hs.hDrop, OrderImpl.dropSynthetic_chains, proxyWidths_chains hs.hProxy,
        hmeta.2.2.2, hc, (Labels.addLabelNodes_metadata hs.hLabels).2.2.1,
        normalize_chains_length hs.hNorm]
      exact (List.getElem?_eq_some_iff.mp hk).1
    have hrevAt : (cg'.edges.map (·.reversed)).getD k false = true := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hk, hrev]
    have hLane : ∃ lane ∈ run.lanes.runs, lane.original = k := by
      rcases hs.hLanes with ⟨_, hr⟩ | ⟨_, hr⟩
      · obtain ⟨base, _, _, heq⟩ := RouteImpl.routeWithLanes_spec hr
        rw [heq]
        change ∃ lane ∈ RouteImpl.plannedLanes P.slot run.proper base run.xs
          (cg'.edges.map (·.reversed)) labelWidths, lane.original = k
        exact RouteImpl.plannedLane_exists hchains hrevAt hnonempty
      · obtain ⟨base, _, _, heq⟩ := routeWithLanesR_spec hr
        have hmem : k ∈ RouteImpl.laneOriginals run.proper (cg'.edges.map (·.reversed)) := by
          simp only [RouteImpl.laneOriginals, List.mem_filter, List.mem_range, Bool.and_eq_true,
            Bool.not_eq_true']
          exact ⟨hchains, hrevAt, hnonempty⟩
        rw [← List.zipIdx_map_fst 0 (RouteImpl.laneOriginals run.proper
          (cg'.edges.map (·.reversed)))] at hmem
        obtain ⟨q, hq, hqk⟩ := List.mem_map.mp hmem
        rw [heq]
        change ∃ lane ∈ (RouteImpl.laneOriginals run.proper (cg'.edges.map (·.reversed))).zipIdx.map
          (fun q => makeLaneR P.slot run.proper base run.xs (cg'.edges.map (·.reversed))
            labelWidths reserved (RouteImpl.laneOriginals run.proper (cg'.edges.map (·.reversed)))
            q.1 q.2), lane.original = k
        exact ⟨_, List.mem_map.mpr ⟨q, hq, rfl⟩, hqk⟩
    obtain ⟨lane, hLaneMem, hLaneKey⟩ := hLane
    obtain ⟨selected, hfind⟩ := regionLabel_find_some
      (f := fun lane : RouteImpl.ReversedLane => lane.original == k) hLaneMem (by simp [hLaneKey])
    unfold labelEnvelope
    rw [hfirst]
    simp only [hb, hrev, hfind]
    exact ⟨_, rfl⟩
  · have hrevF := Bool.eq_false_of_ne_true hrev
    have ⟨halign₀, hwf⟩ := normalize_node_rank_alignment hs.hNorm
    have ⟨hrank, hkeys⟩ := addLabelNodes_anchor_keys hs.hLabels
    have hlen : labeled.nodes.length = p0.nodes.length := by
      simpa only [List.length_map] using congrArg List.length hkeys
    have halign : labeled.nodes.length = labeled.rank.length := by rw [hlen, hrank, halign₀]
    have hbounds := RankImpl.wellformed_spec hwf e (List.mem_of_getElem? hk)
    have htail : e.tail < labeled.rank.length := by
      rw [← halign, hlen]
      exact Nat.lt_of_lt_of_le hbounds.1 (normalize_nodes_length_le hs.hNorm)
    have hhead : e.head < labeled.rank.length := by
      rw [← halign, hlen]
      exact Nat.lt_of_lt_of_le hbounds.2.1 (normalize_nodes_length_le hs.hNorm)
    obtain ⟨i, _, hi, _, _, _⟩ := componentLabels_selected_size hk hloop hfirst hs.hLabels
    have hp := coordinateGraphR_label_prefix P exact spec labeled
    rw [hs.hCoord] at hp
    have hCoordIdx := labelAnchorIndex_prefix halign hp.1 hp.2 hi
    obtain ⟨extra, hr⟩ := hp.2
    have hkeyOut : run.proper.nodes.map ProperNode.edge = pCoord.nodes.map ProperNode.edge := by
      rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes, proxyWidths_edge_keys hs.hProxy, hmeta.1]
    have hrankOut : run.proper.rank = pCoord.rank := by
      rw [← hs.hDrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hs.hProxy).2.1, hmeta.2.1]
    have htailOut : rk run.proper.rank e.tail = rk labeled.rank e.tail := by
      rw [hrankOut, hr, NormalizeImpl.rk_append_left htail]
    have hheadOut : rk run.proper.rank e.head = rk labeled.rank e.head := by
      rw [hrankOut, hr, NormalizeImpl.rk_append_left hhead]
    let mid := rk run.proper.rank e.tail +
      Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2
    have hIdx : labelAnchorIndex run.proper k mid = some i := by
      dsimp only [mid]
      rw [htailOut, hheadOut]
      unfold labelAnchorIndex at hCoordIdx ⊢
      rwa [hkeyOut, hrankOut]
    rw [labelAnchorIndex_eq] at hIdx
    obtain ⟨_, hfind, _⟩ := Option.map_eq_some_iff.mp hIdx
    dsimp only [mid] at hfind
    unfold labelEnvelope
    rw [hfirst]
    simp only [hb, hrevF, hfind]
    exact ⟨_, rfl⟩

theorem regionLabel_routeLabelsPlaced : R7_RouteLabelsPlaced := by
  intro P exact spec inp cg cg' labels orderOptions run l edge e hrun hedge hl
  have hlabel : l ∈ labels := sweep_mem_of_routeLabels hl
  have hdecl : l.edge = e.decl := of_decide_eq_true (sweep_routeLabels_edge hl)
  obtain ⟨selected, hselected⟩ := sweep_findIdx_some_of_mem
    (p := fun e : Edge => e.decl == l.edge) hedge (by simp [hdecl])
  obtain ⟨_, owner, howner, hownerDecl⟩ := sweep_findIdx_lookup hselected
  have hownerKey : owner.decl = l.edge := of_decide_eq_true hownerDecl
  have hmember : l ∈ routeLabels labels owner.decl := by
    exact List.mem_filter.mpr ⟨hlabel, by simp [hownerKey]⟩
  obtain ⟨env, henv⟩ := regionLabel_envelope_of_run hrun howner hmember
  have hlen : (Labels.stackRects env.x env.y cg'.slot
      ((routeLabels labels owner.decl).map fun q => (q.width, q.height))).length =
      (routeLabels labels owner.decl).length := by
    rw [sweep_stackRects_length, List.length_map]
  obtain ⟨pr, hpr⟩ := sweep_zip_find_some hmember hlen
  refine ⟨pr.2, List.mem_filterMap.mpr ⟨l, hlabel, ?_⟩⟩
  simp [hselected, howner, henv, hpr]

end Elegant.Layered.PipelineImpl

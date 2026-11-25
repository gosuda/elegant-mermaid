import Elegant.Layered.RegionReservedChildTransfer
import Elegant.Layered.RegionC8aGroupPlain
import Elegant.Layered.RegionPartSizingClosed

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

abbrev r8bForwardPrepared (P : Params) (exact : List Nat) (s : RegionSpec) (q : Proper) : Proper :=
  clearProxyExtents (OrderImpl.addClusterBorders
    (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact q)) P.clusterBorderW)

private theorem r8b_title_edge (n : ProperNode) : (titleF n).edge = n.edge := by
  unfold titleF
  split <;> rfl

private theorem r8b_clear_edge (n : ProperNode) : (clearF n).edge = n.edge := by
  unfold clearF
  split <;> rfl

private theorem r8b_border_key_prefix (q : Proper) (w : Int) :
    ∃ extra : List (Option Nat),
      (OrderImpl.addClusterBorders q w).nodes.map ProperNode.edge =
        q.nodes.map ProperNode.edge ++ extra ∧ ∀ x ∈ extra, x = none := by
  let inv (p : Proper) := ∃ extra : List (Option Nat),
    p.nodes.map ProperNode.edge = q.nodes.map ProperNode.edge ++ extra ∧ ∀ x ∈ extra, x = none
  unfold OrderImpl.addClusterBorders
  apply OrderImpl.foldl_inv inv _ _ q ⟨[], by simp, by simp⟩
  intro p hp top _
  dsimp only
  split
  · exact hp
  · apply OrderImpl.foldl_inv inv _ _ p hp
    intro st hst _ _
    obtain ⟨extra, he, hn⟩ := hst
    refine ⟨extra ++ [none, none], ?_, ?_⟩
    · simp [List.map_append, he, List.append_assoc]
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hn x hx
      · simpa using hx

private theorem r8b_prepared_key_prefix (P : Params) (exact : List Nat) (s : RegionSpec)
    {q : Proper} (hplain : EdgeAnchorsPlain q) :
    ∃ extra : List (Option Nat),
      (r8bForwardPrepared P exact s q).nodes.map ProperNode.edge =
        q.nodes.map ProperNode.edge ++ extra ∧ ∀ x ∈ extra, x = none := by
  let sized := sizeProperPortsX P exact q
  let titled := titleReservationsR s.titles P.clusterPad sized
  have hsize : sized.nodes.map ProperNode.edge = q.nodes.map ProperNode.edge :=
    sizeProperPortsX_edge P exact q
  have htrim : (sized.nodes.map titleF).map ProperNode.edge = sized.nodes.map ProperNode.edge := by
    rw [List.map_map]
    apply List.map_congr_left
    intro n _
    exact r8b_title_edge n
  let tops := sized.nodes.zipIdx.filter fun a => a.1.node.border == -2
  let titleKeys := tops.map fun a => a.1.edge
  have hcopies : ∀ x ∈ titleKeys, x = none := by
    intro x hx
    change x ∈ tops.map (fun a => a.1.edge) at hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    change a ∈ sized.nodes.zipIdx.filter (fun a => a.1.node.border == -2) at ha
    obtain ⟨hm, ht⟩ := List.mem_filter.mp ha
    have hsz := List.mem_zipIdx_iff_getElem?.mp hm
    have hb : a.1.node.border = -2 := beq_iff_eq.mp ht
    have hk := sizeProperPortsX_key P exact q a.2
    change (sized.nodes[a.2]?).map _ = _ at hk
    have he := congrArg (fun xs : List (Option Nat) => xs[a.2]?) hsize
    cases hq : q.nodes[a.2]? with
    | none => simp [hsz, hq] at hk
    | some n =>
      simp only [List.getElem?_map, hsz, hq, Option.map_some, Option.some.injEq] at he
      simp only [hsz, hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      by_cases hn : a.1.edge = none
      · exact hn
      · have hzero := hplain n (List.mem_of_getElem? hq) (fun hz => hn (he.trans hz))
        have hb' := hk.2.1
        rw [hb, hzero] at hb'
        exact ((by decide : (-2 : Int) ≠ 0) hb').elim
  have ht : titled.nodes.map ProperNode.edge = q.nodes.map ProperNode.edge ++ titleKeys := by
    change ((sized.nodes.map titleF) ++ _).map ProperNode.edge = _
    rw [List.map_append, htrim, hsize, List.map_map]
    all_goals
      apply congrArg (fun keys : List (Option Nat) => q.nodes.map ProperNode.edge ++ keys)
      change _ = tops.map (fun a => a.1.edge)
      apply List.map_congr_left
      intro a _
      rfl
  obtain ⟨extra, hb, hn⟩ := r8b_border_key_prefix titled P.clusterBorderW
  have hc (t : Proper) : (clearProxyExtents t).nodes.map ProperNode.edge =
      t.nodes.map ProperNode.edge := by
    rw [clearProxyExtents_nodes, List.map_map]
    apply List.map_congr_left
    intro n _
    exact r8b_clear_edge n
  refine ⟨titleKeys ++ extra, ?_, ?_⟩
  · change (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes.map
      ProperNode.edge = q.nodes.map ProperNode.edge ++ (titleKeys ++ extra)
    rw [hc, hb, ht, List.append_assoc]
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hcopies x hx
    · exact hn x hx

theorem r8b_forwardPrepared_source (P : Params) (exact : List Nat) (s : RegionSpec)
    {labeled : Proper} {v : Nat} {src : ProperNode} (h : labeled.nodes[v]? = some src) :
    ∃ n, (r8bForwardPrepared P exact s labeled).nodes[v]? = some n ∧
      n.dummy = src.dummy ∧ n.edge = src.edge ∧ n.node.border = src.node.border ∧
      n.node.clusterPath = src.node.clusterPath := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  have ⟨n, hn, hd, he, hb, hp⟩ : ∃ n, sized.nodes[v]? = some n ∧ n.dummy = src.dummy ∧
      n.edge = src.edge ∧ n.node.border = src.node.border ∧ n.node.clusterPath = src.node.clusterPath := by
    simp only [sized, sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx,
      h, Option.map_some, Nat.zero_add]
    split <;> exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  have ht : titled.nodes[v]? = some (titleF n) := by
    change ((sized.nodes.map titleF) ++ _)[v]? = _
    rw [List.getElem?_append_left (by simpa only [List.length_map] using
      (List.getElem?_eq_some_iff.mp hn).1), List.getElem?_map, hn, Option.map_some]
  obtain ⟨_, hx, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  have hc : (r8bForwardPrepared P exact s labeled).nodes[v]? = some (clearF (titleF n)) := by
    change (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[v]? = _
    rw [clearProxyExtents_nodes, List.getElem?_map, hx,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1, ht, Option.map_some]
  have hEdge := (r8b_clear_edge (titleF n)).trans (r8b_title_edge n)
  exact ⟨_, hc, (clearF_keys _).1.trans ((titleF_keys _).1.trans hd), hEdge.trans he,
    (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hb),
    (clearF_keys _).2.2.1.trans ((titleF_keys _).2.2.1.trans hp)⟩

theorem r8b_forwardPrepared_endpoint (P : Params) (exact : List Nat) (s : RegionSpec)
    {cg : Graph} {ranks : List Int} {p0 labeled : Proper} {labels : List MeasuredLabel}
    (hnorm : normalize cg ranks = .ok p0)
    (hlab : Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled)
    {v : Nat} {raw : Node} (hraw : cg.nodes[v]? = some raw) :
    ∃ n, (r8bForwardPrepared P exact s labeled).nodes[v]? = some n ∧
      (coordinateGraphR P exact (some s) labeled).nodes[v]? = some n ∧
      n.node.clusterPath = raw.clusterPath := by
  have hlabel := addLabelNodes_untouched_node hlab (normalize_node_record hnorm hraw) rfl
  obtain ⟨n, hn, hd, _, _, hp⟩ := r8b_forwardPrepared_source P exact s hlabel
  have hf : n.dummy = false := hd
  refine ⟨n, hn, ?_, hp⟩
  change (materializeDummyPaths (r8bForwardPrepared P exact s labeled)).nodes[v]? = some n
  simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx, hn,
    Option.map_some, hf, Bool.false_eq_true, ↓reduceIte]

private theorem r8b_prepared_key_origin (P : Params) (exact : List Nat) (s : RegionSpec)
    {labeled : Proper} {v edge : Nat} {n : ProperNode}
    (hplain : EdgeAnchorsPlain labeled)
    (h : (r8bForwardPrepared P exact s labeled).nodes[v]? = some n) (hk : n.edge = some edge) :
    ∃ src, labeled.nodes[v]? = some src ∧ src.edge = some edge := by
  obtain ⟨extra, he, hnone⟩ := r8b_prepared_key_prefix P exact s hplain
  have hp : ((r8bForwardPrepared P exact s labeled).nodes.map ProperNode.edge)[v]? =
      some (some edge) := by simp only [List.getElem?_map, h, Option.map_some, hk]
  rw [he] at hp
  by_cases hv : v < labeled.nodes.length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using hv),
      List.getElem?_map] at hp
    exact Option.map_eq_some_iff.mp hp
  · have hb : (labeled.nodes.map ProperNode.edge).length ≤ v := by simpa using Nat.le_of_not_gt hv
    rw [List.getElem?_append_right hb] at hp
    have hbad := hnone _ (List.mem_of_getElem? hp)
    cases hbad

private theorem r8b_label_key_origin {cg : Graph} {ranks : List Int} {p0 labeled : Proper}
    {labels : List MeasuredLabel}
    (hnorm : normalize cg ranks = .ok p0)
    (hlab : Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled)
    {v edge : Nat} {src : ProperNode} (hsrc : labeled.nodes[v]? = some src)
    (hkey : src.edge = some edge) :
    ∃ old, p0.nodes[v]? = some old ∧ old.edge = some edge ∧ old.dummy = true ∧
      src.dummy = true ∧ cg.nodes.length ≤ v ∧ src.node.border = 0 := by
  have hkeys := (addLabelNodes_anchor_keys hlab).2
  have hv := congrArg (fun xs : List (Option Nat) => xs[v]?) hkeys
  simp only [List.getElem?_map, hsrc, Option.map_some, hkey] at hv
  obtain ⟨old, hold, hk⟩ := Option.map_eq_some_iff.mp hv.symm
  have hbound : cg.nodes.length ≤ v := by
    apply Nat.le_of_not_gt
    intro hlt
    have horig : cg.nodes[v]? = some cg.nodes[v] := List.getElem?_eq_getElem hlt
    have he := Option.some.inj ((normalize_node_record hnorm horig).symm.trans hold)
    rw [← he] at hk
    cases hk
  have hd : old.dummy = true := by
    rcases normalize_keys hnorm v old hold with ⟨n, hn, _⟩ | h
    · have hnlt := (List.getElem?_eq_some_iff.mp hn).1
      omega
    · exact h.1
  have hm := (Labels.addLabelNodes_metadata hlab).2.2.2 v
  have hplain := addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain hnorm) hlab
  exact ⟨old, hold, hk, hd, by simpa only [hsrc, hold, Option.map_some, Option.some.injEq, hd]
      using hm, hbound, hplain src (List.mem_of_getElem? hsrc) (by simp [hkey])⟩

private theorem r8b_cross_replay {P : Params} {rm : ComponentRegions} {cg : Graph}
    {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed) :
    crossCoordsR P rm cg labels p minimum layers = .ok (xs, pinned, reserved, placed) := by
  have htest : ¬ ((childPreorderGo stages.children (stages.children.length + 1)
      [rm.clusters.length] []).length != stages.children.length) :=
    fun h => (bne_iff_ne.mp h) stages.hTraversal
  unfold crossCoordsR
  simp only [stages.hChildren, bind, Except.bind, ite_eq_right htest, stages.hGroups]
  rw [← stages.hPinned]
  simp only [stages.hCross, stages.hSpans]
  rw [← stages.hPlacement]
  simp only [stages.hAllocation, stages.hFramesAndPorts, ← stages.hLanes]
  all_goals rfl

private theorem r8b_regionFrames_other {pl : RegionPlacement} {P : Params}
    {allocation : RegionAllocation} {xs : List Int} {v : Nat} {n : ProperNode}
    (hn : pl.p.nodes[v]? = some n) (hb : n.node.border = 0)
    (haway : ∀ c ∈ pl.rm.clusters, c.top ≠ v ∧ c.bottom ≠ v) :
    (regionFrames pl P allocation xs).getD v 0 = xs.getD v 0 := by
  have setOther (ys : List Int) (x : Int) {i j : Nat} (hi : i ≠ j) :
      (setAt ys i x).getD j 0 = ys.getD j 0 := by
    induction ys generalizing i j with
    | nil => rfl
    | cons y ys ih =>
      cases i with
      | zero => cases j with
        | zero => exact (hi rfl).elim
        | succ _ => rfl
      | succ i => cases j with
        | zero => rfl
        | succ j => exact ih (fun he => hi (congrArg Nat.succ he))
  unfold regionFrames
  apply OrderImpl.foldl_inv (fun x : List Int => x.getD v 0 = xs.getD v 0) _ _ _ rfl
  intro x hx job hj
  obtain ⟨ht, hb'⟩ := haway job.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hj))
  dsimp only
  rw [setOther _ _ hb', setOther _ _ ht]
  apply OrderImpl.foldl_inv (fun x : List Int => x.getD v 0 = xs.getD v 0) _ _ _ hx
  intro y hy q hq
  by_cases he : q.2 = v
  · have hlookup := List.mem_zipIdx_iff_getElem?.mp hq
    rw [he, hn] at hlookup
    have hz : q.1.node.border = 0 := by rw [← Option.some.inj hlookup, hb]
    simp only [hz]
    split <;> exact hy
  · have hwrite (value : Int) : (setAt y q.2 value).getD v 0 = xs.getD v 0 :=
      (setOther y value he).trans hy
    split
    · exact hy
    · split <;> first | exact hwrite _ | exact hy

private theorem r8b_active_marker_bounds {P : Params} {s : RegionSpec} {inp : Input}
    {candidate : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp candidate = .ok (some rm)) :
    ∀ c ∈ rm.clusters, c.top < candidate.nodes.length ∧ c.bottom < candidate.nodes.length := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bind_ok h
    split at h
    · cases h
    · have hrows : rm.clusters = clusterRows inp s candidate :=
        (congrArg ComponentRegions.clusters (Option.some.inj (Except.ok.inj h))).symm
      intro c hc
      rw [hrows] at hc
      unfold clusterRows at hc
      obtain ⟨q, hq, hc⟩ := List.mem_filterMap.mp hc
      dsimp only at hc
      split at hc
      · cases hc
      · rw [← Option.some.inj hc]
        have htop := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)).1
        refine ⟨htop, ?_⟩
        dsimp only
        split
        · rename_i b hb
          exact (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp
            (List.mem_of_find?_eq_some hb))).1
        · exact htop

set_option maxHeartbeats 6000000 in
theorem componentRunR_selectedAnchor_origin {P : Params} {exact : List Nat} {s : RegionSpec}
    {inp : Input} {candidate cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions} {ranks : List Int} {budget : Bool}
    {p0 labeled p : Proper} {minimum : RegionConstraints} {layers : List (List Nat)}
    {reserved : List (Option Int)}
    (hrun : componentRunR P exact (some s) inp candidate labels orderOptions = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hrank : rankEquivalentR rm candidate = .ok (ranks, cg, budget))
    (hnorm : normalize cg ranks = .ok p0)
    (hlab : Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled)
    (hcoord : coordinateGraphR P exact (some s) labeled = p)
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    {edge v : Nat} {rank : Int} {nd : ProperNode}
    (ha : labelAnchorIndex run.proper edge rank = some v)
    (hnd : run.proper.nodes[v]? = some nd) :
    p.nodes[v]? = some nd ∧ nd.node.border = 0 ∧ run.xs.getD v 0 = stages.shifted.getD v 0 ∧
      nd.dummy = true ∧ nd.edge = some edge ∧ cg.nodes.length ≤ v ∧
      ∃ old prepared, p0.nodes[v]? = some old ∧ old.edge = some edge ∧ old.dummy = true ∧
        (r8bForwardPrepared P exact s labeled).nodes[v]? = some prepared ∧
        prepared.dummy = true ∧ (r8bForwardPrepared P exact s labeled).chains = p0.chains := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, proxied, _, _, actual⟩ := componentRunR_stages hrun
  have hproxy : proxyWidths run.coordinateProper run.coordinateXs = .ok (proxied, run.xs) := by
    rw [actual.hCoordProper]
    exact actual.hProxy
  have hkeys : run.proper.nodes.map ProperNode.edge = p.nodes.map ProperNode.edge := by
    rw [← actual.hDrop, OrderImpl.dropSynthetic_nodes, proxyWidths_edge_keys hproxy,
      (crossCoordsR_label_metadata (r8b_cross_replay stages)).1]
  have hkey := labelAnchorIndex_node_edge ha hnd
  have hkeyLookup := congrArg (fun xs : List (Option Nat) => xs[v]?) hkeys
  simp only [List.getElem?_map, hnd, Option.map_some, hkey] at hkeyLookup
  obtain ⟨n, hn, hk⟩ := Option.map_eq_some_iff.mp hkeyLookup.symm
  let prepared := r8bForwardPrepared P exact s labeled
  have hmat : (materializeDummyPaths prepared).nodes[v]? = some n := by
    change (coordinateGraphR P exact (some s) labeled).nodes[v]? = some n
    rwa [hcoord]
  obtain ⟨before, hbefore, hndDummy, hndBorder, _, _⟩ := materialize_lookup prepared hmat
  have hbKey : before.edge = some edge := by
    simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx, hbefore,
      Option.map_some, Nat.zero_add, Option.some.injEq] at hmat
    split at hmat <;> rw [← hmat] at hk <;> exact hk
  have hplain := addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain hnorm) hlab
  obtain ⟨source, hsource, hsourceKey⟩ := r8b_prepared_key_origin P exact s hplain hbefore hbKey
  obtain ⟨old, hold, hOldKey, hOldDummy, hSourceDummy, hv, hSourcePlain⟩ :=
    r8b_label_key_origin hnorm hlab hsource hsourceKey
  obtain ⟨before', hbefore', hDummy, _, hBorder, _⟩ := r8b_forwardPrepared_source P exact s hsource
  have heq := Option.some.inj (hbefore'.symm.trans hbefore)
  subst before'
  have hBeforeDummy : before.dummy = true := hDummy.trans hSourceDummy
  have hBeforePlain : before.node.border = 0 := hBorder.trans hSourcePlain
  have hb : n.node.border = 0 := hndBorder.trans hBeforePlain
  have hpl : stages.placement.p = p := by rw [stages.hPlacement]
  have hrm : stages.placement.rm = rm := by rw [stages.hPlacement]
  have hpre : stages.placement.p.nodes[v]? = some n := by rwa [hpl]
  have haway : ∀ c ∈ stages.placement.rm.clusters, c.top ≠ v ∧ c.bottom ≠ v := by
    rw [hrm]
    intro c hc
    obtain ⟨ht, hbot⟩ := r8b_active_marker_bounds hactive c hc
    rw [← rankEquivalentR_nodes_eq hrank] at ht hbot
    exact ⟨by omega, by omega⟩
  obtain ⟨out, hout, _, hkeep⟩ := (groupPlain_reservedPorts_record stages.hFramesAndPorts).2 hpre
  obtain ⟨he, hx⟩ := hkeep haway
  subst out
  have hfinal : run.proper.nodes[v]? = some n := by
    rw [← actual.hDrop, OrderImpl.dropSynthetic_nodes]
    exact proxyWidths_plain_node hproxy hout hb
  have he := Option.some.inj (hnd.symm.trans hfinal)
  subst nd
  have hx' := componentRunR_placement_xsR hrun hout (by simp [hb])
  have hchains : prepared.chains = p0.chains := by
    change (OrderImpl.addClusterBorders
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
      P.clusterBorderW).chains = p0.chains
    rw [(OrderImpl.addClusterBorders_metadata _ _).2.1]
    exact (Labels.addLabelNodes_metadata hlab).2.2.1
  exact ⟨hn, hb, hx'.trans (hx.trans (r8b_regionFrames_other hpre hb haway)),
    hndDummy.trans hBeforeDummy, hkey, hv, old, before, hold, hOldKey, hOldDummy,
    hbefore, hBeforeDummy, hchains⟩

#print axioms r8b_forwardPrepared_source
#print axioms r8b_forwardPrepared_endpoint
#print axioms componentRunR_selectedAnchor_origin

end Elegant.Layered.PipelineImpl

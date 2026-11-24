import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.LabelsC7RunLocal

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Exact flat C7 forward branch.

Proves `X_RunLocalForwardSeparation` by replaying `runLocalForwardSeparation`
over `componentRunX_spec`. Shared label-envelope/stack/text lemmas are reused
directly; rank bands come from `X_ReserveBands_holds` (reserved `top`/`ys`
through `reserveExactRanks`); same-rank `x` separation replays
`componentRun_nonproxy_ordered_intervals` over the exact coordinate graph.

Target:
`theorem x_runLocalForwardSeparation_holds (exactIds : List String) :
  X_RunLocalForwardSeparation exactIds`
-/

/-- Dummy flags survive the exact coordinate-graph construction at a fixed
index (copy of `coordinateGraph_dummy_at` with the `sizeProperPortsX` first
step; all later steps are shared). -/
private theorem X_coordinateGraphX_dummy_at {P : Params} {exact : List Nat} {p : Proper}
    {i : Nat} {nd : ProperNode} (h : p.nodes[i]? = some nd) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.dummy = nd.dummy := by
  have hlen : (sizeProperPortsX P exact p).nodes.length = p.nodes.length :=
    sizeProperPortsX_length P exact p
  have hi : i < (sizeProperPortsX P exact p).nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp h).1
    omega
  obtain ⟨sized, hsized⟩ : ∃ sized,
      (sizeProperPortsX P exact p).nodes[i]? = some sized :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  have hkey := sizeProperPortsX_key P exact p i
  rw [h, hsized] at hkey
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
  have hd_sized : sized.dummy = nd.dummy := hkey.1
  obtain ⟨titled, htitled, hd_titled⟩ :
      ∃ titled, (titleReservations (sizeProperPortsX P exact p)).nodes[i]? =
        some titled ∧ titled.dummy = nd.dummy := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by
        have hlt := (List.getElem?_eq_some_iff.mp hsized).1
        simpa using hlt)]
    simp only [List.getElem?_map, hsized, Option.map_some]
    obtain ⟨ha1, -, -, -⟩ := titleF_keys sized
    exact ⟨_, rfl, by rw [ha1, hd_sized]⟩
  obtain ⟨bordered, hbordered, hd_bordered⟩ :
      ∃ bordered, (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? =
          some bordered ∧ bordered.dummy = nd.dummy := by
    obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
    have hlen2 : i < (titleReservations (sizeProperPortsX P exact p)).nodes.length :=
      (List.getElem?_eq_some_iff.mp htitled).1
    rw [hnodes, List.getElem?_append_left hlen2, htitled]
    exact ⟨_, rfl, hd_titled⟩
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
      (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]?.map
        clearF := by
    rw [clearProxyExtents_nodes, List.getElem?_map]
  obtain ⟨ha1, -, -, -⟩ := clearF_keys bordered
  simp only [coordinateGraphX, materializeDummyPaths, List.getElem?_map,
    List.getElem?_zipIdx, hclear, hbordered, Option.map_some]
  split
  · exact ⟨_, rfl, by simp [hd_bordered, ha1]⟩
  · exact ⟨_, rfl, by simp [hd_bordered, ha1]⟩

/-- The exact executed run carries the selected forward label stack at the
exact anchor the forward envelope uses (copy of `forward_anchor_full` with
`componentRunX_spec`, `coordinateGraphX_plain_anchor_dims`,
`coordinateGraphX_anchor_prefix`, and the exact dummy transport above). -/
private theorem X_forward_anchor_full {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {k : Nat} {edge : Edge} {first : MeasuredLabel}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hk : cg.edges[k]? = some edge) (hne : edge.tail ≠ edge.head)
    (hfirst : (routeLabels labels edge.decl).head? = some first) :
    ∃ index nd,
      labelAnchorIndex run.proper k
        (rk run.proper.rank edge.tail +
          Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2) =
          some index ∧
      run.proper.nodes[index]? = some nd ∧
      run.coordinateProper.nodes[index]? = some nd ∧
      nd.edge = some k ∧ nd.dummy = true ∧ nd.node.border = 0 ∧
      (stackSize cg.slot (routeLabels labels edge.decl)).width + first.gutter ≤
        nd.node.w ∧
      nd.node.h = (stackSize cg.slot (routeLabels labels edge.decl)).height := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hc, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨halign0, hwf⟩ := normalize_node_rank_alignment hn
  obtain ⟨hlrank, hlkeys⟩ := addLabelNodes_anchor_keys hl
  have hlen : labeled.nodes.length = p0.nodes.length := by
    have he := congrArg List.length hlkeys
    simpa only [List.length_map] using he
  have halign : labeled.nodes.length = labeled.rank.length := by
    rw [hlen, hlrank, halign0]
  have hedgeBounds := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hk)
  have htailBound : edge.tail < labeled.rank.length := by
    rw [hlrank]
    have hlt : edge.tail < cg.nodes.length := hedgeBounds.1
    have hle := normalize_nodes_length_le hn
    omega
  have hheadBound : edge.head < labeled.rank.length := by
    rw [hlrank]
    have hlt : edge.head < cg.nodes.length := hedgeBounds.2.1
    have hle := normalize_nodes_length_le hn
    omega
  obtain ⟨index, nd, hi, hnode, hw, hh⟩ :=
    componentLabels_selected_size hk hne hfirst hl
  have hedge : nd.edge = some k := labelAnchorIndex_node_edge hi hnode
  have hplain : EdgeAnchorsPlain labeled :=
    addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain hn) hl
  have hborder : nd.node.border = 0 :=
    hplain nd (List.mem_of_getElem? hnode) (by rw [hedge]; simp)
  have hdummy : nd.dummy = true := labeled_anchor_plain hn hl hnode hedge
  obtain ⟨out, hout, hedgeOut, hborderOut, hwOut, hhOut⟩ :=
    coordinateGraphX_plain_anchor_dims P hnode hborder
  obtain ⟨dout, hdout, hd_dout⟩ := X_coordinateGraphX_dummy_at hnode
  have houtEq : dout = out := Option.some.inj (hdout.symm.trans hout)
  subst dout
  have hkeysPrefix := (coordinateGraphX_anchor_prefix P exact labeled).1
  have hrankPrefix := (coordinateGraphX_anchor_prefix P exact labeled).2
  have hicoord := labelAnchorIndex_prefix halign hkeysPrefix hrankPrefix hi
  rw [hc] at hout hicoord hrankPrefix
  obtain ⟨_hedges, hprank, _hprolen, _, _, hpreserve⟩ := proxyWidths_rel hproxy
  have hne2 : ¬ (out.node.border = -2 ∨ out.node.border = 2) := by
    rw [hborderOut]
    omega
  obtain ⟨hpnode, _hxs⟩ := hpreserve index out hout hne2
  have hlookup : run.proper.nodes[index]? = some out := by
    rw [← hdrop]
    exact hpnode
  obtain ⟨_extraRanks, hcrank⟩ := hrankPrefix
  have hfinalrank : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]
    exact hprank
  have htail : rk run.proper.rank edge.tail = rk labeled.rank edge.tail := by
    rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left htailBound]
  have hhead : rk run.proper.rank edge.head = rk labeled.rank edge.head := by
    rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left hheadBound]
  have hanchor : labelAnchorIndex run.proper k
      (rk run.proper.rank edge.tail +
        Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2) =
        some index := by
    rw [htail, hhead, ← hdrop]
    change labelAnchorIndex q0 k _ = some index
    unfold labelAnchorIndex
    rw [proxyWidths_edge_keys hproxy, hprank]
    exact hicoord
  have hedgeP : out.edge = some k := hedgeOut.trans hedge
  have hborderP : out.node.border = 0 := hborderOut
  have hdummyP : out.dummy = true := hd_dout.trans hdummy
  refine ⟨index, out, hanchor, hlookup, hout, hedgeP, hdummyP, hborderP, ?_, ?_⟩
  · rw [← hw]
    exact hwOut
  · exact hhOut.trans hh

/-- Proper nodes transport to coordinate nodes preserving border, dummy flag
and height (copy of `proper_to_coord_node` with `componentRunX_spec`). -/
private theorem X_proper_to_coord_node {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {qv : ProperNode} (hqv : run.proper.nodes[v]? = some qv)
    (hv : v < run.proper.nodes.length) :
    ∃ pv, run.coordinateProper.nodes[v]? = some pv ∧
      pv.node.border = qv.node.border ∧ pv.dummy = qv.dummy ∧
      pv.node.h = qv.node.h := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hplen : v < run.coordinateProper.nodes.length := by
    have h1 := (proxyWidths_rel hproxy).2.2.1
    have h2 : run.proper.nodes = q0.nodes := by
      rw [← hdrop]
      exact OrderImpl.dropSynthetic_nodes _
    rw [h2] at hv
    omega
  obtain ⟨pv, hpv⟩ : ∃ pv, run.coordinateProper.nodes[v]? = some pv :=
    ⟨_, List.getElem?_eq_getElem hplen⟩
  obtain ⟨_, _, _, _, hP1, _⟩ := proxyWidths_rel hproxy
  obtain ⟨qv', hqv', hd', hb', hh'⟩ := hP1 v pv hpv
  have hq : run.proper.nodes[v]? = some qv' := by
    rw [← hdrop]
    simpa only [OrderImpl.dropSynthetic_nodes] using hqv'
  have hqvEq : qv' = qv := Option.some.inj (hq.symm.trans hqv)
  subst hqvEq
  exact ⟨pv, hpv, hb'.symm, hd'.symm, hh'.symm⟩

/-- `sizeProperPortsX` preserves the node count (copy of the private
`X_sized_length`). -/
private theorem X_fwd_sized_length (P : Params) (exact : List Nat) (p : Proper) :
    (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
  unfold sizeProperPortsX
  simp

/-- Exact bordered-graph node classification (copy of the private
`X_coordinateGraph0_lookup`). -/
private theorem X_fwd_coordinateGraph0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := X_fwd_sized_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by
        simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

/-- Exact coordinate-graph node classification (copy of the private
`X_coordinateGraph_lookup`). -/
private theorem X_fwd_coordinateGraph_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases X_fwd_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3

/-- Exact coordinate titles are unique per cluster path (copy of the private
`X_pc_title_unique`). -/
private theorem X_fwd_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper} (hK : NodeKeys cg labeled)
    (hS : CgShape cg) {a b : Nat} {na nb : ProperNode}
    (ha : (coordinateGraphX P exact labeled).nodes[a]? = some na)
    (hb : (coordinateGraphX P exact labeled).nodes[b]? = some nb)
    (h1 : na.node.border = 3) (h2 : nb.node.border = 3)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  have key : ∀ {v : Nat} {nd : ProperNode},
      (coordinateGraphX P exact labeled).nodes[v]? = some nd →
      nd.node.border = 3 →
      ∃ (i : Nat) (q : ProperNode × Nat),
        (titleNodes (sizeProperPortsX P exact labeled))[i]? = some q ∧
        v = labeled.nodes.length + i ∧ nd.node.clusterPath = q.1.node.clusterPath := by
    intro v nd h hb3
    rcases X_fwd_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
      ⟨i, q, hq, hv, hqd, _, h4⟩
    · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
      · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
      · rw [hb] at h1; omega
    · omega
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPortsX_key P exact labeled q.2
      rw [hs] at hk
      cases hpl : labeled.nodes[q.2]? with
      | none => simp [hpl] at hk
      | some mp =>
        simp only [hpl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hpl with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
        · exact ⟨i, q, hq, hv, h4 (by rw [hk1]; exact hmd)⟩
        · rw [hk2] at hbq
          rw [hb'] at hbq
          exact absurd hbq (by decide)
  obtain ⟨i, qi, hqi, hvi, hpi⟩ := key ha h1
  obtain ⟨j, qj, hqj, hvj, hpj⟩ := key hb h2
  obtain ⟨hsi, hbi⟩ := titleNodes_spec hqi
  obtain ⟨hsj, hbj⟩ := titleNodes_spec hqj
  have kI := sizeProperPortsX_key P exact labeled qi.2
  have kJ := sizeProperPortsX_key P exact labeled qj.2
  rw [hsi] at kI
  rw [hsj] at kJ
  cases hli : labeled.nodes[qi.2]? with
  | none => simp [hli] at kI
  | some mi =>
    cases hlj : labeled.nodes[qj.2]? with
    | none => simp [hlj] at kJ
    | some mj =>
      simp only [hli, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kI
      simp only [hlj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kJ
      have hidx : qi.2 = qj.2 :=
        labeled_topUnique hK hS hli hlj (by rw [← kI.2.1]; exact hbi)
          (by rw [← kJ.2.1]; exact hbj)
          (by rw [← kI.2.2, ← kJ.2.2, ← hpi, ← hpj]; exact hp)
      have hij : i = j :=
        nodup_map_inj_aux (·.2) (titleNodes_snd_nodup _) hqi hqj hidx
      rw [hvi, hvj, hij]

/-- Exact proxy frames are flat (copy of the private `X_pc_frame_flat`). -/
private theorem X_fwd_pc_frame_flat {P : Params} {exact : List Nat} {labeled : Proper}
    {v : Nat} {nd : ProperNode} (h : (coordinateGraphX P exact labeled).nodes[v]? = some nd)
    (hb : nd.node.border = -2 ∨ nd.node.border = 2) : nd.node.h = 0 := by
  rcases X_fwd_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, _, _, hf⟩ | ⟨_, h1⟩ |
    ⟨i, q, hq, _, _, h1, _⟩
  · exact hf hb
  · omega
  · omega

/-- Non-proxy exact coordinate nodes transfer to the proper run unchanged
(copy of the private `X_nonproxy_record`). -/
private theorem X_fwd_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- Exact ranked source (copy of the private `X_ranked_source`). -/
private theorem X_fwd_ranked_source {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      ∀ edge ∈ (Compound.rankingGraph cg).edges,
        edge.minLen ≤ rk rr.ranks edge.head - rk rr.ranks edge.tail := by
  unfold componentRunX at h
  obtain ⟨rr, hrr, h⟩ := bind_ok h
  obtain ⟨normalized, hn, h⟩ := bind_ok h
  obtain ⟨labeled, hl, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨lanes, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨shifted, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have heq := Except.ok.inj h
  subst run
  refine ⟨rr, normalized, labeled, hrr, hn, hl, rfl, ?_⟩
  apply rank_feasible (Compound.rankingGraph cg) rr.ranks
  simp only [RankImpl.rank, hrr]

/-- Slim exact prepared source: the coordinate construction and node keys
suffice for the ordered-intervals uniqueness argument (avoids the border
readiness machinery of the full prepared source). -/
private theorem X_fwd_prepared_keys {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ labeled : Proper,
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      NodeKeys cg labeled := by
  obtain ⟨_, _, labeled, _, hn, hl, hc, _⟩ := X_fwd_ranked_source h
  exact ⟨labeled, hc, addLabelNodes_keys _ _ _ (normalize_keys hn) hl⟩

/-- Exact ordered intervals for non-proxy nodes (copy of the private
`X_nonproxy_ordered_intervals`, with the public `exactGraph_shape` in place
of the private shape transport). -/
private theorem X_fwd_nonproxy_ordered_intervals {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {i j a b : Nat} {first second : ProperNode}
    (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hfirst : run.coordinateProper.nodes[a]? = some first)
    (hsecond : run.coordinateProper.nodes[b]? = some second)
    (hfirstBorder : ¬(first.node.border = -2 ∨ first.node.border = 2))
    (hsecondBorder : ¬(second.node.border = -2 ∨ second.node.border = 2)) :
    RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤
      RouteImpl.leftOf run.proper run.xs b := by
  obtain ⟨labeled, hcoordinate, hkeys⟩ := X_fwd_prepared_keys hrun
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate
  have huniq : ∀ (u v : Nat) (left right : ProperNode),
      run.coordinateProper.nodes[u]? = some left →
      run.coordinateProper.nodes[v]? = some right →
      left.node.border = 3 → right.node.border = 3 →
      left.node.clusterPath = right.node.clusterPath → u = v := by
    intro u v left right hleft hright hleftBorder hrightBorder hpath
    apply X_fwd_pc_title_unique hkeys hshape
      (by rw [hcoordinate]; exact hleft)
      (by rw [hcoordinate]; exact hright) hleftBorder hrightBorder hpath
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRunX_spec hrun
  have hsep := cluster_all_pairs_separated hcross huniq layer hlayer i j a b
    first second hij ha hb hfirst hsecond
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hng, hcp, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨hfinalFirst, hxa⟩ := X_fwd_nonproxy_record hrun hfirst hfirstBorder
  obtain ⟨hfinalSecond, hxb⟩ := X_fwd_nonproxy_record hrun hsecond hsecondBorder
  have hwa : RouteImpl.nodeW run.proper a =
      RouteImpl.nodeW run.coordinateProper a := by
    simp only [RouteImpl.nodeW, hfinalFirst, hfirst]
  have hwb : RouteImpl.nodeW run.proper b =
      RouteImpl.nodeW run.coordinateProper b := by
    simp only [RouteImpl.nodeW, hfinalSecond, hsecond]
  have hga : RouteImpl.nodeW run.coordinateProper a ≤
      CoordsImpl.nodeW run.coordinateProper a := CoordsImpl.nodeW_ge_width _ _
  have hgb : RouteImpl.nodeW run.coordinateProper b ≤
      CoordsImpl.nodeW run.coordinateProper b := CoordsImpl.nodeW_ge_width _ _
  have e : ∀ width : Int, Int.fdiv width 2 = width / 2 :=
    fun width => Int.fdiv_eq_ediv_of_nonneg width (by decide)
  unfold CoordsImpl.coordSep at hsep
  simp only [e] at hsep
  simp only [RouteImpl.leftOf, RouteImpl.xAt, hxa, hxb, hwa, hwb, e]
  omega


/-- Exact pre-reserve coordinates (copy of the private `X_run_pre`): unfold
one `componentRunX` to expose the rank-axis output, the proxy `ys`, and the
`reserveExactRanks` equation that produces the final `run.ys`/`run.top`. -/
private theorem X_fwd_run_pre {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (y_pre top_pre ys_pre : List Int),
      rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧
      proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧
      reserveExactRanks cg exact labels run.coordinateProper run.layers ys_pre top_pre =
        .ok (run.ys, run.top) ∧
      run.coordinateYs = y_pre := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, hp0, h⟩ := bind_ok h
  obtain ⟨q, hq, h⟩ := bind_ok h
  obtain ⟨ord, hord, h⟩ := bind_ok h
  obtain ⟨xs, hxs, h⟩ := bind_ok h
  obtain ⟨routed, hprojection, h⟩ := bind_ok h
  obtain ⟨lanes, hr, h⟩ := bind_ok h
  obtain ⟨yt, hy, h⟩ := bind_ok h
  obtain ⟨⟨ysV, topV⟩, hres, h⟩ := bind_ok h
  obtain ⟨routes, hroutes, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst he
  cases yt with
  | mk y top =>
    exact ⟨y, top, _, hy, rfl, hres, rfl⟩

/-- Reserve shifts each rank uniformly: the `ys`-minus-`top` gap at a node is
unchanged by `reserveExactRanks`. The per-rank shift cancels, so the proxy
`ys` edge positions (band top for `border = -2`, band bottom for
`border = 2`) survive reservation. -/
private theorem X_fwd_shift_diff {cg : Graph} {exact : List Nat}
    {labels : List MeasuredLabel} {p : Proper} {layers : List (List Nat)}
    {ys_pre top_pre ys top : List Int}
    (hreserve : reserveExactRanks cg exact labels p layers ys_pre top_pre =
      .ok (ys, top))
    {v r : Nat} (hr : r < top_pre.length) (hv : v < ys_pre.length)
    (hrank : (p.rank.getD v 0).toNat = r) :
    ys.getD v 0 - top.getD r 0 = ys_pre.getD v 0 - top_pre.getD r 0 := by
  unfold reserveExactRanks at hreserve
  obtain ⟨topNew, htopM, h1⟩ := bind_ok hreserve
  obtain ⟨ysNew, hysM, h2⟩ := bind_ok h1
  have hpair := Except.ok.inj h2
  have htopNew_eq : topNew = top := congrArg Prod.snd hpair
  have hysNew_eq : ysNew = ys := congrArg Prod.fst hpair
  have hrZ : r < (top_pre.zipIdx).length := by
    rw [List.length_zipIdx]
    exact hr
  have hvZ : v < (ys_pre.zipIdx).length := by
    rw [List.length_zipIdx]
    exact hv
  have hzinT : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
    have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
    simp [List.getElem?_zipIdx, h1]
  have hzinY : (ys_pre.zipIdx)[v]? = some (ys_pre[v], v) := by
    have h1 : ys_pre[v]? = some ys_pre[v] := List.getElem?_eq_getElem hv
    simp [List.getElem?_zipIdx, h1]
  obtain ⟨_, hidxT⟩ := mapM_getElem? _ _ _ htopM
  obtain ⟨_, hidxY⟩ := mapM_getElem? _ _ _ hysM
  obtain ⟨bT, hbT, hbrT⟩ := hidxT r _ hzinT
  obtain ⟨bY, hbY, hbrY⟩ := hidxY v _ hzinY
  dsimp only at hbT hbY
  have eT := Measure.checkedI32_ok hbT
  have eY := Measure.checkedI32_ok hbY
  rw [hrank] at eY
  have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
  have h2 : ys_pre[v]? = some ys_pre[v] := List.getElem?_eq_getElem hv
  have e3 : top.getD r 0 = bT := by
    rw [← htopNew_eq, List.getD_eq_getElem?_getD, hbrT]
    rfl
  have e4 : ys.getD v 0 = bY := by
    rw [← hysNew_eq, List.getD_eq_getElem?_getD, hbrY]
    rfl
  rw [e3, e4, eT, eY]
  have e5 : top_pre.getD r 0 = top_pre[r] := by
    rw [List.getD_eq_getElem?_getD, h1]
    rfl
  have e6 : ys_pre.getD v 0 = ys_pre[v] := by
    rw [List.getD_eq_getElem?_getD, h2]
    rfl
  rw [e5, e6]
  omega

/-- Forward separation holds for every executed exact flat layout: the stack
rect of a forward edge label is axis-separated from every real node box in
its run. Replay of `runLocalForwardSeparation` over `componentRunX_spec`:
envelope inversion and label coordinates are shared; rank bands come from
`X_ReserveBands_holds` (reserved `top`/`ys`); same-rank `x` separation replays
the ordered-intervals argument over the exact coordinate graph; same-band
frame edges use the proxy `ys` position transported through the reserve
shift. The scope premises are unused, as in the plain proof. -/
theorem x_runLocalForwardSeparation_holds (exactIds : List String) :
    X_RunLocalForwardSeparation exactIds := by
  unfold X_RunLocalForwardSeparation
  intro inp o res execution comp candidate run orderOptions cg k e env v r
    hcomp hcg hrun hk hne hrev henv hv hreal _hscope₀ _hscope₁ hr
  have hslot := componentRunX_slot_nonneg hrun
  have hlab := execution.measured_nonneg
  have hrun' : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run := by
    rw [← hcg]
    exact hrun
  obtain ⟨hinBand, hdisjBands⟩ := X_ReserveBands_holds exactIds hrun
  obtain ⟨first, q, hfirst, hqfind, henv_eq⟩ := forward_envelope_eq hne hrev henv
  have hpred := List.find?_some hqfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨aindex, and, hanchor, hnodeA, houtA, _hedgeA, hdummyA, hborderA, hwA, hhA⟩ :=
    X_forward_anchor_full hrun hk hne hfirst
  rw [labelAnchorIndex_eq] at hanchor
  have hu : q.2 = aindex := by
    rw [hqfind] at hanchor
    exact Option.some.inj hanchor
  have hmem : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hqfind)
  rw [hu] at hmem
  have hq1 : q.1 = and := Option.some.inj (hmem.symm.trans hnodeA)
  rw [hq1, hu] at hpred
  have hrk_u : rk run.proper.rank aindex =
      (rk run.proper.rank e.tail +
        Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) :=
    hpred.2
  have hu_len : aindex < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnodeA).1
  have hWu : RouteImpl.nodeW run.proper aindex = and.node.w := by
    unfold RouteImpl.nodeW
    rw [hnodeA]
  have hHu : RouteImpl.nodeH run.proper aindex = and.node.h := by
    unfold RouteImpl.nodeH
    rw [hnodeA]
  have hfm : first ∈ routeLabels execution.measured e.decl := by
    cases hrfl : routeLabels execution.measured e.decl with
    | nil => simp [hrfl] at hfirst
    | cons hd tl =>
      have heq : hd = first := by
        have h2 := hfirst
        rw [hrfl] at h2
        simpa using h2
      subst heq
      exact List.mem_cons_self
  have hg0 : 0 ≤ first.gutter := (hlab first ((List.mem_filter.mp hfm).1)).2.2
  have hsizes : ∀ s ∈ (routeLabels execution.measured e.decl).map
      fun l => (l.width, l.height),
      0 ≤ s.1 ∧ 0 ≤ s.2 := by
    intro s hs
    obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hs
    exact ⟨(hlab l ((List.mem_filter.mp hlm).1)).1, (hlab l ((List.mem_filter.mp hlm).1)).2.1⟩
  have hsizes2 : ∀ s ∈ (routeLabels execution.measured e.decl).map
      fun l => (l.width, l.height),
      0 ≤ s.2 := fun s hs => (hsizes s hs).2
  have hle : Labels.stackHeight cg.slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) ≤
      RouteImpl.nodeH run.proper aindex := by
    rw [hHu, hhA, ← stackSize_height_eq]
    exact Int.le_refl _
  have hrx : r.x = env.x := (stackRects_entry hr).1
  have hrw : r.w ≤ Labels.stackWidth
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) :=
    stackRect_width_le hr
  have henvx : env.x = RouteImpl.xAt run.xs aindex -
      Int.fdiv (RouteImpl.nodeW run.proper aindex) 2 + first.gutter := by
    rw [henv_eq, hu]
    exact textRectAt_left _ _ _ _ _
  have henvy : env.y = RouteImpl.yAt run.ys aindex := by
    rw [henv_eq, hu]
    exact textRectAt_y _ _ _ _ _
  have _henvw : env.w = RouteImpl.nodeW run.proper aindex - first.gutter := by
    rw [henv_eq, hu]
    rfl
  have henvh : env.h = RouteImpl.nodeH run.proper aindex := by
    rw [henv_eq, hu]
    rfl
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop', hrLanes, _, _⟩ :=
    componentRunX_spec hrun
  have hlay : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hrLanes).1
  have hcov := (RouteImpl.layersOk_spec hlay).2.2.2.1
  obtain ⟨lu, hlu_mem, hu_mem, hu_nn⟩ := hcov aindex hu_len
  obtain ⟨qv, hqv⟩ : ∃ qv, run.proper.nodes[v]? = some qv :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  obtain ⟨lv, hlv_mem, hv_mem, hv_nn⟩ := hcov v hv
  have hprank : q0.rank = run.coordinateProper.rank := (proxyWidths_rel hproxy).2.1
  have hfinalrank : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop']
    exact hprank
  have hplen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    have h1 := (proxyWidths_rel hproxy).2.2.1
    have h2 : run.proper.nodes = q0.nodes := by
      rw [← hdrop']
      exact OrderImpl.dropSynthetic_nodes _
    rw [h2]
    exact h1
  have hrkU : rk run.proper.rank aindex = ((rk run.proper.rank aindex).toNat : Int) :=
    (Int.toNat_of_nonneg hu_nn).symm
  have hrkV : rk run.proper.rank v = ((rk run.proper.rank v).toNat : Int) :=
    (Int.toNat_of_nonneg hv_nn).symm
  have hrkUC : rk run.coordinateProper.rank aindex =
      ((rk run.proper.rank aindex).toNat : Int) := by
    rw [← hfinalrank]
    exact hrkU
  have hrkVC : rk run.coordinateProper.rank v =
      ((rk run.proper.rank v).toNat : Int) := by
    rw [← hfinalrank]
    exact hrkV
  have hu_lenC : aindex < run.coordinateProper.nodes.length := by omega
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hbandU := hinBand _ _ _ hlu_mem hu_mem hu_lenC hrkUC
  have hbandV := hinBand _ _ _ hlv_mem hv_mem hvC hrkVC
  have htop : ∀ r r' (lr lr' : List Nat), r < r' → run.layers[r]? = some lr →
      run.layers[r']? = some lr' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper lr ≤
        run.top.getD r' 0 :=
    fun r r' lr lr' hrr h1 h2 => hdisjBands r r' lr lr' hrr h1 h2
  have hyAt_a : RouteImpl.yAt run.ys aindex = run.ys.getD aindex 0 := rfl
  have hyAt_v : RouteImpl.yAt run.ys v = run.ys.getD v 0 := rfl
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ :=
    X_fwd_run_pre hrun
  obtain ⟨pv, hpv, hpv_border, _hpv_dummy, _hpv_h⟩ :=
    X_proper_to_coord_node hrun hqv hv
  have hHaBridge : RouteImpl.nodeH run.proper aindex =
      RouteImpl.nodeH run.coordinateProper aindex := by
    have e1 : RouteImpl.nodeH run.proper aindex = and.node.h := by
      simp [RouteImpl.nodeH, hnodeA]
    have e2 : RouteImpl.nodeH run.coordinateProper aindex = and.node.h := by
      simp [RouteImpl.nodeH, houtA]
    omega
  have hHvBridge : RouteImpl.nodeH run.proper v =
      RouteImpl.nodeH run.coordinateProper v := by
    have e1 : RouteImpl.nodeH run.proper v = qv.node.h := by
      simp [RouteImpl.nodeH, hqv]
    have e2 : RouteImpl.nodeH run.coordinateProper v = pv.node.h := by
      simp [RouteImpl.nodeH, hpv]
    have e3 : pv.node.h = qv.node.h := _hpv_h
    omega
  have hbandU' : run.top.getD (rk run.proper.rank aindex).toNat 0 ≤
      RouteImpl.yAt run.ys aindex ∧
      RouteImpl.yAt run.ys aindex + RouteImpl.nodeH run.coordinateProper aindex ≤
      run.top.getD (rk run.proper.rank aindex).toNat 0 +
        CoordsImpl.layerHeight run.coordinateProper lu := hbandU
  have hbandV' : run.top.getD (rk run.proper.rank v).toNat 0 ≤
      RouteImpl.yAt run.ys v ∧
      RouteImpl.yAt run.ys v + RouteImpl.nodeH run.coordinateProper v ≤
      run.top.getD (rk run.proper.rank v).toNat 0 +
        CoordsImpl.layerHeight run.coordinateProper lv := hbandV
  by_cases heq : (rk run.proper.rank aindex).toNat = (rk run.proper.rank v).toNat
  · -- Same rank: horizontal separation by the layer order.
    have hlv_eq : lv = lu := by
      have h2 : run.layers[(rk run.proper.rank aindex).toNat]? = some lv := by
        rw [heq]
        exact hlv_mem
      exact Option.some.inj (h2.symm.trans hlu_mem)
    have hlayer_mem : lu ∈ run.layers := List.mem_of_getElem? hlu_mem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu_mem
    have hvmem : v ∈ lu := hlv_eq ▸ hv_mem
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvmem
    have hne_uv : v ≠ aindex := by
      intro heq2
      subst heq2
      have h1 := hreal and hnodeA
      rw [hdummyA] at h1
      cases h1
    have hij : i ≠ j := by
      intro heq2
      apply hne_uv
      have hi' : lu[j]? = some aindex := heq2 ▸ hi
      exact (Option.some.inj (hi'.symm.trans hj)).symm
    obtain ⟨pu, hpu, hpu_border, _hpu_dummy, _hpu_h⟩ :=
      X_proper_to_coord_node hrun hnodeA hu_len
    have hpu0 : pu.node.border = 0 := by
      rw [hpu_border]
      exact hborderA
    by_cases hfr : qv.node.border = -2 ∨ qv.node.border = 2
    · -- Foreign frame on the same band: band-edge separation.
      have hpv2 : pv.node.border = qv.node.border := hpv_border
      have hylen : y_pre.length = run.coordinateProper.nodes.length :=
        (CoordsImpl.rankCoordsWith_length hry).1
      have htopLen : top_pre.length = run.layers.length :=
        (CoordsImpl.rankCoordsWith_length hry).2
      have hysLen : ys_pre.length = run.coordinateProper.nodes.length := by
        rw [← hyspre]
        unfold proxyYs
        rw [List.length_map, List.length_zipIdx]
        exact hylen
      have hlen_y : v < y_pre.length := by omega
      have hrk_eq : (rk run.coordinateProper.rank v).toNat =
          (rk run.proper.rank aindex).toNat := by
        rw [← hfinalrank, ← heq]
      have hrTop : (rk run.proper.rank aindex).toNat < top_pre.length := by
        have hlt := (List.getElem?_eq_some_iff.mp hlu_mem).1
        omega
      have hvYs : v < ys_pre.length := by omega
      have hrankV : (run.coordinateProper.rank.getD v 0).toNat =
          (rk run.proper.rank aindex).toNat := hrk_eq
      have hshift := X_fwd_shift_diff hreserve hrTop hvYs hrankV
      have hpg := proxyYs_getD run.coordinateProper run.layers top_pre y_pre hpv hlen_y
      rw [hyspre] at hpg
      rcases hfr with hb2 | hb2
      · have hbeq : (pv.node.border == -2) = true := by simp [hpv2, hb2]
        have hpre : ys_pre.getD v 0 =
            top_pre.getD (rk run.proper.rank aindex).toNat 0 := by
          rw [hpg, hbeq]
          simp only [↓reduceIte]
          rw [hrk_eq]
        have hyv : RouteImpl.yAt run.ys v =
            run.top.getD (rk run.proper.rank aindex).toNat 0 := by
          simp only [RouteImpl.yAt]
          omega
        have hframe : RouteImpl.IsFrame run.proper v := by
          rw [isFrame_iff hqv]
          exact ⟨hreal qv hqv, Or.inl hb2⟩
        have hfh : RouteImpl.nodeH run.proper v = 0 := by
          obtain ⟨labeled, hcoordinate, _⟩ := X_fwd_prepared_keys hrun
          have hpvC : (coordinateGraphX execution.params
              (exactDecls exactIds inp) labeled).nodes[v]? = some pv := by
            rw [hcoordinate]
            exact hpv
          have hflat : pv.node.h = 0 :=
            X_fwd_pc_frame_flat hpvC (by rw [hpv2]; exact Or.inl hb2)
          have e1 : RouteImpl.nodeH run.proper v = qv.node.h := by
            simp [RouteImpl.nodeH, hqv]
          have e2 : pv.node.h = qv.node.h := _hpv_h
          omega
        apply Or.inr; apply Or.inr; apply Or.inr
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
            RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
        have hboxh : (RouteImpl.boxRect run.proper run.xs run.ys v).h =
            RouteImpl.nodeH run.proper v := boxRect_h _ _ _ _
        have hlo : env.y ≤ r.y := stackRect_lower_le hslot hsizes2 hr
        rw [henvy] at hlo
        omega
      · have hbeq : (pv.node.border == -2) = false := by simp [hpv2, hb2]
        have hbeq2 : (pv.node.border == 2) = true := by simp [hpv2, hb2]
        have hLH : CoordsImpl.layerHeight run.coordinateProper lu =
            RouteImpl.layerHeight run.proper lu := by
          rw [layerHeight_eq_route]
          have hHH : (fun w => RouteImpl.nodeH run.proper w) =
              (fun w => RouteImpl.nodeH run.coordinateProper w) := by
            funext w
            have h1 := nodeH_proxy hproxy w
            have h2 : run.proper.nodes = q0.nodes := by
              rw [← hdrop']
              exact OrderImpl.dropSynthetic_nodes _
            have h3 : RouteImpl.nodeH run.proper w = RouteImpl.nodeH q0 w := by
              unfold RouteImpl.nodeH
              rw [h2]
            rw [h3]
            exact h1
          simp only [RouteImpl.layerHeight, hHH]
        have hget : run.layers.getD (rk run.proper.rank aindex).toNat [] = lu := by
          rw [List.getD_eq_getElem?_getD, hlu_mem]
          rfl
        have hpre : ys_pre.getD v 0 =
            top_pre.getD (rk run.proper.rank aindex).toNat 0 +
            CoordsImpl.layerHeight run.coordinateProper lu := by
          rw [hpg, hbeq, hbeq2]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hrk_eq, hget]
        have hyv : RouteImpl.yAt run.ys v =
            run.top.getD (rk run.proper.rank aindex).toNat 0 +
            RouteImpl.layerHeight run.proper lu := by
          simp only [RouteImpl.yAt]
          omega
        apply Or.inr; apply Or.inr; apply Or.inl
        have hup : r.y + r.h ≤ env.y +
            Labels.stackHeight cg.slot
              ((routeLabels execution.measured e.decl).map
                fun l => (l.width, l.height)) :=
          stackRect_upper_le hslot hsizes2 hr
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
            RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
        rw [hbox, hyv]
        omega
    · -- Both non-frames: layer order.
      have hnb1 : ¬ (pu.node.border = -2 ∨ pu.node.border = 2) := by
        rw [hpu0]
        omega
      have hnb2 : ¬ (pv.node.border = -2 ∨ pv.node.border = 2) := by
        rw [hpv_border]
        exact hfr
      have e1 : Int.fdiv (RouteImpl.nodeW run.proper aindex) 2 =
          RouteImpl.nodeW run.proper aindex / 2 := fdiv2_ediv _
      have e2 : Int.fdiv (RouteImpl.nodeW run.proper v) 2 =
          RouteImpl.nodeW run.proper v / 2 := fdiv2_ediv _
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · have hord := X_fwd_nonproxy_ordered_intervals execution hcomp hrun'
          hlayer_mem hlt hi hj hpu hpv hnb1 hnb2
        apply Or.inl
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).x =
            RouteImpl.xAt run.xs v - Int.fdiv (RouteImpl.nodeW run.proper v) 2 :=
          boxRect_left _ _ _ _
        rw [hrx, henvx, hbox, e1, e2]
        unfold RouteImpl.leftOf at hord
        have hwle : Labels.stackWidth
            ((routeLabels execution.measured e.decl).map
              fun l => (l.width, l.height)) +
            first.gutter ≤ RouteImpl.nodeW run.proper aindex := by
          rw [hWu, ← stackSize_width_eq]
          exact hwA
        omega
      · have hord := X_fwd_nonproxy_ordered_intervals execution hcomp hrun'
          hlayer_mem hgt hj hi hpv hpu hnb2 hnb1
        apply Or.inr; apply Or.inl
        have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).x =
            RouteImpl.xAt run.xs v - Int.fdiv (RouteImpl.nodeW run.proper v) 2 :=
          boxRect_left _ _ _ _
        have hboxw : (RouteImpl.boxRect run.proper run.xs run.ys v).w =
            RouteImpl.nodeW run.proper v :=
          boxRect_w _ _ _ _
        rw [hrx, henvx, hbox, hboxw, e1, e2]
        unfold RouteImpl.leftOf at hord
        omega
  · -- Different ranks: band separation.
    have hne2 : (rk run.proper.rank aindex).toNat ≠ (rk run.proper.rank v).toNat :=
      heq
    rcases Nat.lt_or_gt_of_ne hne2 with hlt | hgt
    · have hband := rank_band_above hlu_mem hlv_mem hlt htop hbandU' hbandV'.1
      apply Or.inr; apply Or.inr; apply Or.inl
      have hup : r.y + r.h ≤ env.y +
          Labels.stackHeight cg.slot
            ((routeLabels execution.measured e.decl).map
              fun l => (l.width, l.height)) :=
        stackRect_upper_le hslot hsizes2 hr
      have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
          RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
      rw [hbox]
      omega
    · have hband := rank_band_below hlu_mem hlv_mem hgt htop hbandU'.1 hbandV'
      apply Or.inr; apply Or.inr; apply Or.inr
      have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
          RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
      have hboxh : (RouteImpl.boxRect run.proper run.xs run.ys v).h =
          RouteImpl.nodeH run.proper v := boxRect_h _ _ _ _
      have hlo : env.y ≤ r.y := stackRect_lower_le hslot hsizes2 hr
      rw [henvy] at hlo
      rw [hbox, hboxh]
      omega

end PipelineImpl
end Layered
end Elegant

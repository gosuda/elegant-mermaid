import Elegant.Layered.ExactRouteForwardClearProof
import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.RouteLabelForeignClearProof
import Elegant.Layered.ExactFlatC7Forward
import Elegant.Layered.ExactFlatC7Reversed
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactForeignNonGroupSpansProof
import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactFlatC2

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact forward clearance facts (`XFR_*X_holds`)

Proves four premises of `XF_routeForwardClearX_holds`
(`ExactRouteForwardClearProof.lean:309`): `XFR_RouteLabelRealClearX`,
`XFR_RouteLabelForeignClearX`, `XFR_RouteLabelLeftoverPairX`,
`XFR_SeamsImplyForeignX`.

Plain path replayed for each (as closed by `routeRunClear_closed`,
`RouteRunClearClosed.lean:76`):

* real: `routeLabelRealClear_of_run` (`RouteRunClearCases.lean:667`) over
  `componentRunX`, with the loop branch through the extended footprint miss
  `X_LoopEnvelopeMiss` (`ExactLoopEnvelopeSeparationProof.lean:50`), the
  replacement for the plain `RunLocalLoopFootprint` separation half (the
  plain reservation `n * band <= frame.h` is false on fixed-size nodes).
* foreign: `routeLabelForeignClear_of_run`
  (`RouteLabelForeignClearProof.lean:51`) over `componentRunX`, with the
  dummy cell through the exact span seams below.
* leftover: `routeLabelLeftoverPair_of_run`
  (`RouteLabelLeftoverPairProof.lean:446`) over `componentRunX`, composing
  the sibling forward facts proved in this file.
* seams-imply: `foreignFramesDisjoint_of_run`
  (`RouteRunClearCases.lean:752`) over `componentRunX`, from the exact span
  seams below.

Probe: `proofs/wip/Probe/ExactFwdClearFactsTProbe.lean` checks the real
conclusion on a wider-than-slot fixed node (`w = 500` next to the label
dummy): `real=true` over 65 scope-outside pairs, `layoutX ok`.
-/

/-- Copy of the private `findIdxHitElem` (`RouteRunClearCases.lean`): a
`findIdx?` hit carries its element and the satisfied predicate. -/
private theorem xfrf_findIdxHitElem {α : Type} {l : List α} (p : α → Bool)
    (j : Nat) (h : l.findIdx? p = some j) :
    ∃ x, l[j]? = some x ∧ p x = true := by
  induction l generalizing j with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      cases j with
      | zero => exact ⟨y, rfl, hp⟩
      | succ j' => exact absurd h (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases j with
      | zero => exact absurd h (by simp)
      | succ j' =>
        cases hv : ys.findIdx? p with
        | none => rw [hv] at h; simp at h
        | some k =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          have hjk : j' = k := by omega
          obtain ⟨x, hx, hpx⟩ := ih k hv
          exact ⟨x, by simp only [hjk]; simpa using hx, hpx⟩

/-- Executed exact `RouteLabelRealClear`: a placed label misses the box of
every real proper node outside the edge's endpoint cluster paths. Replay of
`routeLabelRealClear_of_run` (`RouteRunClearCases.lean:667`) over
`componentRunX`: edge identity through `exactGraph_decls_nodup`, slot and
label nonnegativity through the exact facts, and the three edge-form
separations through `x_runLocalForwardSeparation_holds`,
`x_runLocalReversedSeparation_holds`, and
`X_runLocalLoopSeparation_of_envelopeMiss`. The loop branch consumes the
replacement residual `X_LoopEnvelopeMiss` (plain original: the separation
half of `RunLocalLoopFootprint`, as assumed by the plain proof through
`hfoot`); the scope premises are unused by the forward and reversed proofs,
as in the plain proof. -/
theorem XFR_routeLabelRealClearX_holds (exactIds : List String)
    (hloopMiss : X_LoopEnvelopeMiss exactIds) :
    XFR_RouteLabelRealClearX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl v pn hlook hI hsc1 hsc2
  have hnd := measureLabels_index_nodup execution.measured_eq
  obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv,
    hfindstk, hrfl⟩ := placedLabels_pair_inv hnd hmem
  have hml : ml = l₀ :=
    measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)
  have hdecl' : e'.decl = ml.edge := by
    obtain ⟨x, hx, hpx⟩ := xfrf_findIdxHitElem _ _ hfind
    have hee : e' = x := Option.some.inj (he'.symm.trans hx)
    have hpx2 : (x.decl == ml.edge) = true := hpx
    rw [← hee] at hpx2
    exact beq_iff_eq.mp hpx2
  subst hml
  have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
  have hdecls :
      ((componentCandidate execution.graph comp candidate).edges.map
        Edge.decl).Nodup := by
    have hndE := exactGraph_decls_nodup execution.graph0_eq execution.graph_eq
    exact componentCandidate_decls_nodup _ _ _ hndE
  have heq : edge = edge' := by
    have hmap :
        ((componentCandidate execution.graph comp candidate).edges.map
          Edge.decl)[edge]? =
          ((componentCandidate execution.graph comp candidate).edges.map
            Edge.decl)[edge']? := by
      simp only [List.getElem?_map, hedge, he', Option.map_some]
      exact congrArg some hdd
    have hlen : edge <
        ((componentCandidate execution.graph comp candidate).edges.map
          Edge.decl).length := by
      simpa only [List.length_map] using
        (List.getElem?_eq_some_iff.mp hedge).1
    exact (hdecls.getElem?_inj hlen).mp hmap
  subst heq
  have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
  subst hEE
  have hv : v < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hlook).1
  have hmemstk : rect ∈ Labels.stackRects env.x env.y
      (componentCandidate execution.graph comp candidate).slot
      ((routeLabels execution.measured e.decl).map fun l =>
        (l.width, l.height)) := by
    have hmstk := List.mem_of_find?_eq_some hfindstk
    have hzip := (List.of_mem_zip hmstk).2
    rw [← hrfl] at hzip
    exact hzip
  have hslot := componentRunX_slot_nonneg hrun
  have hlab := execution.measured_nonneg
  by_cases hloop : e.tail = e.head
  · have hsep := (X_runLocalLoopSeparation_of_envelopeMiss exactIds
      hloopMiss) inp o res execution comp candidate run orderOptions
      (componentCandidate execution.graph comp candidate) edge e env v
      hcomp rfl hrun he' hloop henv hv hI hsc1 hsc2
    have hclear := loop_branch_clear he' hloop henv hslot hlab hmemstk hsep
    unfold Disjoint
    rw [Rect.meetsInterior_comm]
    exact hclear
  · by_cases hrev : e.reversed = true
    · have hle := x_runLocalReversedSeparation_holds exactIds
        inp o res execution comp candidate run orderOptions
        (componentCandidate execution.graph comp candidate) edge e env v
        rect hcomp rfl hrun he' hloop hrev henv hv hI hsc1 hsc2 hmemstk
      unfold Disjoint Rect.meetsInterior
      omega
    · have hrev' : e.reversed = false := by
        cases hr : e.reversed with
        | true => exact absurd hr hrev
        | false => rfl
      have hsep := x_runLocalForwardSeparation_holds exactIds
        inp o res execution comp candidate run orderOptions
        (componentCandidate execution.graph comp candidate) edge e env v
        rect hcomp rfl hrun he' hloop hrev' henv hv hI hsc1 hsc2 hmemstk
      have hdis := RectAxisSeparated_of_not_meetsInterior hsep
      unfold Disjoint
      rw [Rect.meetsInterior_comm]
      exact hdis

/-- Dummy flags survive the exact coordinate-graph construction at a fixed
index (copy of `X_coordinateGraphX_dummy_at`, `ExactFlatC7Forward.lean:31`,
with the `sizeProperPortsX` first step). -/
private theorem xfrf_coord_dummy_at {P : Params} {exact : List Nat} {p : Proper}
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
exact anchor the forward envelope uses (copy of `X_forward_anchor_full`,
`ExactFlatC7Forward.lean:84`). -/
private theorem xfrf_forward_anchor_core {P : Params} {exact : List Nat} {cg : Graph}
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
      nd.edge = some k ∧ nd.dummy = true ∧ nd.node.border = 0 := by
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
  obtain ⟨dout, hdout, hd_dout⟩ := xfrf_coord_dummy_at hnode
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
  exact ⟨index, out, hanchor, hlookup, hout, hedgeP, hdummyP, hborderP⟩

/-- Exact bordered-graph node classification (copy of `Xb_coord0_lookup`,
`ExactFlatC5Bottom.lean:225`). -/
private theorem xfrf_coord0_lookup (P : Params) (exact : List Nat)
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
  have hlen := sizeProperPortsX_length P exact p
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
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
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

/-- Exact coordinate-graph node classification (copy of `Xb_coord_lookup`,
`ExactFlatC5Bottom.lean:290`). -/
private theorem xfrf_coord_lookup (P : Params) (exact : List Nat)
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
  rcases xfrf_coord0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
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

/-- Exact dummy border collapse: a dummy node of `coordinateGraphX` has
border 0 (copy of `Xb_pc_plain`, `ExactFlatC5Bottom.lean:646`). -/
private theorem xfrf_pc_plain {cg : Graph} {P : Params} {exact : List Nat} {labeled : Proper}
    (hK : NodeKeys cg labeled)
    {v : Nat} {nd : ProperNode} (h : (coordinateGraphX P exact labeled).nodes[v]? = some nd)
    (hd : nd.dummy = true) : nd.node.border = 0 := by
  rcases xfrf_coord_lookup P exact labeled h with ⟨m, hm, h1, h2, _, _⟩ | ⟨h1, _⟩ |
    ⟨i, q, hq, _, h1, h2, _⟩
  · rcases hK v m hm with ⟨n, _, hmd, _, _⟩ | ⟨_, hb, _⟩
    · rw [h1] at hd; rw [hmd] at hd; exact absurd hd (by decide)
    · rw [h2, hb]
  · rw [h1] at hd; exact absurd hd (by decide)
  · obtain ⟨hs, hb⟩ := titleNodes_spec hq
    have hk := sizeProperPortsX_key P exact labeled q.2
    rw [hs] at hk
    cases hp : labeled.nodes[q.2]? with
    | none => simp [hp] at hk
    | some mp =>
      simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨hk1, hk2, _⟩ := hk
      rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
      · rw [h1, hk1, hmd] at hd; exact absurd hd (by decide)
      · rw [hk2] at hb
        rw [hb'] at hb
        exact absurd hb (by decide)

/-- An executed exact proper dummy has border 0 with the same record in the
coordinate graph (copy of `Xb_proper_to_coord_dummy`,
`ExactFlatC5Bottom.lean:672`, additionally exporting the border-0 fact). -/
private theorem xfrf_proper_to_coord_dummy {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {pn : ProperNode}
    (hp : run.proper.nodes[i]? = some pn) (hd : pn.dummy = true) :
    ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = true ∧
      pn.node.border = 0 ∧ cn.node.border = pn.node.border ∧
      cn.node.h = pn.node.h ∧
      cn.node.clusterPath = pn.node.clusterPath := by
  obtain ⟨_, _, labeled, q0, hn, hl, hc, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq0i : q0.nodes[i]? = some pn := by rw [← hnodes]; exact hp
  have hlen : q0.nodes.length = run.coordinateProper.nodes.length :=
    (proxyWidths_rel hproxy).2.2.1
  have hiC : i < run.coordinateProper.nodes.length := by
    have hi0 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0i).1
    omega
  obtain ⟨cn, hcn⟩ : ∃ cn, run.coordinateProper.nodes[i]? = some cn :=
    ⟨_, List.getElem?_eq_getElem hiC⟩
  obtain ⟨nd', hnd', hddum, _, hhh⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 i cn hcn
  have hndEq : nd' = pn := Option.some.inj (hnd'.symm.trans hq0i)
  have hcnDum : cn.dummy = true := by rw [← hddum, hndEq]; exact hd
  have hK : NodeKeys cg labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hcnL : (coordinateGraphX P exact labeled).nodes[i]? = some cn := by
    rw [hc]; exact hcn
  have hbord0 : cn.node.border = 0 := xfrf_pc_plain hK hcnL hcnDum
  have hnp : ¬ (cn.node.border = -2 ∨ cn.node.border = 2) := by
    rw [hbord0]; decide
  obtain ⟨hsame, -⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 i cn hcn hnp
  have hcnEq : cn = pn := Option.some.inj (hsame.symm.trans hq0i)
  have hcnH : cn.node.h = pn.node.h := by rw [← hhh, hndEq]
  exact ⟨cn, hcn, hcnDum, by rw [← hcnEq]; exact hbord0, by rw [hcnEq], hcnH,
    by rw [hcnEq]⟩

/-- Copy of the private `frameRect_eq_nodeRect_of_plain`
(`RouteRunClearCases.lean`). -/
private theorem xfrf_frameRect_eq_nodeRect_of_plain {P : Params} {cg : Graph}
    {run : Run} {pos : Nat} {nd : Node} (hnd : cg.nodes[pos]? = some nd)
    (hplain : nd.border ≠ -2) :
    frameRect P cg run pos = nodeRect cg run pos := by
  have hget : cg.nodes.getD pos default = nd := by
    rw [List.getD_eq_getElem?_getD, hnd, Option.getD_some]
  have hb : ((cg.nodes.getD pos default).border != -2) = true := by
    rw [hget]
    simp only [bne_iff_ne]
    exact hplain
  unfold frameRect
  dsimp only
  rw [ite_eq_left hb]

/-- Copy of the private `nodeRect_eq_boxRect`
(`RouteLabelLeftoverPairProof.lean`). -/
private theorem xfrf_nodeRect_eq_boxRect {cg : Graph} {run : Run} {pos : Nat}
    {pn : ProperNode} (hlook : run.proper.nodes[pos]? = some pn) :
    nodeRect cg run pos = RouteImpl.boxRect run.proper run.xs run.ys pos := by
  have hget : run.proper.nodes.getD pos default = pn := by
    rw [List.getD_eq_getElem?_getD, hlook, Option.getD_some]
  have hw : RouteImpl.nodeW run.proper pos = pn.node.w := by
    unfold RouteImpl.nodeW
    simp only [hlook]
  have hh : RouteImpl.nodeH run.proper pos = pn.node.h := by
    unfold RouteImpl.nodeH
    simp only [hlook]
  unfold nodeRect RouteImpl.boxRect RouteImpl.xAt RouteImpl.yAt
  rw [hget, hw, hh]

/-- Narrow residual: scope-free forward clearance of a label stack rect
against a real box. Exact twin of `forwardRealClearScopeFree`
(`RouteLabelLeftoverPairProof.lean:96`), the scope-free form of
`runLocalForwardSeparation` (the scope premises are unused by that proof).
Probe: `ExactFwdClearFactsTProbe` reports `real=true` over scope-failing
real pairs, including the wider-than-slot fixed node sharing the dummy rank. -/
def XFR_ForwardScopeFreeX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ (k : Nat) (e : Edge) (env : Rect) (v : Nat) (r : Rect),
    (componentCandidate execution.graph comp candidate).edges[k]? = some e →
    e.tail ≠ e.head → e.reversed = false →
    labelEnvelope execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured
      k e = some env →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    r ∈ Labels.stackRects env.x env.y
      (componentCandidate execution.graph comp candidate).slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) →
    RectAxisSeparated r (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Proper nodes transport to coordinate nodes preserving border, dummy flag
and height (copy of `X_proper_to_coord_node`,
`ExactFlatC7Forward.lean:173`). -/
private theorem xfrf_proper_to_coord_node {P : Params} {exact : List Nat} {cg : Graph}
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

/-- Admission: every executed exact layout input is well-formed. Mirror of the
per-execution premise the plain `foreignFramesDisjoint_of_run` takes as
`hwf`; discharged at the family level where `layoutFamilyX` ensures it. -/

def XFR_WellFormedX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionX exactIds inp o res),
    WellFormed (inputModel inp o)

/-- Admission: every executed exact layout input has framed parents. Mirror
of the per-execution premise the plain proof takes as `hframed`. -/
def XFR_FramedX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionX exactIds inp o res),
    framedParents inp = true

/-- Exact placed label inside its dummy: placed labels of single-label
forward edges lie in their dummy rect. Replay of `routeLabelInDummy_of_run`
(`RouteRunClearCases.lean:525`) over `componentRunX`: edge identity through
`exactGraph_decls_nodup`, the anchor through `xfrf_forward_anchor_core` with
coincidence via `labelAnchorIndex_eq`, sizes through
`componentRunX_forward_anchor_size`, and the shared envelope/stack lemmas. -/
private theorem xfrf_inDummy (exactIds : List String)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run) :
    RouteLabelInDummy execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl hne hrev d nd hdummy hfindd
  have hnd := measureLabels_index_nodup execution.measured_eq
  obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv,
    hfindstk, hrfl⟩ := placedLabels_pair_inv hnd hmem
  have hml : ml = l₀ :=
    measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)
  have hdecl' : e'.decl = ml.edge := by
    obtain ⟨x, hx, hpx⟩ := xfrf_findIdxHitElem _ _ hfind
    have hee : e' = x := Option.some.inj (he'.symm.trans hx)
    have hpx2 : (x.decl == ml.edge) = true := hpx
    rw [← hee] at hpx2
    exact beq_iff_eq.mp hpx2
  subst hml
  have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
  have hdecls :
      ((componentCandidate execution.graph comp candidate).edges.map
        Edge.decl).Nodup := by
    have hndE := exactGraph_decls_nodup execution.graph0_eq execution.graph_eq
    exact componentCandidate_decls_nodup _ _ _ hndE
  have heq : edge = edge' := by
    have hmap :
        ((componentCandidate execution.graph comp candidate).edges.map
          Edge.decl)[edge]? =
          ((componentCandidate execution.graph comp candidate).edges.map
            Edge.decl)[edge']? := by
      simp only [List.getElem?_map, hedge, he', Option.map_some]
      exact congrArg some hdd
    have hlen : edge <
        ((componentCandidate execution.graph comp candidate).edges.map
          Edge.decl).length := by
      simpa only [List.length_map] using
        (List.getElem?_eq_some_iff.mp hedge).1
    exact (hdecls.getElem?_inj hlen).mp hmap
  subst heq
  have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
  subst hEE
  obtain ⟨first, q, hfirst, hqfind, hqenv⟩ := forward_envelope_eq hne hrev henv
  obtain ⟨aindex, and, hanchor, hnodeA, _, _, _, _⟩ :=
    xfrf_forward_anchor_core hrun hedge hne hfirst
  obtain ⟨aindex2, and2, hanchor2, hnode2, hwA0, hhA0⟩ :=
    componentRunX_forward_anchor_size hrun hedge hne hfirst
  have hidxEq : aindex2 = aindex := Option.some.inj (hanchor2.symm.trans hanchor)
  rw [hidxEq] at hnode2
  have hnd2and : and2 = and := Option.some.inj (hnode2.symm.trans hnodeA)
  rw [labelAnchorIndex_eq] at hanchor
  have hu : q.2 = aindex := by
    rw [hqfind] at hanchor
    exact Option.some.inj hanchor
  have hqq : q = (nd, d) := Option.some.inj (hqfind.symm.trans hfindd)
  have hq2 : q.2 = d := congrArg Prod.snd hqq
  have hq1a : q.1 = nd := congrArg Prod.fst hqq
  have hmemq : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hqfind)
  have hnodeA' : run.proper.nodes[q.2]? = some and := by
    rw [hu]
    exact hnodeA
  have hq1b : q.1 = and := Option.some.inj (hmemq.symm.trans hnodeA')
  have hndand : nd = and := hq1a.symm.trans hq1b
  have hwA : Labels.stackWidth
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) +
      first.gutter ≤ and.node.w := by
    have hwA' : Labels.stackWidth
        ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) +
        first.gutter ≤ and2.node.w := by
      rw [stackSize_width_eq] at hwA0
      omega
    rw [hnd2and] at hwA'
    exact hwA'
  have hhA : and.node.h =
      (stackSize (componentCandidate execution.graph comp candidate).slot
        (routeLabels execution.measured e.decl)).height := by
    rw [← hnd2and]
    exact hhA0
  have hlab := execution.measured_nonneg
  have hfm : first ∈ routeLabels execution.measured e.decl := by
    cases hrfl : routeLabels execution.measured e.decl with
    | nil => simp [hrfl] at hfirst
    | cons hd tl =>
      have heq2 : hd = first := by
        have h2 := hfirst
        rw [hrfl] at h2
        simpa using h2
      subst heq2
      exact List.mem_cons_self
  have hg0 : 0 ≤ first.gutter := (hlab first (List.mem_filter.mp hfm).1).2.2
  have hsizes : ∀ s ∈ (routeLabels execution.measured e.decl).map
      fun l => (l.width, l.height), 0 ≤ s.1 ∧ 0 ≤ s.2 := by
    intro s hs
    obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hs
    exact ⟨(hlab l (List.mem_filter.mp hlm).1).1,
      (hlab l (List.mem_filter.mp hlm).1).2.1⟩
  have hslot := componentRunX_slot_nonneg hrun
  have hmemd : run.proper.nodes[d]? = some nd := by
    rw [← hq2, ← hq1a]
    exact hmemq
  have hWd : RouteImpl.nodeW run.proper d = nd.node.w := by
    unfold RouteImpl.nodeW
    rw [hmemd]
  have hHd : RouteImpl.nodeH run.proper d = nd.node.h := by
    unfold RouteImpl.nodeH
    rw [hmemd]
  have he2 : env = Labels.textRectAt run.proper run.xs run.ys d first.gutter := by
    rw [hqenv, hq2]
  have henvW : env.w = nd.node.w - first.gutter := by
    simp only [he2, Labels.textRectAt, Labels.rectAt, Labels.labelRect, hWd, hHd]
  have henvH : env.h = nd.node.h := by
    simp only [he2, Labels.textRectAt, Labels.rectAt, Labels.labelRect, hWd, hHd]
  have hmemstk : rect ∈ Labels.stackRects env.x env.y
      ((componentCandidate execution.graph comp candidate).slot)
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) := by
    have hmstk := List.mem_of_find?_eq_some hfindstk
    have hzip := (List.of_mem_zip hmstk).2
    rw [← hrfl] at hzip
    exact hzip
  have hw : Labels.stackWidth
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) ≤ env.w := by
    have hwA' : Labels.stackWidth
        ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) ≤
        and.node.w - first.gutter := by
      omega
    rw [henvW, hndand]
    exact hwA'
  have hh : Labels.stackHeight
      ((componentCandidate execution.graph comp candidate).slot)
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) ≤ env.h := by
    rw [henvH, hndand, hhA, stackSize_height_eq]
    exact Int.le_refl _
  obtain ⟨_, _, hcont⟩ := Labels.stackRects_contained env
      ((componentCandidate execution.graph comp candidate).slot) hslot hsizes hw hh
      rect hmemstk
  have hsub : (Labels.rectAt run.proper run.xs run.ys d).Contained env := by
    have hex : env.x = (Labels.rectAt run.proper run.xs run.ys d).x + first.gutter := by
      rw [he2]
      rfl
    have hey : env.y = (Labels.rectAt run.proper run.xs run.ys d).y := by
      rw [he2]
      rfl
    have how : (Labels.rectAt run.proper run.xs run.ys d).w = nd.node.w := by
      unfold Labels.rectAt Labels.labelRect
      exact hWd
    have hoh : (Labels.rectAt run.proper run.xs run.ys d).h = nd.node.h := by
      unfold Labels.rectAt Labels.labelRect
      exact hHd
    unfold Rect.Contained
    omega
  exact Rect.Contained.trans hsub hcont

/-- Exact dummy-cell foreign clearance: every forward-edge mid-rank anchor
dummy cell misses every group frame whose declaration avoids the dummy's
cluster path. Replay of `routeLabelDummyCellForeignClear_of_run`
(`RouteLabelDummyCellProof.lean:30`) over `componentRunX`: the dummy is
border-0 through `xfrf_proper_to_coord_dummy`, rank bands through
`componentRunX_node_band` and `X_ReserveBands_holds`, tops through
`XB_topNonneg_holds`, and the bracket case through the three `XN_` seams. -/
private theorem xfrf_dummyCell (exactIds : List String)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplain : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds)
    (hwellformed : XFR_WellFormedX exactIds)
    (hframed : XFR_FramedX exactIds)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (edge : Nat) (e : Edge)
    (_hedge : (componentCandidate execution.graph comp candidate).edges[edge]? = some e)
    (_hne : e.tail ≠ e.head) (_hrev : e.reversed = false)
    (d : Nat) (nd : ProperNode) (hdummy : nd.dummy = true)
    (hfindd : run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge && rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (nd, d))
    (gpos : Nat) (gn : Node)
    (hu : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn)
    (hgrp : gn.border = -2)
    (hout : gn.decl ∉ nd.node.clusterPath) :
    Disjoint (Labels.rectAt run.proper run.xs run.ys d)
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run gpos) := by
  have hpropD : run.proper.nodes[d]? = some nd :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfindd)
  have hnotMem : nd.node.clusterPath.contains gn.decl = false := by
    rw [List.contains_eq_mem]
    simp only [hout, decide_false]
  obtain ⟨cn, hcn, _, hbordD, hbordND, hhND, _⟩ :=
    xfrf_proper_to_coord_dummy hrun hpropD hdummy
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨_edges, hrankEq, _nlen, _xlen, _records, hnp⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  obtain ⟨_len, _sz, _members, hcov, _edges2⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1
  have htopNN : ∀ r : Nat, (0 : Int) ≤ run.top.getD r 0 :=
    fun r => XB_topNonneg_holds exactIds hrun r
  have hdP : d < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hpropD).1
  obtain ⟨hinBand, hdisjBands⟩ := X_ReserveBands_holds exactIds hrun
  have hrecD : ∃ cw : ProperNode, run.coordinateProper.nodes[d]? = some cw ∧
      cw.node.border = nd.node.border ∧ cw.node.h = nd.node.h :=
    ⟨cn, hcn, hbordND, hhND⟩
  obtain ⟨lD, hlyD, hdTopBand, hdBotBand⟩ :=
    componentRunX_node_band hrun hpropD hrecD
  have hcovd := hcov d hdP
  obtain ⟨-, -, -, hdNN⟩ := hcovd
  have hrkDNN : 0 ≤ rk run.coordinateProper.rank d := by rw [← hranks]; exact hdNN
  have hysDNN : (0 : Int) ≤ run.ys.getD d 0 :=
    Int.le_trans (htopNN _) hdTopBand
  have hwf := hwellformed execution
  have hfp := hframed execution
  have hlines : execution.lines.length = inp.boxes.length :=
    boxLines_length execution.lines_eq
  by_cases hLow : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains gn.decl = true ∧
      (rk run.coordinateProper.rank q).toNat ≤ (rk run.coordinateProper.rank d).toNat
  · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains gn.decl = true ∧
      (rk run.coordinateProper.rank d).toNat ≤ (rk run.coordinateProper.rank q).toNat
    · -- the bracket case: marker pair at d's rank, aligned span, foreign clearance
      obtain ⟨low, lowNd, hlowRec, hlowCon, hlowLe⟩ := hLow
      obtain ⟨high, highNd, hhighRec, hhighCon, hhighGe⟩ := hHigh
      rw [← hranks] at hlowLe hhighGe
      obtain ⟨mL, mR, nL, nR, hcpmL, hborderL, hlastL, hrankL,
        hcpmR, hborderR, hlastR, hrankR⟩ :=
        hbracket execution.graph0_eq execution.graph_eq hlines hwf hfp hcomp hrun
          (rk run.proper.rank d).toNat
          hlowRec hlowCon hlowLe hhighRec hhighCon hhighGe
      have hnotProxyL : ¬(nL.node.border = -2 ∨ nL.node.border = 2) := by
        rw [hborderL]; omega
      have hnotProxyR : ¬(nR.node.border = -2 ∨ nR.node.border = 2) := by
        rw [hborderR]; omega
      obtain ⟨hnpRecL, -⟩ := hnp mL nL hcpmL hnotProxyL
      obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
      have hmarkRunL : run.proper.nodes[mL]? = some nL := by
        rw [hnodes]; exact hnpRecL
      have hmarkRunR : run.proper.nodes[mR]? = some nR := by
        rw [hnodes]; exact hnpRecR
      have hrankmDL : rk run.proper.rank mL = rk run.proper.rank d := by
        rw [hranks, hrankL, hranks]
        exact Int.toNat_of_nonneg hrkDNN
      have hrankmDR : rk run.proper.rank mR = rk run.proper.rank d := by
        rw [hranks, hrankR, hranks]
        exact Int.toNat_of_nonneg hrkDNN
      have hrankLR : rk run.proper.rank mL = rk run.proper.rank mR := by
        rw [hrankmDL, hrankmDR]
      obtain hsep :=
        hplain execution.graph0_eq execution.graph_eq hcomp hrun hpropD hbordD hnotMem
          hmarkRunL hborderL hlastL hmarkRunR hborderR hlastR hrankmDL hrankmDR
      have hmemRectL : Labels.rectAt run.proper run.xs run.ys mL ∈
          groupBorderRects (componentCandidate execution.graph comp candidate) run gn.decl :=
        groupBorderRects_mem_of_record hmarkRunL (Or.inl hborderL) hlastL
      have hneRects : groupBorderRects (componentCandidate execution.graph comp candidate) run
          gn.decl ≠ [] := by
        intro hnil
        rw [hnil] at hmemRectL
        simp at hmemRectL
      have hborderLOr : nL.node.border = -1 ∨ nL.node.border = 1 :=
        Or.inl hborderL
      have hborderROr : nR.node.border = -1 ∨ nR.node.border = 1 :=
        Or.inr hborderR
      have hcross :=
        (halignN execution.graph0_eq execution.graph_eq hcomp hrun hmarkRunL hborderLOr hlastL
          hmarkRunR hborderROr hlastR).2.2 ⟨hborderL, hborderR, hrankLR⟩
      have hall : ∀ r ∈ groupBorderRects (componentCandidate execution.graph comp candidate) run
          gn.decl,
          RouteImpl.leftOf run.proper run.xs mL ≤ r.x ∧
            r.x + r.w ≤ RouteImpl.leftOf run.proper run.xs mR +
              RouteImpl.nodeW run.proper mR := by
        intro r hr
        obtain ⟨q, nd, hq, hbq, hlastq, hrq⟩ := groupBorderRects_inv hr
        rcases hbq with hbqL | hbqR
        · obtain ⟨heq1, heq2⟩ :=
            (halignN execution.graph0_eq execution.graph_eq hcomp hrun hmarkRunL hborderLOr hlastL
              hq (Or.inl hbqL) hlastq).1 (by rw [hborderL, hbqL])
          rw [hrq, rectAt_eq]
          dsimp only
          rw [heq1, ← heq2]
          exact ⟨Int.le_refl _, hcross.2⟩
        · obtain ⟨heq1, heq2⟩ :=
            (halignN execution.graph0_eq execution.graph_eq hcomp hrun hmarkRunR hborderROr hlastR
              hq (Or.inr hbqR) hlastq).1 (by rw [hborderR, hbqR])
          rw [hrq, rectAt_eq]
          dsimp only
          refine ⟨?_, ?_⟩
          · rw [← heq1]; exact hcross.1
          · omega
      have hnonnegR :=
        (halignN execution.graph0_eq execution.graph_eq hcomp hrun hmarkRunR hborderROr hlastR
          hmarkRunR hborderROr hlastR).2.1
      have hminX := boundsOf_minX_ge_of_all hneRects (fun r hr => (hall r hr).1)
      have hright := boundsOf_right_le_of_all hnonnegR
        (fun r hr => (hall r hr).2)
      have hcontain := boundsOf_rect_mem hmemRectL
      rw [rectAt_eq] at hcontain
      rw [frameRect_group_span hu hgrp, rectAt_eq]
      unfold Disjoint Rect.meetsInterior
      simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
        hpropD, hmarkRunL, hmarkRunR,
        Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)]
        at hsep hcontain hminX hright ⊢
      omega
    · -- every member rank is strictly below d's rank
      have hAllBelow : ∀ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd →
          nd.node.clusterPath.contains gn.decl = true →
          (rk run.coordinateProper.rank q).toNat < (rk run.coordinateProper.rank d).toNat := by
        intro q nd hrec hcon
        refine Classical.byContradiction (fun hcontra => ?_)
        exact hHigh ⟨q, nd, hrec, hcon, by omega⟩
      have hmem : ∀ r ∈ groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl,
          r.y + r.h ≤ run.ys.getD d 0 := by
        intro r hr
        obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
        have hqP : q < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hq).1
        obtain ⟨pv, hpv, hbordQ, _, hhQ⟩ := xfrf_proper_to_coord_node hrun hq hqP
        obtain ⟨l, hly, _, hqBot⟩ :=
          componentRunX_node_band hrun hq ⟨pv, hpv, hbordQ, hhQ⟩
        have hband := hdisjBands
          (rk run.coordinateProper.rank q).toNat (rk run.coordinateProper.rank d).toNat
          l lD (hAllBelow q nd hq hcon) hly hlyD
        simp only [RouteImpl.nodeH, hq] at hqBot
        rw [hrq, rectAt_eq]
        simp only [RouteImpl.yAt, RouteImpl.nodeH, hq]
        omega
      have hbot := boundsOf_bottom_le_of_all hysDNN hmem
      rw [frameRect_group_span hu hgrp, rectAt_eq]
      refine rect_disjoint_of_y (Or.inr ?_)
      have hkey : (boundsOf (groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl) []).minY +
          ((boundsOf (groupMemberRects (componentCandidate execution.graph comp candidate) run
            gn.decl) []).bottom -
            (boundsOf (groupMemberRects (componentCandidate execution.graph comp candidate) run
              gn.decl) []).minY) ≤
          run.ys.getD d 0 := by omega
      exact hkey
  · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains gn.decl = true ∧
      (rk run.coordinateProper.rank d).toNat ≤ (rk run.coordinateProper.rank q).toNat
    · -- every member rank is strictly above d's rank
      by_cases hmemNil : groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl = []
      · rw [frameRect_group_span hu hgrp, hmemNil]
        refine disjoint_of_height_zero_right ?_
        show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
        rfl
      · have hmem : ∀ r ∈ groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl,
          run.ys.getD d 0 + RouteImpl.nodeH run.proper d ≤ r.y := by
          intro r hr
          obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
          have hqP : q < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hq).1
          obtain ⟨pv, hpv, hbordQ, _, hhQ⟩ := xfrf_proper_to_coord_node hrun hq hqP
          obtain ⟨l, hly, _, hqBot⟩ :=
            componentRunX_node_band hrun hq ⟨pv, hpv, hbordQ, hhQ⟩
          have hAllBelow : (rk run.coordinateProper.rank d).toNat <
              (rk run.coordinateProper.rank q).toNat := by
            refine Classical.byContradiction (fun hcontra => ?_)
            exact hLow ⟨q, nd, hq, hcon, by omega⟩
          have hband := hdisjBands
            (rk run.coordinateProper.rank d).toNat (rk run.coordinateProper.rank q).toNat
            lD l hAllBelow hlyD hly
          simp only [RouteImpl.nodeH, hq] at hqBot
          simp only [RouteImpl.nodeH, hpropD] at hdBotBand
          rw [hrq, rectAt_eq]
          dsimp only
          simp only [RouteImpl.yAt, RouteImpl.nodeH, hpropD]
          omega
        have htop := boundsOf_minY_ge_of_all hmemNil hmem
        simp only [RouteImpl.nodeH, hpropD] at htop
        rw [frameRect_group_span hu hgrp, rectAt_eq]
        refine rect_disjoint_of_y (Or.inl ?_)
        simp only [RouteImpl.yAt, RouteImpl.nodeH, hpropD] at ⊢
        omega
    · -- no member at all: the frame is flat
      have hmemNil : groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl = [] := by
        refine Classical.byContradiction (fun hne => ?_)
        cases hmem : groupMemberRects (componentCandidate execution.graph comp candidate) run
            gn.decl with
        | nil => exact hne hmem
        | cons r rest =>
          obtain ⟨q, nd, hq, hcon, _r⟩ :=
            groupMemberRects_inv (show r ∈ groupMemberRects
              (componentCandidate execution.graph comp candidate) run gn.decl by
              rw [hmem]; exact List.mem_cons_self)
          rcases (show (rk run.coordinateProper.rank q).toNat ≤
              (rk run.coordinateProper.rank d).toNat ∨
            (rk run.coordinateProper.rank d).toNat ≤
              (rk run.coordinateProper.rank q).toNat by omega) with hle | hle
          · exact hLow ⟨q, nd, hq, hcon, hle⟩
          · exact hHigh ⟨q, nd, hq, hcon, hle⟩
      rw [frameRect_group_span hu hgrp, hmemNil]
      refine disjoint_of_height_zero_right ?_
      show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
      rfl


/-- Executed exact `SeamsImplyForeign`: unrelated group frames of one exact
run are pairwise disjoint. Replay of `foreignFramesDisjoint_of_run`
(`RouteRunClearCases.lean:752`) over `componentRunX`: the group half through
`XB_foreignBorderSpansSeparated_holds` (with the three run facts
`XB_orderedIntervals_holds`, `XB_topNonneg_holds`, `XB_memberNonneg_holds`
reused outright) and the non-group half through
`XN_foreignNonGroupSpansClear_holds`, composed by `frameRect_disjoint_of_hulls`
exactly as the plain `foreignSpansClear_of_run` specializes to the group-vs-group
case. The plain `BracketMarkersAtRank` / `ForeignClusterRankSpans` hypotheses
are closed facts unused by the exact span assembly; the remaining seam
premises below mirror the plain open seams field for field. -/
theorem XFR_seamsImplyForeignX_holds (exactIds : List String)
    (hspans : XB_ForeignClusterRankSpans exactIds)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (halignB : XB_ForeignBorderChainXAligned exactIds)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplain : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds)
    (hwellformed : XFR_WellFormedX exactIds)
    (hframed : XFR_FramedX exactIds) :
    XFR_SeamsImplyForeignX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro _hbracket _hrank _hxalign
  intro g1 g2 n1 n2 hg1 hg2 hgrp1 hgrp2 hne hu1 hu2
  have hwf := hwellformed execution
  have hfp := hframed execution
  have hlines : execution.lines.length = inp.boxes.length :=
    boxLines_length execution.lines_eq
  have hgroups : XB_ForeignBorderSpansSeparated exactIds :=
    XB_foreignBorderSpansSeparated_holds exactIds hspans horder halignB
      (XB_orderedIntervals_holds exactIds) (XB_topNonneg_holds exactIds)
      (XB_memberNonempty_holds exactIds)
  have hothers : XN_ForeignNonGroupSpansClear exactIds :=
    XN_foreignNonGroupSpansClear_holds exactIds hbracket hplain halignN
  have hclear : ∀ (u w : Nat) (uNode wNode : Node),
      (componentCandidate execution.graph comp candidate).nodes[u]? = some uNode →
      (componentCandidate execution.graph comp candidate).nodes[w]? = some wNode →
      uNode.border = -2 → uNode.decl ≠ wNode.decl →
      wNode.clusterPath.contains uNode.decl = false →
      uNode.clusterPath.contains wNode.decl = false →
      Disjoint (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run u)
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run w) := by
    intro u w uNode wNode hu hw hgroupU hne hpathW hpathU
    by_cases hgroupW : wNode.border = -2
    · have hsep := hgroups execution.graph0_eq execution.graph_eq hlines hwf hfp
        hcomp hrun hu hw hgroupU hgroupW hne hpathW hpathU
      exact frameRect_disjoint_of_hulls hu hgroupU hw hgroupW hsep
    · exact hothers execution.graph0_eq execution.graph_eq hlines hwf hfp hcomp
        hrun hu hw hgroupU hgroupW hne hpathW hpathU
  exact hclear g1 g2 n1 n2 hg1 hg2 hgrp1 hne hu2 hu1

/-- Executed exact `RouteLabelForeignClear`: a placed forward label misses
every group frame outside its anchor dummy's cluster path. Replay of
`routeLabelForeignClear_of_run` (`RouteLabelForeignClearProof.lean:51`) over
`componentRunX`: the label lies in its dummy cell (`xfrf_inDummy` replay of
`routeLabelInDummy_of_run` above), the cell misses the foreign frame by
`xfrf_dummyCell`, and the two rectangles separate by containment. The
`X_ForeignBorderChainXAligned` premise is tracked for the marker-span
alignment; the bracket/plain/aligned `XN_` seams carry the span content. -/
theorem XFR_routeLabelForeignClearX_holds (exactIds : List String)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (hplain : XN_PlainClearOfSideMarker exactIds)
    (halignN : XN_SideMarkerSpanAligned exactIds)
    (hwellformed : XFR_WellFormedX exactIds)
    (hframed : XFR_FramedX exactIds)
    (_hchain : X_ForeignBorderChainXAligned exactIds) :
    XFR_RouteLabelForeignClearX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro _ _ _ _ k rect l₀ edge e hmem hmem0 hidx hedge hdecl hne hrev
    d nd hdummy hfindd gpos gn hg hgrp hout
  have hC := xfrf_inDummy exactIds execution hcomp hrun k rect l₀ edge e hmem
    hmem0 hidx hedge hdecl hne hrev d nd hdummy hfindd
  have hD := xfrf_dummyCell exactIds hbracket hplain halignN hwellformed hframed
    execution hcomp hrun edge e hedge hne hrev d nd hdummy hfindd gpos gn hg
    hgrp hout
  have hS : Disjoint rect (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run gpos) := by
    unfold Rect.Contained at hC
    unfold Disjoint Rect.meetsInterior at hD ⊢
    omega
  unfold Disjoint Rect.meetsInterior at hS ⊢
  omega

/-- Executed exact `RouteLabelLeftoverPair`: a placed label against an
in-bounds frame whose proper node is a nonzero dummy or a scope-failing real
node clears or strictly contains that frame. Replay of
`routeLabelLeftoverPair_of_run` (`RouteLabelLeftoverPairProof.lean:446`) over
`componentRunX`: nonzero dummies are impossible at original indices
(`X_componentRun_source_isReal`); scope-failing real nodes of forward edges
are cleared by the scope-free forward separation (`XFR_ForwardScopeFreeX`
above, twin of `forwardRealClearScopeFree`); group frames go through the
dummy-inside (`xfrf_inDummy` above) and foreign-disjointness cases, and
non-forward edges through the sibling nonforward clearance. The sibling
strict, foreign, dummy-existence, seams-imply, chain, and scope-free facts
are premises, as in the plain composition. -/
theorem XFR_routeLabelLeftoverPairX_holds (exactIds : List String)
    (hstrict : XFR_StrictDummyLinkedX exactIds)
    (hforeign : XFR_RouteLabelForeignClearX exactIds)
    (hloop : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionX exactIds inp o res)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate)
        execution.measured orderOptions = .ok run →
      RouteNonforwardLabelClear execution.params
        (componentCandidate execution.graph comp candidate) run
        execution.measured)
    (hdummy : XFR_DummyExLabeledX exactIds)
    (himp : XFR_SeamsImplyForeignX exactIds)
    (hxalign : ForeignBorderChainXAligned)
    (hscopeFree : XFR_ForwardScopeFreeX exactIds) :
    XFR_RouteLabelLeftoverPairX exactIds := by
  intro inp o res execution comp hcomp candidate run orderOptions hrun
  intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl pos hpos pn hlook hcase
  have hnd := measureLabels_index_nodup execution.measured_eq
  obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv,
    hfindstk, hrfl⟩ := placedLabels_pair_inv hnd hmem
  have hdecl' : e'.decl = ml.edge := by
    obtain ⟨x, hx, hpx⟩ := xfrf_findIdxHitElem _ _ hfind
    have hee : e' = x := Option.some.inj (he'.symm.trans hx)
    have hpx2 : (x.decl == ml.edge) = true := hpx
    rw [← hee] at hpx2
    exact beq_iff_eq.mp hpx2
  have hml : l₀ = ml :=
    (measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)).symm
  subst hml
  have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
  have hdecls :
      ((componentCandidate execution.graph comp candidate).edges.map
        Edge.decl).Nodup := by
    have hndE := exactGraph_decls_nodup execution.graph0_eq execution.graph_eq
    exact componentCandidate_decls_nodup _ _ _ hndE
  have heq : edge = edge' := by
    have hmap :
        ((componentCandidate execution.graph comp candidate).edges.map
          Edge.decl)[edge]? =
          ((componentCandidate execution.graph comp candidate).edges.map
            Edge.decl)[edge']? := by
      simp only [List.getElem?_map, hedge, he', Option.map_some]
      exact congrArg some hdd
    have hlen : edge <
        ((componentCandidate execution.graph comp candidate).edges.map
          Edge.decl).length := by
      simpa only [List.length_map] using
        (List.getElem?_eq_some_iff.mp hedge).1
    exact (hdecls.getElem?_inj hlen).mp hmap
  subst heq
  have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
  subst hEE
  have hv : pos < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hlook).1
  have hmemstk : rect ∈ Labels.stackRects env.x env.y
      (componentCandidate execution.graph comp candidate).slot
      ((routeLabels execution.measured e.decl).map fun l =>
        (l.width, l.height)) := by
    have hmstk := List.mem_of_find?_eq_some hfindstk
    have hzip := (List.of_mem_zip hmstk).2
    rw [← hrfl] at hzip
    exact hzip
  have hne : (componentCandidate execution.graph comp candidate).nodes[pos]? ≠ none := by
    intro h
    rw [List.getElem?_eq_none_iff] at h
    omega
  obtain ⟨nd, hnd⟩ := Option.ne_none_iff_exists'.mp hne
  have hbr : BracketMarkersAtRank := bracketMarkersAtRank'
  have hrk : ForeignClusterRankSpans := foreignClusterRankSpans'
  by_cases hfw : e.tail = e.head ∨ e.reversed = true
  · exact hloop execution hcomp hrun k rect l₀ edge e hmem hmem0 hidx hedge hdecl
      hfw pos hpos
  · have hne' : e.tail ≠ e.head := fun h => hfw (Or.inl h)
    have hnr : e.reversed = false := by
      cases hr : e.reversed with
      | true => rw [hr] at hfw; simp at hfw
      | false => rfl
    by_cases hgrp : nd.border = -2
    · obtain ⟨ndd, d, hddummy, hdfind⟩ := hdummy execution hcomp hrun
        edge e hedge hne' hnr ⟨l₀, hmem0, hdecl.symm⟩
      by_cases hpc : nd.decl ∈ ndd.node.clusterPath
      · have h2 := xfrf_inDummy exactIds execution hcomp hrun
        have hS := case_group_inside hmem hmem0 hidx hedge hdecl hne' hnr hnd
          hgrp hddummy hdfind hpc (hstrict execution hcomp hrun) h2
        exact Or.inr hS
      · have hI := himp execution hcomp hrun
        have hD := hforeign execution hcomp hrun hbr hrk hxalign hI k rect l₀
          edge e hmem hmem0 hidx hedge hdecl hne' hnr d ndd hddummy hdfind pos
          nd hnd hgrp hpc
        exact Or.inl hD
    · have hfr : frameRect execution.params
          (componentCandidate execution.graph comp candidate) run pos =
          nodeRect (componentCandidate execution.graph comp candidate) run pos :=
        xfrf_frameRect_eq_nodeRect_of_plain hnd hgrp
      have hbrr : nodeRect (componentCandidate execution.graph comp candidate) run pos =
          RouteImpl.boxRect run.proper run.xs run.ys pos :=
        xfrf_nodeRect_eq_boxRect hlook
      rcases hcase with ⟨hdummy, _⟩ | ⟨hI, _⟩
      · have hreal := X_componentRun_source_isReal hrun hnd
        have hfalse := hreal pn hlook
        rw [hdummy] at hfalse
        exact absurd hfalse (by decide)
      · have hsep := hscopeFree execution hcomp hrun edge e env pos rect hedge
          hne' hnr henv hv hI hmemstk
        have hdis := RectAxisSeparated_of_not_meetsInterior hsep
        rw [hfr, hbrr]
        apply Or.inl
        unfold Disjoint
        rw [Rect.meetsInterior_comm]
        exact hdis

end PipelineImpl
end Layered
end Elegant

import Elegant.Layered.RunLocalLabelClearanceProof
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.LabelsC7RunLocalFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.CoordGraph
import Elegant.Layered.FlatC6Loops

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Elegant Layered

/-! # Run-local label separations for the layered label-runs seam

Proves the three per-branch separation fields of `LayeredSeams`
(`RunLocalForwardSeparation`, `RunLocalReversedSeparation`,
`RunLocalLoopSeparation` in `RunLocalLabelClearanceProof`) from executed
component runs.

* Forward: the envelope is the text rect of the label dummy on its middle
  rank.  Nodes on other ranks are separated in `y` by the rank bands;
  nodes on the dummy's own rank are separated in `x` by the layer order.
  Endpoint boxes are covered too: the scope premises are simply unused.
* Reversed: the envelope sits in the planned lane right of every node.
* Loop: the envelope is contained in the loop footprint; the footprint
  separation itself stays the named residual `RunLocalLoopFootprint`
  (the loop-footprint phase), pinned to the executed run.
-/

/-- Axis separation rules out interior meeting. -/
theorem RectAxisSeparated_of_not_meetsInterior {a b : Rect}
    (h : Elegant.Layered.RectAxisSeparated a b) : ¬ a.meetsInterior b := by
  unfold Elegant.Layered.RectAxisSeparated at h
  unfold Rect.meetsInterior
  rcases h with h | h | h | h <;> omega

 /-- A stack entry starts at the envelope's left edge with a listed size. -/
theorem stackRects_entry {x y gap : Int} {sizes : List (Int × Int)} {r : Rect}
    (hr : r ∈ Labels.stackRects x y gap sizes) :
    r.x = x ∧ ∃ s ∈ sizes, r.w = s.1 ∧ r.h = s.2 :=
  Labels.stackRects_mem x gap sizes y r hr

/-- A stack entry is no wider than the stack width. -/
theorem stackRect_width_le {x y gap : Int} {sizes : List (Int × Int)} {r : Rect}
    (hr : r ∈ Labels.stackRects x y gap sizes) :
    r.w ≤ Labels.stackWidth sizes := by
  obtain ⟨_, s, hmem, hw, _⟩ := Labels.stackRects_mem x gap sizes y r hr
  have hle : s.1 ≤ Labels.stackWidth sizes := Labels.mem_le_foldl_max sizes 0 hmem
  omega

 /-- A stack entry respects the stack upper bound. -/
 theorem stackRect_upper_le {x y gap : Int} {sizes : List (Int × Int)} {r : Rect}
     (hgap : 0 ≤ gap)
     (hsizes : ∀ s ∈ sizes, 0 ≤ s.2)
     (hr : r ∈ Labels.stackRects x y gap sizes) :
     r.y + r.h ≤ y + Labels.stackHeight gap sizes :=
   Labels.stackRects_upper x gap hgap sizes y hsizes r hr

 /-- A stack entry starts no earlier than the stack origin. -/
 theorem stackRect_lower_le {x y gap : Int} {sizes : List (Int × Int)} {r : Rect}
     (hgap : 0 ≤ gap)
     (hsizes : ∀ s ∈ sizes, 0 ≤ s.2)
     (hr : r ∈ Labels.stackRects x y gap sizes) :
     y ≤ r.y :=
   Labels.stackRects_lower x gap hgap sizes y hsizes r hr

 /-- Execution parameters are valid. -/
 theorem execution_valid {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res) : execution.params.Valid :=
   checkedParams_valid execution.checked
 /-! ## Forward anchor transport -/

 /-- Labeled-stage anchors with an edge identity are dummy nodes:
 normalization only assigns edge identities to dummies, and the label fold
 preserves per-index edge and dummy flags. -/
 theorem labeled_anchor_plain {cg : Graph} {p0 labeled : Proper} {ranks : List Int}
     {labels : List MeasuredLabel} {k : Nat} {nd : ProperNode} {index : Nat}
     (hn : normalize cg ranks = .ok p0)
     (hl : Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled)
     (hnode : labeled.nodes[index]? = some nd) (hedge : nd.edge = some k) :
     nd.dummy = true := by
   have hkeys := (addLabelNodes_anchor_keys hl).2
   have hmap : (p0.nodes.map ProperNode.edge)[index]? = some (some k) := by
     rw [← hkeys]
     simp only [List.getElem?_map, hnode, Option.map_some, hedge]
   obtain ⟨nd0, h0, he0⟩ : ∃ nd0, p0.nodes[index]? = some nd0 ∧ nd0.edge = some k := by
     cases h00 : p0.nodes[index]? with
     | none => simp [h00] at hmap
     | some nd0 =>
       simp only [List.getElem?_map, h00, Option.map_some] at hmap
       exact ⟨nd0, rfl, Option.some.inj hmap⟩
   have hdummy0 : nd0.dummy = true :=
     normalize_edge_dummies hn nd0 (List.mem_of_getElem? h0) (by rw [he0]; simp)
   have hmeta := (Labels.addLabelNodes_metadata hl).2.2.2 index
   rw [hnode, h0] at hmeta
   simp only [Option.map_some, Option.some.injEq] at hmeta
   rw [hmeta]
   exact hdummy0

 /-- Dummy flags survive the coordinate-graph construction at a fixed index. -/
 theorem coordinateGraph_dummy_at {P : Params} {p : Proper} {i : Nat} {nd : ProperNode}
     (h : p.nodes[i]? = some nd) :
     ∃ out, (coordinateGraph P p).nodes[i]? = some out ∧ out.dummy = nd.dummy := by
   obtain ⟨sized, hsized, hd_sized⟩ :
       ∃ sized, (sizeProperPorts P p).nodes[i]? = some sized ∧ sized.dummy = nd.dummy := by
     unfold sizeProperPorts
     simp only [List.getElem?_map, List.getElem?_zipIdx, h, Option.map_some]
     split
     · exact ⟨_, rfl, rfl⟩
     · exact ⟨_, rfl, rfl⟩
   obtain ⟨titled, htitled, hd_titled⟩ :
       ∃ titled, (titleReservations (sizeProperPorts P p)).nodes[i]? = some titled ∧
         titled.dummy = nd.dummy := by
     rw [titleReservations_nodes,
       List.getElem?_append_left (by
         have hlt := (List.getElem?_eq_some_iff.mp hsized).1
         simpa using hlt)]
     simp only [List.getElem?_map, hsized, Option.map_some]
     obtain ⟨ha1, -, -, -⟩ := titleF_keys sized
     exact ⟨_, rfl, by rw [ha1, hd_sized]⟩
   obtain ⟨bordered, hbordered, hd_bordered⟩ :
       ∃ bordered, (OrderImpl.addClusterBorders
         (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[i]? =
           some bordered ∧ bordered.dummy = nd.dummy := by
     obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra
       (titleReservations (sizeProperPorts P p)) P.clusterBorderW
     have hlen2 : i < (titleReservations (sizeProperPorts P p)).nodes.length :=
       (List.getElem?_eq_some_iff.mp htitled).1
     rw [hnodes, List.getElem?_append_left hlen2, htitled]
     exact ⟨_, rfl, hd_titled⟩
   have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[i]? =
       (OrderImpl.addClusterBorders
         (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[i]?.map clearF := by
     rw [clearProxyExtents_nodes, List.getElem?_map]
   obtain ⟨ha1, -, -, -⟩ := clearF_keys bordered
   simp only [coordinateGraph, materializeDummyPaths, List.getElem?_map,
     List.getElem?_zipIdx, hclear, hbordered, Option.map_some]
   split
   · exact ⟨_, rfl, by simp [hd_bordered, ha1]⟩
   · exact ⟨_, rfl, by simp [hd_bordered, ha1]⟩

 /-- The executed run carries the selected forward label stack at the exact
 anchor the forward envelope uses: edge identity, dummy flag, plain border,
 and the measured width/height bounds. -/
 theorem forward_anchor_full {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     {k : Nat} {edge : Edge} {first : MeasuredLabel}
     (hrun : componentRun P cg labels orderOptions = .ok run)
     (hk : cg.edges[k]? = some edge) (hne : edge.tail ≠ edge.head)
     (hfirst : (routeLabels labels edge.decl).head? = some first) :
     ∃ index nd,
       labelAnchorIndex run.proper k
         (rk run.proper.rank edge.tail +
           Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2) =
           some index ∧
       run.proper.nodes[index]? = some nd ∧
       nd.edge = some k ∧ nd.dummy = true ∧ nd.node.border = 0 ∧
       (stackSize cg.slot (routeLabels labels edge.decl)).width + first.gutter ≤
         nd.node.w ∧
       nd.node.h = (stackSize cg.slot (routeLabels labels edge.decl)).height := by
   obtain ⟨ranks, p0, labeled, projected, hn, hl, hc, _, _, hproxy, hdrop, _hroute,
     _, _, _, _⟩ := componentRun_spec hrun
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
     coordinateGraph_plain_anchor_dims P hnode hborder
   obtain ⟨dout, hdout, hd_dout⟩ := coordinateGraph_dummy_at hnode
   have houtEq : dout = out := Option.some.inj (hdout.symm.trans hout)
   subst dout
   have hkeysPrefix := (coordinateGraph_anchor_prefix P labeled).1
   have hrankPrefix := (coordinateGraph_anchor_prefix P labeled).2
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
     change labelAnchorIndex projected k _ = some index
     unfold labelAnchorIndex
     rw [proxyWidths_edge_keys hproxy, hprank]
     exact hicoord
   have hedgeP : out.edge = some k := hedgeOut.trans hedge
   have hborderP : out.node.border = 0 := hborderOut
   have hdummyP : out.dummy = true := hd_dout.trans hdummy
   refine ⟨index, out, hanchor, hlookup, hedgeP, hdummyP, hborderP, ?_, ?_⟩
   · rw [← hw]
     exact hwOut
   · exact hhOut.trans hh

 /-! ## Forward separation -/

 /-- Proper nodes transport to coordinate nodes preserving border, dummy flag
 and height. -/
 theorem proper_to_coord_node {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P cg labels orderOptions = .ok run)
     {v : Nat} {qv : ProperNode} (hqv : run.proper.nodes[v]? = some qv)
     (hv : v < run.proper.nodes.length) :
     ∃ pv, run.coordinateProper.nodes[v]? = some pv ∧
       pv.node.border = qv.node.border ∧ pv.dummy = qv.dummy ∧
       pv.node.h = qv.node.h := by
   obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
     componentRun_spec hrun
   have hplen : v < run.coordinateProper.nodes.length := by
     have h1 := (proxyWidths_rel hproxy).2.2.1
     have h2 : run.proper.nodes = routed.nodes := by
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

 /-- Invert the forward `labelEnvelope` branch: the envelope is the anchor's
 text rect and the find? witness carries the edge and rank. -/
 theorem forward_envelope_eq {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
     (hne : e.tail ≠ e.head) (hrev : e.reversed = false)
     (henv : labelEnvelope P cg run labels k e = some env) :
     ∃ first q,
       (routeLabels labels e.decl).head? = some first ∧
       run.proper.nodes.zipIdx.find? (fun qq =>
         qq.1.edge == some k &&
           rk run.proper.rank qq.2 ==
             (rk run.proper.rank e.tail +
               Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2)) =
         some q ∧
       env = Labels.textRectAt run.proper run.xs run.ys q.2 first.gutter := by
   unfold labelEnvelope at henv
   obtain ⟨first, hfirst, hrest⟩ := Option.bind_eq_some_iff.mp henv
   have hb : (e.tail == e.head) = false := by simp [hne]
   simp only [hb, hrev] at hrest
   obtain ⟨q, hq, hqenv⟩ := Option.bind_eq_some_iff.mp hrest
   exact ⟨first, q, hfirst, hq, (Option.some.inj hqenv).symm⟩
 /-- Forward separation holds for every executed flat layout: the envelope
 sits on the label dummy's rank band, so nodes on other ranks are separated
 in `y` by the bands and nodes on the same rank in `x` by the layer order. -/
 theorem runLocalForwardSeparation :
     ∀ inp o res, RunLocalForwardSeparation inp o res := by
   intro inp o res execution comp candidate run orderOptions cg k e env v r
     hcomp hcg hrun hk hne hrev henv hv hreal _hscope₀ _hscope₁ hr
   have hslot := componentRun_slot_nonneg hrun
   have hlab := execution.measured_nonneg
   have hP := execution_valid execution
   have hnd : (cg.edges.map (·.decl)).Nodup := by
     rw [hcg]
     exact componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
   have hshape : CgShape cg := by
     rw [hcg]
     exact componentCandidate_shape (components_nodup execution.graph comp hcomp)
       (measuredGraph_shape execution.graph_eq) candidate
   have hfacts := componentRun_labelFacts hP hnd hshape hrun
   have hrun' : componentRun execution.params
       (componentCandidate execution.graph comp candidate) execution.measured
       orderOptions = .ok run := by
     rw [← hcg]
     exact hrun
   obtain ⟨first, q, hfirst, hqfind, henv_eq⟩ := forward_envelope_eq hne hrev henv
   have hpred := List.find?_some hqfind
   simp only [Bool.and_eq_true, beq_iff_eq] at hpred
   obtain ⟨aindex, and, hanchor, hnodeA, _hedgeA, hdummyA, hborderA, hwA, hhA⟩ :=
     forward_anchor_full hrun hk hne hfirst
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
   have hsizes : ∀ s ∈ (routeLabels execution.measured e.decl).map fun l => (l.width, l.height),
       0 ≤ s.1 ∧ 0 ≤ s.2 := by
     intro s hs
     obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hs
     exact ⟨(hlab l (List.mem_filter.mp hlm).1).1, (hlab l (List.mem_filter.mp hlm).1).2.1⟩
   have hsizes2 : ∀ s ∈ (routeLabels execution.measured e.decl).map fun l => (l.width, l.height),
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
   obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop', hrLanes, _hroutEq, hyT,
       hysEq, _hrts⟩ :=
     componentRun_spec hrun
   have hlay : RouteImpl.layersOk run.proper run.layers = true :=
     (RouteImpl.routeWithLanes_geometry hrLanes).1
   have hcov := (RouteImpl.layersOk_spec hlay).2.2.2.1
   obtain ⟨lu, hlu_mem, hu_mem, hu_nn⟩ := hcov aindex hu_len
   obtain ⟨qv, hqv⟩ : ∃ qv, run.proper.nodes[v]? = some qv :=
     ⟨_, List.getElem?_eq_getElem hv⟩
   obtain ⟨lv, hlv_mem, hv_mem, hv_nn⟩ := hcov v hv
   have hrkU : rk run.proper.rank aindex = ((rk run.proper.rank aindex).toNat : Int) :=
     (Int.toNat_of_nonneg hu_nn).symm
   have hrkV : rk run.proper.rank v = ((rk run.proper.rank v).toNat : Int) :=
     (Int.toNat_of_nonneg hv_nn).symm
   have hbandU := hfacts.node_in_band _ _ _ hlu_mem hu_mem hu_len hrkU
   have hbandV := hfacts.node_in_band _ _ _ hlv_mem hv_mem hv hrkV
   have htop : ∀ r r' (lr lr' : List Nat), r < r' → run.layers[r]? = some lr →
       run.layers[r']? = some lr' →
       run.top.getD r 0 + CoordsImpl.layerHeight run.proper lr ≤
         run.top.getD r' 0 := by
     intro r r' lr lr' hrr h1 h2
     rw [layerHeight_eq_route]
     exact hfacts.bands_disjoint r r' lr lr' hrr h1 h2
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
       proper_to_coord_node hrun hnodeA hu_len
     obtain ⟨pv, hpv, hpv_border, _hpv_dummy, _hpv_h⟩ :=
       proper_to_coord_node hrun hqv hv
     have hpu0 : pu.node.border = 0 := by
       rw [hpu_border]
       exact hborderA
     by_cases hfr : qv.node.border = -2 ∨ qv.node.border = 2
     · -- Foreign frame on the same band: band-edge separation.
       have hpv2 : pv.node.border = qv.node.border := hpv_border
       rcases hfr with hb2 | hb2
       · have hbeq : (pv.node.border == -2) = true := by simp [hpv2, hb2]
         have hcylen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
           obtain ⟨_, _, _, _, _, _, hyvv⟩ := CoordsImpl.rankCoordsWith_spec hyT
           rw [hyvv, List.length_map, List.length_range]
         have hlen_cy : v < run.coordinateYs.length := by
           have hplen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
             have h1 := (proxyWidths_rel hproxy).2.2.1
             have h2 : run.proper.nodes = routed.nodes := by
               rw [← hdrop']
               exact OrderImpl.dropSynthetic_nodes _
             rw [h2]
             exact h1
           rw [hcylen, ← hplen]
           exact hv
         have hqr : run.proper.rank = run.coordinateProper.rank := by
           have h1 := (proxyWidths_rel hproxy).2.1
           rw [← hdrop']
           simpa only [OrderImpl.dropSynthetic_rank] using h1
         have hrk_eq : (rk run.coordinateProper.rank v).toNat =
             (rk run.proper.rank aindex).toNat := by
           rw [← hqr, ← heq]
         have hyv : RouteImpl.yAt run.ys v =
             run.top.getD (rk run.proper.rank aindex).toNat 0 := by
           have hys_eq : run.ys =
              proxyYs run.coordinateProper run.layers run.top run.coordinateYs := hysEq.symm
           rw [hys_eq]
           unfold RouteImpl.yAt
           have hpg := proxyYs_getD run.coordinateProper run.layers run.top
             run.coordinateYs hpv hlen_cy
           rw [hpg, hbeq]
           simp only [↓reduceIte]
           rw [hrk_eq]
         have hframe : RouteImpl.IsFrame run.proper v := by
           rw [isFrame_iff hqv]
           exact ⟨hreal qv hqv, Or.inl hb2⟩
         have hfh : RouteImpl.nodeH run.proper v = 0 := hfacts.frame_flat v hframe
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
         have hcylen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
           obtain ⟨_, _, _, _, _, _, hyvv⟩ := CoordsImpl.rankCoordsWith_spec hyT
           rw [hyvv, List.length_map, List.length_range]
         have hlen_cy : v < run.coordinateYs.length := by
           have hplen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
             have h1 := (proxyWidths_rel hproxy).2.2.1
             have h2 : run.proper.nodes = routed.nodes := by
               rw [← hdrop']
               exact OrderImpl.dropSynthetic_nodes _
             rw [h2]
             exact h1
           rw [hcylen, ← hplen]
           exact hv
         have hqr : run.proper.rank = run.coordinateProper.rank := by
           have h1 := (proxyWidths_rel hproxy).2.1
           rw [← hdrop']
           simpa only [OrderImpl.dropSynthetic_rank] using h1
         have hrk_eq : (rk run.coordinateProper.rank v).toNat =
             (rk run.proper.rank aindex).toNat := by
           rw [← hqr, ← heq]
         have hLH : CoordsImpl.layerHeight run.coordinateProper lu =
             RouteImpl.layerHeight run.proper lu := by
           rw [layerHeight_eq_route]
           have hHH : (fun w => RouteImpl.nodeH run.proper w) =
               (fun w => RouteImpl.nodeH run.coordinateProper w) := by
             funext w
             have h1 := nodeH_proxy hproxy w
             have h2 : run.proper.nodes = routed.nodes := by
               rw [← hdrop']
               exact OrderImpl.dropSynthetic_nodes _
             have h3 : RouteImpl.nodeH run.proper w = RouteImpl.nodeH routed w := by
               unfold RouteImpl.nodeH
               rw [h2]
             rw [h3]
             exact h1
           simp only [RouteImpl.layerHeight, hHH]
         have hget : run.layers.getD (rk run.proper.rank aindex).toNat [] = lu := by
           rw [List.getD_eq_getElem?_getD, hlu_mem]
           rfl
         have hyv : RouteImpl.yAt run.ys v =
             run.top.getD (rk run.proper.rank aindex).toNat 0 +
               RouteImpl.layerHeight run.proper lu := by
           have hys_eq : run.ys =
              proxyYs run.coordinateProper run.layers run.top run.coordinateYs := hysEq.symm
           rw [hys_eq]
           unfold RouteImpl.yAt
           have hpg := proxyYs_getD run.coordinateProper run.layers run.top
             run.coordinateYs hpv hlen_cy
           rw [hpg, hbeq, hbeq2]
           simp only [Bool.false_eq_true, ↓reduceIte]
           rw [hrk_eq, hget, hLH]
         apply Or.inr; apply Or.inr; apply Or.inl
         have hup : r.y + r.h ≤ env.y +
             Labels.stackHeight cg.slot
               ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) :=
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
       · have hord := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp
           hrun' hlayer_mem hlt hi hj hpu hpv hnb1 hnb2
         apply Or.inl
         have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).x =
             RouteImpl.xAt run.xs v - Int.fdiv (RouteImpl.nodeW run.proper v) 2 :=
          boxRect_left _ _ _ _
         rw [hrx, henvx, hbox, e1, e2]
         unfold RouteImpl.leftOf at hord
         have hwle : Labels.stackWidth
             ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) +
             first.gutter ≤ RouteImpl.nodeW run.proper aindex := by
           rw [hWu, ← stackSize_width_eq]
           exact hwA
         omega
       · have hord := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp
           hrun' hlayer_mem hgt hj hi hpv hpu hnb2 hnb1
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
     have hne2 : (rk run.proper.rank aindex).toNat ≠ (rk run.proper.rank v).toNat := heq
     rcases Nat.lt_or_gt_of_ne hne2 with hlt | hgt
     · have hband := rank_band_above hlu_mem hlv_mem hlt htop hbandU hbandV.1
       apply Or.inr; apply Or.inr; apply Or.inl
       have hup : r.y + r.h ≤ env.y +
           Labels.stackHeight cg.slot
             ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height)) :=
         stackRect_upper_le hslot hsizes2 hr
       have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
          RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
       rw [hbox]
       omega
     · have hband := rank_band_below hlu_mem hlv_mem hgt htop hbandU.1 hbandV
       apply Or.inr; apply Or.inr; apply Or.inr
       have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).y =
          RouteImpl.yAt run.ys v := boxRect_top _ _ _ _
       have hboxh : (RouteImpl.boxRect run.proper run.xs run.ys v).h =
          RouteImpl.nodeH run.proper v := boxRect_h _ _ _ _
       have hlo : env.y ≤ r.y := stackRect_lower_le hslot hsizes2 hr
       rw [henvy] at hlo
       rw [hbox, hboxh]
       omega

 /-! ## Reversed separation -/

 /-- Invert the reversed `labelEnvelope` branch: the envelope sits in the
 planned lane. -/
 theorem reversed_envelope_eq {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
     (hne : e.tail ≠ e.head) (hrev : e.reversed = true)
     (henv : labelEnvelope P cg run labels k e = some env) :
     ∃ first lane,
       (routeLabels labels e.decl).head? = some first ∧
       run.lanes.runs.find? (fun lane => lane.original == k) = some lane ∧
       env = RouteImpl.reversedLabelRect cg.slot run.top
         (run.layers.map (RouteImpl.layerHeight run.proper)) run.routing lane
         (stackSize cg.slot (routeLabels labels e.decl)).width
         (stackSize cg.slot (routeLabels labels e.decl)).height := by
   unfold labelEnvelope at henv
   obtain ⟨first, hfirst, hrest⟩ := Option.bind_eq_some_iff.mp henv
   have hb : (e.tail == e.head) = false := by simp [hne]
   simp only [hb, hrev] at hrest
   obtain ⟨lane, hlane, henv2⟩ := Option.bind_eq_some_iff.mp hrest
   exact ⟨first, lane, hfirst, hlane, (Option.some.inj henv2).symm⟩

 /-- Reversed separation holds for every executed flat layout: the envelope
 sits in the planned lane, strictly right of every node box. -/
 theorem runLocalReversedSeparation :
     ∀ inp o res, RunLocalReversedSeparation inp o res := by
   intro inp o res execution comp candidate run orderOptions cg k e env v r
     hcomp hcg hrun hk hne hrev henv hv hreal _hscope₀ _hscope₁ hr
   have _hslot := componentRun_slot_nonneg hrun
   obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrLanes, _, _, _, _⟩ :=
     componentRun_spec hrun
   obtain ⟨_first, lane, _hfirst, hlane, henv_eq⟩ := reversed_envelope_eq hne hrev henv
   have hmem : lane ∈ run.lanes.runs := List.mem_of_find?_eq_some hlane
   obtain ⟨base, _, h1slot, hlr⟩ := RouteImpl.routeWithLanes_spec hrLanes
   rw [hlr] at hmem
   have hge := RouteImpl.plannedLane_right_strict (by omega : 0 ≤ execution.params.slot) hmem
   have hbound := RouteImpl.laneRight_bound run.proper run.xs hv
   have hrx : r.x = env.x := (stackRects_entry hr).1
   have henvx : env.x = lane.lane + cg.slot := by
     rw [henv_eq]
     rfl
   have hbox : (RouteImpl.boxRect run.proper run.xs run.ys v).x =
       RouteImpl.xAt run.xs v - Int.fdiv (RouteImpl.nodeW run.proper v) 2 :=
    boxRect_left _ _ _ _
   have hboxw : (RouteImpl.boxRect run.proper run.xs run.ys v).w =
       RouteImpl.nodeW run.proper v :=
    boxRect_w _ _ _ _
   have hloop : 0 ≤ (run.proper.nodes.getD v default).node.loopExtent :=
     Nat.zero_le _
   have e2 : Int.fdiv (RouteImpl.nodeW run.proper v) 2 =
       RouteImpl.nodeW run.proper v / 2 := fdiv2_ediv _
   rw [hrx, henvx, hbox, hboxw, e2]
   rw [e2] at hbound
   omega

 /-- A successful component run has no exact ports. -/
 theorem run_exact_nil {P : Params} {cg : Graph} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions} {run : Run}
     (h : componentRun P cg labels orderOptions = .ok run) : run.exact = [] := by
   unfold componentRun at h
   obtain ⟨_, _, h⟩ := bind_ok h
   obtain ⟨_, _, h⟩ := bind_ok h
   obtain ⟨_, _, h⟩ := bind_ok h
   obtain ⟨_, _, h⟩ := bind_ok h
   obtain ⟨_, _, h⟩ := bind_ok h
   obtain ⟨_, _, h⟩ := bind_ok h
   obtain ⟨_, _, h⟩ := bind_ok h
   obtain ⟨_, _, h⟩ := bind_ok h
   obtain ⟨_, _, h⟩ := bind_ok h
   have h := Except.ok.inj h
   subst h
   rfl

 /-- Foldl max lower bound for loop label heights. -/
 theorem foldl_max_height_ge (sizes : List LoopLabel) (acc : Int) :
     acc ≤ sizes.foldl (fun h l => max h l.height) acc := by
   induction sizes generalizing acc with
   | nil => exact Int.le_refl _
   | cons s rest ih =>
     simp only [List.foldl]
     exact Int.le_trans (Int.le_max_left acc s.height) (ih (max acc s.height))

 /-- Foldl max is monotone in its accumulator. -/
 theorem foldl_max_mono_acc (l : List LoopLabel) (acc acc' : Int) (h : acc ≤ acc') :
     l.foldl (fun h l => max h l.height) acc ≤
       l.foldl (fun h l => max h l.height) acc' := by
   induction l generalizing acc acc' with
   | nil => exact h
   | cons b rest ih =>
     simp only [List.foldl]
     exact ih _ _ (by omega)

 /-- Every member height is bounded by the loop band. -/
 theorem loopBand_ge_mem_aux (slot : Int) :
     ∀ (sizes : List LoopLabel) (s : LoopLabel), s ∈ sizes →
       s.height ≤ Loops.band slot sizes := by
   intro sizes
   induction sizes with
   | nil => intro s hs; simp at hs
   | cons a rest ih =>
     intro s hs
     simp only [List.mem_cons] at hs
     unfold Loops.band
     simp only [List.foldl]
     rcases hs with rfl | hs
     · exact Int.le_trans (Int.le_max_right _ _) (foldl_max_height_ge rest _)
     · exact Int.le_trans (ih s hs) (foldl_max_mono_acc rest _ _ (Int.le_max_left _ _))

 /-- Foldl add distributes a shifted accumulator. -/
 theorem foldl_add_acc {α : Type} (l : List α) (f : α → Int) (acc : Int) :
     (l.map f).foldl (· + ·) acc = acc + (l.map f).foldl (· + ·) 0 := by
   induction l generalizing acc with
   | nil => simp
   | cons a rest ih =>
     simp only [List.map_cons, List.foldl]
     rw [ih (acc + f a), ih (0 + f a)]
     omega

 /-- Foldl add dominates the accumulator for nonneg summands. -/
 theorem foldl_add_ge_acc {α : Type} (f : α → Int) :
     ∀ (l : List α) (acc : Int), (∀ x ∈ l, 0 ≤ f x) →
       acc ≤ (l.map f).foldl (· + ·) acc := by
   intro l
   induction l with
   | nil => intro acc _; simp
   | cons a rest ih =>
     intro acc hpos
     simp only [List.map_cons, List.foldl]
     have h1 : acc ≤ acc + f a := by
       have := hpos a List.mem_cons_self
       omega
     exact Int.le_trans h1 (ih (acc + f a) (fun x hx => hpos x (List.mem_cons_of_mem _ hx)))

 /-- Foldl add dominates any member value. -/
 theorem foldl_add_ge_mem {α : Type} (f : α → Int) :
     ∀ (l : List α) (s : α), (∀ x ∈ l, 0 ≤ f x) → s ∈ l →
       f s ≤ (l.map f).foldl (· + ·) 0 := by
   intro l
   induction l with
   | nil => intro s _ hs; simp at hs
   | cons a rest ih =>
     intro s hpos hs
     simp only [List.mem_cons] at hs
     simp only [List.map_cons, List.foldl]
     rcases hs with hseq | hs
     · rw [hseq]; exact Int.le_trans (by omega) (foldl_add_ge_acc f rest (0 + f a)
         (fun x hx => hpos x (List.mem_cons_of_mem _ hx)))
     · have h1 := ih s (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) hs
       have h2 : (rest.map f).foldl (· + ·) 0 ≤ (rest.map f).foldl (· + ·) (0 + f a) := by
         rw [foldl_add_acc rest f (0 + f a)]
         have hfa := hpos a List.mem_cons_self
         omega
       exact Int.le_trans h1 h2

 /-- Foldl add splits over a pointwise sum. -/
 theorem foldl_add_split {α : Type} (f g : α → Int) :
     ∀ (l : List α) (acc : Int),
     (l.map fun x => f x + g x).foldl (· + ·) acc =
       (l.map f).foldl (· + ·) acc + (l.map g).foldl (· + ·) 0 := by
   intro l
   induction l with
   | nil => intro acc; simp
   | cons a rest ih =>
     intro acc
     simp only [List.map_cons, List.foldl]
     rw [ih (acc + (f a + g a))]
     rw [foldl_add_acc _ f (acc + (f a + g a)), foldl_add_acc _ f (acc + f a),
       foldl_add_acc _ g (0 + g a), foldl_add_acc _ g 0]
     omega

 /-- First components of zipped indices lie in the original list. -/
 theorem fst_mem_of_mem_zipIdx {sizes : List LoopLabel} {q : LoopLabel × Nat}
     (hmem : q ∈ sizes.zipIdx) : q.1 ∈ sizes :=
   List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hmem)

 /-- The loop extent dominates the lane offset plus any member width. -/
 theorem extent_ge_lane_width {slot : Int} (hs : 0 ≤ slot) {sizes : List LoopLabel}
     (hw : ∀ s ∈ sizes, 0 ≤ s.width) {w : LoopLabel} (hmem : w ∈ sizes)
     (hn : 1 ≤ sizes.length) :
     slot * ((sizes.length : Int) + 1) + w.width ≤ Loops.extent slot sizes := by
   have hsplit := foldl_add_split
     (fun q : LoopLabel × Nat => slot * ((q.2 : Int) + 2))
     (fun q : LoopLabel × Nat => q.1.width) sizes.zipIdx 0
   have hext : Loops.extent slot sizes =
       (((sizes.zipIdx).map fun q : LoopLabel × Nat => slot * ((q.2 : Int) + 2)).foldl
           (· + ·) 0 +
         ((sizes.zipIdx).map fun q : LoopLabel × Nat => q.1.width).foldl (· + ·) 0) := by
     unfold Loops.extent
     exact hsplit
   have hA : slot * ((sizes.length : Int) + 1) ≤
       (((sizes.zipIdx).map fun q : LoopLabel × Nat => slot * ((q.2 : Int) + 2)).foldl
          (· + ·) 0) := by
     have hn1 : 0 < sizes.length := by omega
     obtain ⟨s', hs'⟩ : ∃ s', sizes[sizes.length - 1]? = some s' :=
       ⟨_, List.getElem?_eq_getElem (by omega : sizes.length - 1 < sizes.length)⟩
     have hz : (sizes.zipIdx)[sizes.length - 1]? = some (s', 0 + (sizes.length - 1)) := by
       rw [List.getElem?_zipIdx, hs']
       rfl
     have hmemA : (s', 0 + (sizes.length - 1)) ∈ sizes.zipIdx :=
       List.mem_of_getElem? hz
     have hle := foldl_add_ge_mem (fun q : LoopLabel × Nat => slot * ((q.2 : Int) + 2))
       sizes.zipIdx (s', 0 + (sizes.length - 1))
       (fun q _ => by
         have h1 : (0 : Int) ≤ (q.2 : Int) := Int.natCast_nonneg _
         have h2 : (0 : Int) ≤ (q.2 : Int) + 2 := by omega
         exact Int.mul_nonneg hs h2) hmemA
     dsimp only at hle
     have hzero : (0 + (sizes.length - 1) : Nat) = sizes.length - 1 := by omega
     rw [hzero] at hle
     have hcast : (((sizes.length - 1 : Nat) : Int)) + 2 = (sizes.length : Int) + 1 := by
       omega
     rw [hcast] at hle
     exact hle
   have hW : w.width ≤
       (((sizes.zipIdx).map fun q : LoopLabel × Nat => q.1.width).foldl (· + ·) 0) := by
     obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
     have hz : (sizes.zipIdx)[j]? = some (w, 0 + j) := by
       rw [List.getElem?_zipIdx, hj]
       rfl
     have hmemW : (w, 0 + j) ∈ sizes.zipIdx := List.mem_of_getElem? hz
     have hle := foldl_add_ge_mem (fun q : LoopLabel × Nat => q.1.width)
       sizes.zipIdx (w, 0 + j) (fun q hq => hw q.1 (fst_mem_of_mem_zipIdx hq)) hmemW
     simpa using hle
   omega
 /-- Invert the loop `labelEnvelope` branch. -/
 theorem loop_envelope_eq {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
     (hloop : e.tail = e.head) (hexact : run.exact = [])
     (henv : labelEnvelope P cg run labels k e = some env) :
     env = (Loops.placement (frameRect P cg run e.tail) cg.slot
       (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
       (loopEdges cg.edges e.tail).length
       (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
       (stackSize cg.slot (routeLabels labels e.decl))).label := by
   unfold labelEnvelope at henv
   obtain ⟨_first, _hfirst, hrest⟩ := Option.bind_eq_some_iff.mp henv
   have hb : (e.tail == e.head) = true := by simp [hloop]
   have hnoex : run.exact.contains e.tail = false := by simp [hexact]
   simp only [hb, hnoex] at hrest
   exact (Option.some.inj hrest).symm

 /-- The loop envelope is contained in the loop footprint, given the loop
 reservation. -/
 theorem loop_envelope_contained {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
     (hslot : 0 ≤ cg.slot)
     (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
     (hexact : run.exact = [])
     (hk : cg.edges[k]? = some e) (hloop : e.tail = e.head)
     (henv_eq : env = (Loops.placement (frameRect P cg run e.tail) cg.slot
       (Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot))
       (loopEdges cg.edges e.tail).length
       (((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl)
       (stackSize cg.slot (routeLabels labels e.decl))).label)
     (hrsv : (loopSizes cg.edges labels e.tail cg.slot).length *
         Loops.band cg.slot (loopSizes cg.edges labels e.tail cg.slot) ≤
       (frameRect P cg run e.tail).h) :
     (loopFootprint cg run labels e.tail).Contained env := by
   have he0 : e ∈ loopEdges cg.edges e.tail := by
     have hkm : e ∈ cg.edges := List.mem_of_getElem? hk
     apply List.mem_filter.mpr
     exact ⟨hkm, by simp [hloop]⟩
   have hnn : ∀ s ∈ loopSizes cg.edges labels e.tail cg.slot, 0 ≤ s.width ∧ 0 ≤ s.height := by
     intro s hs
     obtain ⟨e', _he', rfl⟩ := List.mem_map.mp hs
     rw [stackSize_width_eq, stackSize_height_eq]
     refine ⟨Labels.stackWidth_nonneg _, ?_⟩
     exact Labels.stackHeight_nonneg _ hslot (fun t ht => by
       obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp ht
       exact (hlab l (List.mem_filter.mp hlm).1).2.1)
   obtain ⟨F, hF⟩ : ∃ F, F = frameRect P cg run e.tail := ⟨_, rfl⟩
   obtain ⟨sizes, hsizes⟩ : ∃ sizes, sizes = loopSizes cg.edges labels e.tail cg.slot := ⟨_, rfl⟩
   obtain ⟨n, hn⟩ : ∃ n, n = sizes.length := ⟨_, rfl⟩
   obtain ⟨band, hband⟩ : ∃ band, band = Loops.band cg.slot sizes := ⟨_, rfl⟩
   obtain ⟨idx, hidx⟩ : ∃ idx, idx = ((loopEdges cg.edges e.tail).map (·.decl)).idxOf e.decl := ⟨_, rfl⟩
   obtain ⟨sz, hsz⟩ : ∃ sz, sz = stackSize cg.slot (routeLabels labels e.decl) := ⟨_, rfl⟩
   rw [← hF, ← hsizes, ← hband, ← hidx, ← hsz] at henv_eq
   rw [← hF, ← hsizes, ← hband] at hrsv
   rw [← hsizes] at hnn
   have hmem : sz ∈ sizes := by
     rw [hsizes, hsz]
     exact List.mem_map.mpr ⟨e, he0, rfl⟩
   have hnlen : (loopEdges cg.edges e.tail).length = n := by
     rw [hn, hsizes]
     exact (List.length_map _).symm
   have hidx : idx < n := by
     rw [hidx]
     have hmemd : e.decl ∈ (loopEdges cg.edges e.tail).map (·.decl) :=
      List.mem_map.mpr ⟨e, he0, rfl⟩
     have hlt := List.idxOf_lt_length_of_mem hmemd
     have hlen2 : ((loopEdges cg.edges e.tail).map (·.decl)).length = n :=
      (List.length_map _).trans hnlen
     rwa [hlen2] at hlt
   have hcount : 1 ≤ n := by omega
   have hband_nn : 0 ≤ band := by
     rw [hband]
     unfold Loops.band
     exact Int.le_trans (Int.mul_nonneg (by decide : (0 : Int) ≤ 2) hslot)
      (foldl_max_height_ge _ _)
   have hsz_band : sz.height ≤ band := by
     rw [hband]
     exact loopBand_ge_mem_aux _ _ _ hmem
   have hszw : ∀ s ∈ sizes, 0 ≤ s.width := fun s hs => (hnn s hs).1
   have hext := extent_ge_lane_width hslot hszw hmem (hn ▸ hcount)
   have hFirrel : frameRect P cg run e.tail = frameRect default cg run e.tail := rfl
   have hfp : loopFootprint cg run labels e.tail =
       ⟨F.x + F.w, F.y, Loops.extent cg.slot sizes, F.h⟩ := by
     rw [hF]
     have h1 : run.exact.contains e.tail = false := by simp [hexact]
     unfold loopFootprint
     simp only [h1, hFirrel, Bool.false_eq_true, ↓reduceIte]
     rw [← hsizes]
   have hpx : env.x = F.x + F.w + cg.slot * ((n : Int) + 1) := by
     rw [henv_eq]
     simp only [Loops.placement]
     rw [hnlen]
   have hpy : env.y = F.y + (idx : Int) * band + Int.fdiv band 2 -
       Int.fdiv sz.height 2 := by
     rw [henv_eq]
     simp only [Loops.placement]
   have hpw : env.w = sz.width := by
     rw [henv_eq]
     rfl
   have hph : env.h = sz.height := by
     rw [henv_eq]
     rfl
   have eband : Int.fdiv band 2 = band / 2 := fdiv2_ediv band
   have ehsz : Int.fdiv sz.height 2 = sz.height / 2 := fdiv2_ediv _
   have hA_nn : 0 ≤ (idx : Int) * band := Int.mul_nonneg (Int.natCast_nonneg _) hband_nn
   have hrow : (idx : Int) * band + band ≤ (n : Int) * band := by
     have h1 : ((idx : Int) + 1) * band ≤ (n : Int) * band :=
       Int.mul_le_mul_of_nonneg_right (by omega) hband_nn
     have h2 : ((idx : Int) + 1) * band = (idx : Int) * band + band := by
       rw [Int.add_mul, Int.one_mul]
     omega
   rw [← hn] at hrsv hext
   have hup : env.y + env.h ≤ F.y + F.h := by
     rw [hpy, hph, eband, ehsz]
     have hle : band / 2 - sz.height / 2 + sz.height ≤ band := by omega
     omega
   have hlo : F.y ≤ env.y := by
     rw [hpy, eband, ehsz]
     have hge : sz.height / 2 ≤ band / 2 := by omega
     omega
   have hleft : F.x + F.w ≤ env.x := by
     rw [hpx]
     have hpos : 0 ≤ cg.slot * ((n : Int) + 1) :=
       Int.mul_nonneg hslot (by omega)
     omega
   have hright : env.x + env.w ≤ F.x + F.w + Loops.extent cg.slot sizes := by
     rw [hpx, hpw]
     omega
   rw [hfp]
   unfold Rect.Contained
   refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
   · exact hleft
   · exact hright
   · exact hlo
   · exact hup


 /-! ## Loop separation (modulo the footprint residual) -/
 /-- Loop-footprint residual: the loop reservation holds and the footprint
 misses every in-scope real box. This is the loop-footprint phase: the
 reservation is the placement precondition and the separation is the
 footprint-level fact the flat clause-6 argument needs. -/
 def RunLocalLoopFootprint (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
   ∀ (execution : SceneExecution inp o res)
     (comp : List Nat) (candidate : Nat) (run : Run)
     (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
     comp ∈ components execution.graph →
     cg = componentCandidate execution.graph comp candidate →
     componentRun execution.params cg execution.measured orderOptions = .ok run →
     cg.edges[k]? = some e →
     e.tail = e.head →
     v < run.proper.nodes.length →
     RouteImpl.IsReal run.proper v →
     RouteImpl.nodeDecl run.proper v ∉
       ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
     RouteImpl.nodeDecl run.proper v ∉
       ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
     (loopSizes cg.edges execution.measured e.tail cg.slot).length *
         Loops.band cg.slot (loopSizes cg.edges execution.measured e.tail cg.slot) ≤
       (frameRect execution.params cg run e.tail).h ∧
     ¬ (loopFootprint cg run execution.measured e.tail).meetsInterior
         (RouteImpl.boxRect run.proper run.xs run.ys v)

 /-- Loop separation holds modulo the footprint residual: the envelope is
 contained in the footprint, which misses every in-scope box. -/
 theorem runLocalLoopSeparation :
     ∀ inp o res, RunLocalLoopFootprint inp o res → RunLocalLoopSeparation inp o res := by
   intro inp o res hres execution comp candidate run orderOptions cg k e env v
     hcomp hcg hrun hk hloop henv hv hreal _hscope₀ _hscope₁
   have hslot := componentRun_slot_nonneg hrun
   have hlab := execution.measured_nonneg
   have hexact := run_exact_nil hrun
   have henv_eq := loop_envelope_eq hloop hexact henv
   obtain ⟨hrsv, hsep⟩ := hres execution comp candidate run orderOptions cg k e v
     hcomp hcg hrun hk hloop hv hreal _hscope₀ _hscope₁
   have hcont := loop_envelope_contained hslot hlab hexact hk hloop henv_eq hrsv
   exact Elegant.Layered.not_meetsInterior_of_contained hcont hsep
 end Elegant.Layered.PipelineImpl

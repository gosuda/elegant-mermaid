import Elegant.Layered.RegionCrossCoordinateSeparation
import Elegant.Layered.RegionRunPlacementFacts
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem coordinateGraphR_plain_record (P : Params) (exact : List Nat)
    (s : RegionSpec) {p : Proper} {i : Nat} {source : Node}
    (hsource : p.nodes[i]? = some ⟨source, false, none, false⟩)
    (hplain : source.border = 0) :
    ∃ n, (coordinateGraphR P exact (some s) p).nodes[i]? = some n ∧
      n.node.border = 0 := by
  let sized := sizeProperPortsX P exact p
  let titled := titleReservationsR s.titles P.clusterPad sized
  have hkeys := sizeProperPortsX_key P exact p i
  change (sized.nodes[i]?).map _ = _ at hkeys
  cases hs : sized.nodes[i]? with
  | none => simp [hs, hsource] at hkeys
  | some n =>
    simp only [hs, hsource, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkeys
    have hb : n.node.border = 0 := hkeys.2.1.trans hplain
    have hd : n.dummy = false := hkeys.1
    have ht : titled.nodes[i]? = some n := by
      unfold titled titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by
        simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hs).1)]
      simp [List.getElem?_map, hs, hb]
    obtain ⟨_, hnodes, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    have hc : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[i]? =
        some n := by
      rw [clearProxyExtents_nodes, List.getElem?_map, hnodes,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1, ht]
      simp [clearF, hb]
    refine ⟨n, ?_, hb⟩
    change (materializeDummyPaths
      (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW))).nodes[i]? = some n
    simp [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx, hc, hd]

private theorem reservedPortsR_border_record {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs xs' : List Int} {p' : Proper}
    (h : reservedPortsR pl cg labels xs = .ok (xs', p'))
    {i : Nat} {n : ProperNode} (hn : pl.p.nodes[i]? = some n) :
    ∃ m, p'.nodes[i]? = some m ∧ m.node.border = n.node.border := by
  let step (acc : List Int × Array ProperNode) (q : RegionCluster × Nat) :
      Except LayoutError (List Int × Array ProperNode) := do
    let c := q.1
    let footprint := max c.titleH
      (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      pure (x, acc.2.set! c.top { top with node := { top.node with
        h := max (RouteImpl.nodeH pl.p c.top) footprint } })
  have preserve (entries : List (RegionCluster × Nat))
      (acc out : List Int × Array ProperNode)
      (hacc : ∃ m, acc.2[i]? = some m ∧ m.node.border = n.node.border)
      (hfold : entries.foldlM step acc = .ok out) :
      ∃ m, out.2[i]? = some m ∧ m.node.border = n.node.border := by
    induction entries generalizing acc with
    | nil =>
      change Except.ok acc = Except.ok out at hfold
      rw [← Except.ok.inj hfold]
      exact hacc
    | cons q rest ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨mid, hmid, hrest⟩ := bind_ok hfold
      apply ih mid ?_ hrest
      dsimp only [step] at hmid
      split at hmid
      · cases hmid
      · obtain ⟨_, _, hmid⟩ := bind_ok hmid
        obtain ⟨_, _, hmid⟩ := bind_ok hmid
        rw [← Except.ok.inj hmid]
        dsimp only
        obtain ⟨m, hm, hb⟩ := hacc
        rw [Array.set!_eq_setIfInBounds]
        by_cases he : q.1.top = i
        · have hlt := (Array.getElem?_eq_some_iff.mp hm).1
          have hget : acc.2.getD i default = m := by
            simp only [Array.getD_eq_getD_getElem?, hm, Option.getD_some]
          rw [he, Array.getElem?_setIfInBounds_self_of_lt hlt, hget]
          exact ⟨_, rfl, hb⟩
        · rw [Array.getElem?_setIfInBounds_ne he]
          exact ⟨m, hm, hb⟩
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = _ at h
  obtain ⟨out, hfold, hfinish⟩ := bind_ok h
  have he := Except.ok.inj hfinish
  have hp : p'.nodes = out.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) he).symm
  rw [hp, Array.getElem?_toList]
  exact preserve _ _ _ ⟨n, by rwa [List.getElem?_toArray], rfl⟩ hfold

private theorem crossCoordsR_placement_records {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)} {out : List Int × List (List Nat) × List (Option Int) × Proper}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok out) :
    1 ≤ min P.nodeGap P.clusterPad ∧
      ∀ {i : Nat} {n : ProperNode}, p.nodes[i]? = some n →
        ∃ m, out.2.2.2.nodes[i]? = some m ∧ m.node.border = n.node.border := by
  unfold crossCoordsR at h
  obtain ⟨_, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    cases h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, hcross, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
    obtain ⟨⟨_, placed⟩, hports, h⟩ := bind_ok h
    have hp : out.2.2.2 = placed :=
      (congrArg (fun q : List Int × List (List Nat) × List (Option Int) × Proper =>
        q.2.2.2) (Except.ok.inj h)).symm
    obtain ⟨hng, hcp, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
    refine ⟨Int.le_min.mpr ⟨hng, hcp⟩, ?_⟩
    intro i n hn
    rw [hp]
    exact reservedPortsR_border_record hports hn

/-- Successful some-spec runs have a positive cross-axis gap, and original plain
nodes retain their coordinate records and centres through proxy placement. -/
theorem componentRunR_region_plain_cross_geometry {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run)) :
    1 ≤ min P.nodeGap P.clusterPad ∧
      ∀ {i : Nat} {source : Node}, cg'.nodes[i]? = some source → source.border = 0 →
        ∃ n, run.coordinateProper.nodes[i]? = some n ∧ run.proper.nodes[i]? = some n ∧
          n.node.border = 0 ∧ run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
  obtain ⟨_, _, _, _, _, pCoord, _, _, _, _, placed, _, _, _, stages⟩ :=
    componentRunR_stages hrun
  have hplace : 1 ≤ min P.nodeGap P.clusterPad ∧
      ∀ {i : Nat} {n : ProperNode}, pCoord.nodes[i]? = some n →
        ∃ m, placed.nodes[i]? = some m ∧ m.node.border = n.node.border := by
    rcases stages.hPlaced with ⟨_, hcross, _, _, heq⟩ | ⟨_, _, _, _, hcross⟩
    · obtain ⟨hng, hcp, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
      refine ⟨Int.le_min.mpr ⟨hng, hcp⟩, ?_⟩
      intro i n hn
      rw [heq]
      exact ⟨n, hn, rfl⟩
    · exact crossCoordsR_placement_records hcross
  refine ⟨hplace.1, ?_⟩
  intro i source hsource hplain
  obtain ⟨n, hn, hnb⟩ := coordinateGraphR_plain_record P exact s
    (addLabelNodes_untouched_node stages.hLabels (normalize_node_record stages.hNorm hsource) rfl)
    hplain
  rw [stages.hCoord] at hn
  obtain ⟨m, hm, hmb⟩ := hplace.2 hn
  have hb := hmb.trans hnb
  have hnotProxy : ¬ (m.node.border = -2 ∨ m.node.border = 2) := by rw [hb]; decide
  have hproper := ((proxyWidths_rel stages.hProxy).2.2.2.2.2 i m hm hnotProxy).1
  have hcoord : run.coordinateProper.nodes[i]? = some m := by
    rw [stages.hCoordProper]
    exact hm
  refine ⟨m, hcoord, ?_, hb, componentRunR_placement_xsR hrun hcoord hnotProxy⟩
  rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
  exact hproper

private theorem plain_frame_cross_rect {P : Params} {cg : Graph} {run : Run}
    {i : Nat} {source : Node} {n : ProperNode} (hs : cg.nodes[i]? = some source)
    (hb : source.border = 0) (hn : run.proper.nodes[i]? = some n)
    (hx : run.xs.getD i 0 = run.coordinateXs.getD i 0) :
    frameRect P cg run i =
      ⟨run.coordinateXs.getD i 0 - Int.fdiv n.node.w 2, run.ys.getD i 0, n.node.w, n.node.h⟩ := by
  have hget : cg.nodes.getD i default = source := by
    simp only [List.getD_eq_getElem?_getD, hs, Option.getD_some]
  have hframe : frameRect P cg run i = nodeRect cg run i := by
    unfold frameRect
    simp only []
    rw [hget, hb]
    rfl
  rw [hframe, ← hx]
  simp [nodeRect, hn]

/-- Distinct original plain siblings in one executed region layer have disjoint
frame rectangles, in either order in the layer. -/
theorem componentRunR_region_same_layer_siblings_disjoint {P : Params} {exactIds : List String}
    {s : RegionSpec} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {labels : List MeasuredLabel} {graph0 graph cg' : Graph}
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hgraph : exactGraph P exactIds inp o labels graph0 = .ok graph)
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) graph comp candidate) labels orderOptions = .ok (cg', run))
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {u v keyU keyV : Nat} {nu nv : Node} {bu bv : ModelBox}
    (hu : u ∈ layer) (hv : v ∈ layer) (hne : u ≠ v)
    (hpartU : comp[u]? = some keyU) (hpartV : comp[v]? = some keyV)
    (hnu : graph.nodes[keyU]? = some nu) (hnv : graph.nodes[keyV]? = some nv)
    (hboxU : inp.boxes[keyU]? = some bu) (hboxV : inp.boxes[keyV]? = some bv)
    (hplainU : nu.border = 0) (hplainV : nv.border = 0) (hparent : bu.parent = bv.parent) :
    Disjoint (frameRect P cg' run u) (frameRect P cg' run v) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  have hnodes : cg'.nodes = (componentCandidateR (some s) graph comp candidate).nodes := by
    rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, hrank⟩
    · rw [he]
    · exact rankEquivalentR_nodes_eq hrank
  have hnu' : cg'.nodes[u]? = some nu := by
    rw [hnodes]
    exact component_node_lookupR hpartU hnu
  have hnv' : cg'.nodes[v]? = some nv := by
    rw [hnodes]
    exact component_node_lookupR hpartV hnv
  obtain ⟨hgap, hrecords⟩ := componentRunR_region_plain_cross_geometry hrun
  obtain ⟨mU, hcU, hpU, _, hxU⟩ := hrecords hnu' hplainU
  obtain ⟨mV, hcV, hpV, _, hxV⟩ := hrecords hnv' hplainV
  have hwU : mU.node.w ≤ CoordsImpl.nodeW run.coordinateProper u := by
    simpa only [hcU] using CoordsImpl.nodeW_ge_width run.coordinateProper u
  have hwV : mV.node.w ≤ CoordsImpl.nodeW run.coordinateProper v := by
    simpa only [hcV] using CoordsImpl.nodeW_ge_width run.coordinateProper v
  have half (w : Int) : Int.fdiv w 2 = w / 2 := Int.fdiv_eq_ediv_of_nonneg w (by decide)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
  have hnePos : i ≠ j := by
    intro he
    rw [he] at hi
    exact hne (Option.some.inj (hi.symm.trans hj))
  rw [plain_frame_cross_rect hnu' hplainU hpU hxU, plain_frame_cross_rect hnv' hplainV hpV hxV]
  unfold Disjoint Rect.meetsInterior
  dsimp only
  simp only [half]
  rcases Nat.lt_or_gt_of_ne hnePos with hlt | hgt
  · have hsep := componentRunR_region_sibling_order h0 hgraph hrun hlayer hlt hi hj
      hpartU hpartV hnu hnv hboxU hboxV hplainU hplainV hparent
    simp only [CoordsImpl.coordSep, half] at hsep
    omega
  · have hsep := componentRunR_region_sibling_order h0 hgraph hrun hlayer hgt hj hi
      hpartV hpartU hnv hnu hboxV hboxU hplainV hplainU hparent.symm
    simp only [CoordsImpl.coordSep, half] at hsep
    omega

end Elegant.Layered.PipelineImpl

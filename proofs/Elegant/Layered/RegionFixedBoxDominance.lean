import Elegant.Layered.RegionFallbackStructuralProof
import Elegant.Layered.SizingFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem fixedGraphNodeR {exactIds : List String} {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph} {i : Nat} {ls : List Measure.Line} {source : ModelBox}
    {entry : String × Size} (hg0 : measuredGraph P inp o lines = .ok graph0)
    (hg : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hline : lines[i]? = some ls) (hs : inp.boxes[i]? = some source)
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == source.id) = some entry) :
    ∃ node, graph.nodes[i]? = some node ∧ node.border = 0 ∧
      (match o.direction with | .TB | .BT => entry.2.w | .LR | .RL => entry.2.h) ≤ node.w ∧
      (match o.direction with | .TB | .BT => entry.2.h | .LR | .RL => entry.2.w) ≤ node.h := by
  obtain ⟨before, hbefore, hdecl, hb, hw, hh⟩ :=
    measuredGraph_fixed_node_dims hg0 hline hs hfixed
  unfold exactGraph at hg
  obtain ⟨nodes, hnodes, hresult⟩ := bind_ok hg
  have hgNodes : graph.nodes = nodes :=
    (congrArg Graph.nodes (Except.ok.inj hresult)).symm
  obtain ⟨_, hat⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨node, hstep, hnode⟩ := hat i before hbefore
  rw [← hgNodes] at hnode
  have hsrc : inp.boxes[before.decl]? = some source := by rwa [hdecl]
  simp only [hsrc] at hstep
  split at hstep
  · simp only [pure, Except.pure] at hstep
    obtain rfl := Except.ok.inj hstep
    refine ⟨before, hnode, hb, ?_⟩
    cases hd : o.direction <;> simp only [hd] at hw hh ⊢ <;> exact ⟨hw, hh⟩
  · simp only [hfixed] at hstep
    split at hstep
    · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hstep
      cases hstep
    · split at hstep
      · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hstep
        cases hstep
      · simp only [pure, Except.pure] at hstep
        obtain rfl := Except.ok.inj hstep
        refine ⟨_, hnode, ?_⟩
        cases hd : o.direction <;> exact ⟨hb, Int.le_refl _, Int.le_refl _⟩

theorem regionCoordinatePlainDims (P : Params) (exact : List Nat)
    (spec : Option RegionSpec) {p : Proper} {i : Nat} {node : ProperNode}
    (hn : p.nodes[i]? = some node) (hb : node.node.border = 0) :
    ∃ nd, (coordinateGraphR P exact spec p).nodes[i]? = some nd ∧
      nd.node.border = 0 ∧ node.node.w ≤ nd.node.w ∧ node.node.h = nd.node.h := by
  let sized := sizeProperPortsX P exact p
  obtain ⟨nd, hs, hborder, hw, hh⟩ : ∃ nd, sized.nodes[i]? = some nd ∧
      nd.node.border = 0 ∧ node.node.w ≤ nd.node.w ∧ node.node.h = nd.node.h := by
    simp only [sized, sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx,
      hn, Option.map_some, Nat.zero_add]
    split
    · exact ⟨node, rfl, hb, Int.le_refl _, rfl⟩
    · exact ⟨_, rfl, hb, Int.le_max_left _ _, rfl⟩
  let titled := match spec with
    | none => titleReservations sized
    | some s => titleReservationsR s.titles P.clusterPad sized
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have ht : titled.nodes[i]? = some nd := by
    cases spec with
    | none =>
      change (titleReservations sized).nodes[i]? = some nd
      rw [titleReservations_nodes, List.getElem?_append_left (by
        simpa only [List.length_map] using hi)]
      simp [List.getElem?_map, hs, titleF, hborder]
    | some s =>
      change (titleReservationsR s.titles P.clusterPad sized).nodes[i]? = some nd
      unfold titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by simpa only [List.length_map] using hi)]
      simp [List.getElem?_map, hs, hborder]
  obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  have hadd : (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes[i]? = some nd := by
    rw [hnodes, List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1]
    exact ht
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[i]? =
      some nd := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hadd, clearF, hborder]
  have hcoord : coordinateGraphR P exact spec p =
      materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)) := by
    cases spec <;> rfl
  rw [hcoord]
  simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx, hclear,
    Option.map_some, Nat.zero_add]
  split <;> exact ⟨_, rfl, hborder, hw, hh⟩

private theorem regionPortDims {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {x x' : List Int} {out : Proper} {i : Nat}
    {nd : ProperNode} (h : reservedPortsR pl cg labels x = .ok (x', out))
    (hn : pl.p.nodes[i]? = some nd) :
    ∃ n, out.nodes[i]? = some n ∧ n.node.border = nd.node.border ∧
      n.node.w = nd.node.w ∧ nd.node.h ≤ n.node.h := by
  unfold reservedPortsR at h
  obtain ⟨result, hfold, hdone⟩ := bind_ok h
  let step : (List Int × Array ProperNode) → (RegionCluster × Nat) →
      Except LayoutError (List Int × Array ProperNode) := fun acc q => do
    let c := q.1
    let footprint := max c.titleH
      (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      let nodes := acc.2.set! c.top
        { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
      pure (x, nodes)
  let keeps (acc : List Int × Array ProperNode) : Prop :=
    ∃ n, acc.2[i]? = some n ∧ n.node.border = nd.node.border ∧
      n.node.w = nd.node.w ∧ nd.node.h ≤ n.node.h
  have foldKeeps : ∀ (rows : List (RegionCluster × Nat)) (start finish : List Int × Array ProperNode),
      rows.foldlM step start = .ok finish → keeps start → keeps finish := by
    intro rows
    induction rows with
    | nil =>
      intro start finish hnil hkeep
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hnil
      rwa [← hnil]
    | cons q rest ih =>
      intro start finish hcons hkeep
      simp only [List.foldlM_cons] at hcons
      obtain ⟨next, hnext, hrest⟩ := bind_ok hcons
      apply ih next finish hrest
      obtain ⟨cur, hcur, hb, hw, hh⟩ := hkeep
      dsimp only [step] at hnext
      split at hnext
      · simp [throw, throwThe, MonadExceptOf.throw] at hnext
      · obtain ⟨_, _, hnext⟩ := bind_ok hnext
        obtain ⟨_, _, hnext⟩ := bind_ok hnext
        rw [← Except.ok.inj hnext]
        change ∃ n, (start.2.set! q.1.top _)[i]? = some n ∧
          n.node.border = nd.node.border ∧ n.node.w = nd.node.w ∧ nd.node.h ≤ n.node.h
        by_cases heq : q.1.top = i
        · have hbound := (Array.getElem?_eq_some_iff.mp hcur).1
          have hread : start.2.getD i default = cur := by
            rw [Array.getD_eq_getD_getElem?, hcur, Option.getD_some]
          let footprint := max q.1.titleH
            (Loops.requiredHeight cg.slot (loopSizes cg.edges labels q.1.node cg.slot))
          refine ⟨{ cur with node := { cur.node with h := max nd.node.h footprint } },
            ?_, hb, hw, Int.le_max_left _ _⟩
          rw [heq, getElem?_set!_self hbound, hread, RouteImpl.nodeH, hn]
        · exact ⟨cur, (getElem?_set!_ne heq _).trans hcur, hb, hw, hh⟩
  have hbase : keeps (x, pl.p.nodes.toArray) := by
    exact ⟨nd, by simpa only [List.getElem?_toArray] using hn, rfl, rfl, Int.le_refl _⟩
  have hnodes : out.nodes = result.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hdone)).symm
  obtain ⟨n, hget, hb, hw, hh⟩ := foldKeeps _ _ _ hfold hbase
  exact ⟨n, by rw [hnodes, Array.getElem?_toList]; exact hget, hb, hw, hh⟩

theorem regionCrossPlainDims {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {m : RegionConstraints}
    {layers layers' : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    {i : Nat} {nd : ProperNode}
    (h : crossCoordsR P rm cg labels p m layers = .ok (xs, layers', reserved, placed))
    (hn : p.nodes[i]? = some nd) :
    ∃ n, placed.nodes[i]? = some n ∧ n.node.border = nd.node.border ∧
      n.node.w = nd.node.w ∧ nd.node.h ≤ n.node.h := by
  unfold crossCoordsR at h
  obtain ⟨_, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    exact absurd h (by simp)
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨xp, hxp, h⟩ := bind_ok h
    have hp : placed = xp.2 :=
      (congrArg (fun q : List Int × List (List Nat) × List (Option Int) × Proper => q.2.2.2)
        (Except.ok.inj h)).symm
    rw [hp]
    cases xp with
    | mk x out => exact regionPortDims hxp hn

theorem regionRunFrameDims {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg final : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {i : Nat} {node : Node}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (final, run))
    (hn : cg.nodes[i]? = some node) (hb : node.border = 0) :
    node.w ≤ (frameRect P final run i).w ∧ node.h ≤ (frameRect P final run i).h := by
  obtain ⟨rs, ranks, _, p0, labeled, pCoord, _, _, _, _, placed, q0, _, _, _, hRank,
    hNorm, hLabels, hCoord, _, _, _, hPlaced, hProxy, hDrop, _, _, _, _, _, _, _, _, _, _⟩ :=
    componentRunR_specR h
  have hnodes : final.nodes = cg.nodes := by
    rcases hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, hr⟩
    · rw [he]
    · exact rankEquivalentR_nodes_eq hr
  have hfinal : final.nodes[i]? = some node := by rwa [hnodes]
  have hlabel := addLabelNodes_untouched_node hLabels (normalize_node_record hNorm hfinal) rfl
  obtain ⟨nd, hnd, hborder, hwidth, hheight⟩ := regionCoordinatePlainDims P exact spec hlabel hb
  rw [hCoord] at hnd
  obtain ⟨out, hout, hbout, hwout, hhout⟩ : ∃ out, placed.nodes[i]? = some out ∧
      out.node.border = nd.node.border ∧ out.node.w = nd.node.w ∧ nd.node.h ≤ out.node.h := by
    rcases hPlaced with ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, hc⟩
    · exact ⟨nd, he.symm ▸ hnd, rfl, rfl, Int.le_refl _⟩
    · exact regionCrossPlainDims hc hnd
  have hbout' : out.node.border = 0 := hbout.trans hborder
  have hproper : run.proper.nodes[i]? = some out := by
    rw [← hDrop, OrderImpl.dropSynthetic_nodes]
    exact proxyWidths_plain_node hProxy hout hbout'
  have hplain : (final.nodes.getD i default).border ≠ -2 := by
    simp only [List.getD_eq_getElem?_getD, hfinal, Option.getD_some, hb]
    decide
  obtain ⟨hfw, hfh⟩ := frameRect_plain_dims P final run i out hplain hproper
  change node.w ≤ nd.node.w at hwidth
  change node.h = nd.node.h at hheight
  rw [hfw, hwout, hfh, hheight]
  exact ⟨hwidth, hhout⟩

/-- Every successful regional leaf run honors the first fixed-size entry at each
    declaration, including group frames, without a well-formedness premise. -/
theorem R_fixedBoxDominates_holds (exactIds : List String)
    (idSets : List (String × List String)) : R_FixedBoxDominates exactIds idSets := by
  intro inp o res execution i box source entry hbox hsource hfixed
  have hi := (List.getElem?_eq_some_iff.mp hsource).1
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  obtain ⟨_, hlookup⟩ := mapM_getElem? _ _ _ hlines
  obtain ⟨ls, _, hline⟩ := hlookup i (source, i)
    (by simp only [List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add])
  obtain ⟨node, hnode, hb, hw, hh⟩ := fixedGraphNodeR execution.graph0_eq
    execution.graph_eq hline hsource hfixed
  obtain ⟨part, pos, k, _, hpart, hpos⟩ := key_part_positionR execution hi
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, hpacked, _⟩ := bind_ok hpack
  have hk : k < packed.boxes.length := by
    rw [Pack.pack_count hpacked, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hpart).1
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? =
      some (part, packed.boxes[k]) :=
    List.getElem?_zip_eq_some.mpr ⟨hpart, List.getElem?_eq_getElem hk⟩
  have hindex : i < execution.componentsAcc.rects.size := by
    rwa [execution.components_rects_sizeR]
  obtain ⟨index, cg, run, loops, _, spec, hrun, _, _, hrect⟩ :=
    actual_components_packed_frame_sourceR (by rfl) execution.components_eq
      execution.packed_eq packed hpacked hselected hpos hindex default
  have hcand : (componentCandidateR spec execution.graph part.1 index).nodes =
      part.1.map (fun key => execution.graph.nodes.getD key default) := by
    cases spec with
    | none => exact componentCandidate_nodes _ _ _
    | some _ => rfl
  have hlocal : (componentCandidateR spec execution.graph part.1 index).nodes[pos]? = some node := by
    rw [hcand]
    simp only [List.getElem?_map, hpos, Option.map_some, List.getD_eq_getElem?_getD, hnode,
      Option.getD_some]
  obtain ⟨hwframe, hhframe⟩ := regionRunFrameDims hrun hlocal hb
  rw [execution.boxes_eq_mapR, List.getElem?_map, List.getElem?_zipIdx] at hbox
  simp only [hsource, Option.map_some, Option.some.injEq, Nat.zero_add] at hbox
  dsimp only at hrect
  rw [← hbox, hrect]
  have hfWidth := Int.le_trans hw hwframe
  have hfHeight := Int.le_trans hh hhframe
  cases hd : o.direction <;>
    simp only [hd, orientRect, shiftRect] at hfWidth hfHeight ⊢ <;>
    first | exact ⟨hfWidth, hfHeight⟩ | exact ⟨hfHeight, hfWidth⟩

end Elegant.Layered.PipelineImpl

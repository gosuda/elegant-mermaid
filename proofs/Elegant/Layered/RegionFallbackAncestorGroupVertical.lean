import Elegant.Layered.RegionFallbackAncestorRanks
import Elegant.Layered.RegionC5ContributorRank
import Elegant.Layered.RegionC8aGroupPlain

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem regionBandLayersOk {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    RouteImpl.layersOk run.proper run.layers = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs⟩ := componentRunR_stages hrun
  rcases hs.hLanes with ⟨_, h⟩ | ⟨_, h⟩
  · exact (RouteImpl.routeWithLanes_geometry h).1
  · obtain ⟨base, hbase, _, _⟩ := routeWithLanesR_spec h
    exact (RouteImpl.route_spec hbase).1

private theorem coordinateBottomOrigin {P : Params} {exact : List Nat} {spec : RegionSpec}
    {labeled : Proper} {v : Nat} {n : ProperNode}
    (hn : (coordinateGraphR P exact (some spec) labeled).nodes[v]? = some n)
    (hb : n.node.border = 2) : ∃ src, labeled.nodes[v]? = some src ∧ src.node.border = 2 := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR spec.titles P.clusterPad sized
  change (materializeDummyPaths (clearProxyExtents
    (OrderImpl.addClusterBorders titled P.clusterBorderW))).nodes[v]? = some n at hn
  obtain ⟨cleared, hc, _, hborder, _, _⟩ := materialize_lookup _ hn
  rw [clearProxyExtents_nodes, List.getElem?_map] at hc
  obtain ⟨pre, hpre, rfl⟩ := Option.map_eq_some_iff.mp hc
  have hp : pre.node.border = 2 := (clearF_keys pre).2.1.symm.trans (hborder.symm.trans hb)
  obtain ⟨extra, hnodes, hmarkers⟩ := addClusterBorders_extra titled P.clusterBorderW
  rw [hnodes] at hpre
  by_cases hvt : v < titled.nodes.length
  · rw [List.getElem?_append_left hvt] at hpre
    let copy (q : ProperNode × Nat) : ProperNode :=
      let height := (spec.titles.getD q.1.node.decl (0, 0)).2 + P.clusterPad
      { q.1 with node := { q.1.node with border := 3, loopExtent := 0, h := height } }
    have ht : titled.nodes = sized.nodes.map titleF ++
        (sized.nodes.zipIdx.filter fun q => q.1.node.border == -2).map copy := rfl
    rw [ht] at hpre
    by_cases hvs : v < sized.nodes.length
    · rw [List.getElem?_append_left (by simpa only [List.length_map] using hvs),
        List.getElem?_map] at hpre
      obtain ⟨sz, hsz, rfl⟩ := Option.map_eq_some_iff.mp hpre
      obtain ⟨src, hsrc, _, hsrcBorder, _⟩ := X_sizeProperPorts_node_origin P exact labeled hsz
      exact ⟨src, hsrc, hsrcBorder.symm.trans ((titleF_keys sz).2.1.symm.trans hp)⟩
    · rw [List.getElem?_append_right (by simpa only [List.length_map] using Nat.le_of_not_gt hvs),
        List.getElem?_map] at hpre
      obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hpre
      have htag : (3 : Int) = 2 :=
        (congrArg (fun m : ProperNode => m.node.border) he).trans hp
      cases htag
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hvt)] at hpre
    have hs := (hmarkers pre (List.mem_of_getElem? hpre)).2
    omega

private theorem regionBandTopNonneg {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run))
    {r : Nat} (hr : r < run.layers.length) : 0 ≤ run.top.getD r 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, _, ⟨_, top⟩, ysMid, st⟩ :=
    componentRunR_stages hrun
  have hrTop : r < top.length := by rw [(CoordsImpl.rankCoordsWith_length st.hYt).2]; exact hr
  obtain ⟨extra, shifts, _, hExtra, hprefix, _, htop, _⟩ :=
    (runHooksShift_exact P exactIds inp cg' labels).shifts placed run.layers ysMid top
      run.ys run.top st.hReserve
  have prefixNonneg (es : List Int) (a : Int) (out : List Int)
      (ha : 0 ≤ a) (hOut : ∀ x ∈ out, 0 ≤ x) (he : ∀ x ∈ es, 0 ≤ x) :
      ∀ x ∈ (es.foldl (fun acc x => (acc.1 + x, acc.2 ++ [acc.1])) (a, out)).2,
        0 ≤ x := by
    induction es generalizing a out with
    | nil => exact hOut
    | cons x xs ih =>
      simp only [List.foldl_cons]
      refine ih _ _ (Int.add_nonneg ha (he x List.mem_cons_self)) ?_ ?_
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hOut y hy
        · simpa only [List.mem_singleton.mp hy] using ha
      · exact fun y hy => he y (List.mem_cons_of_mem _ hy)
  have hShift : 0 ≤ shifts.getD r 0 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : shifts[r]? with
    | none => exact Int.le_refl _
    | some x =>
      have hx := List.mem_of_getElem? h
      rw [hprefix] at hx
      exact prefixNonneg extra 0 [] (Int.le_refl _) (by simp) hExtra x hx
  obtain ⟨hg, hslot, _, hgaps, _, htopEq, _⟩ := CoordsImpl.rankCoordsWith_spec st.hYt
  have hHeights : ∀ x ∈ run.layers.map (CoordsImpl.layerHeight placed), 0 ≤ x := by
    intro x hx
    obtain ⟨layer, _, rfl⟩ := List.mem_map.mp hx
    exact CoordsImpl.layerHeight_nonneg placed layer
  have hSteps := CoordsImpl.rankSteps_nonneg
    (show 0 ≤ P.rankGap by omega) (show 0 ≤ P.slot by omega)
    placed run.layers (run.lanes.routing.gaps.map (·.slots)) hgaps
  have hBase : 0 ≤ top.getD r 0 := by
    rw [htopEq, List.getD_eq_getElem?_getD]
    cases h : (CoordsImpl.topsFrom 0 1 0
        (run.layers.map (CoordsImpl.layerHeight placed))
        (CoordsImpl.rankSteps P.rankGap P.slot placed run.layers
          (run.lanes.routing.gaps.map (·.slots))))[r]? with
    | none => exact Int.le_refl _
    | some x =>
      exact CoordsImpl.topsFrom_ge 0 1 (Int.le_refl 0) (by decide)
        _ _ _ hHeights hSteps x (List.mem_of_getElem? h)
  rw [htop r hrTop]
  exact Int.add_nonneg hBase hShift

private theorem activeContributorBand {P : Params} {exactIds : List String} {spec : RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P (exactDecls exactIds inp) (some spec) inp cg labels orderOptions =
      .ok (cg', run))
    (hactive : newComponentRegions (some spec) P inp cg = .ok (some rm))
    {v : Nat} {node : ProperNode} (hn : run.proper.nodes[v]? = some node) :
    ∃ layer, run.layers[(rk run.proper.rank v).toNat]? = some layer ∧
      0 ≤ rk run.proper.rank v ∧
      run.top.getD (rk run.proper.rank v).toNat 0 ≤ run.ys.getD v 0 ∧
      run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤
        run.top.getD (rk run.proper.rank v).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper layer := by
  obtain ⟨_, _, labeled, p, _, _, _, _, _, hnorm, hlabels, hcoord, _, _, ⟨alloc⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, q0, _, _, hs⟩ := componentRunR_stages hrun
  have hfinalNodes : run.proper.nodes = q0.nodes := by rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes]
  have ports := groupPlain_reservedPorts_record alloc.hFramesAndPorts
  have hlen : run.proper.nodes.length = alloc.placement.p.nodes.length := by
    rw [hfinalNodes, (proxyWidths_rel hs.hProxy).2.2.1, ← hs.hCoordProper]
    exact ports.1
  have hv := (List.getElem?_eq_some_iff.mp hn).1
  have hvp : v < alloc.placement.p.nodes.length := by rwa [← hlen]
  let source := alloc.placement.p.nodes[v]
  have hsource : alloc.placement.p.nodes[v]? = some source := List.getElem?_eq_getElem hvp
  obtain ⟨coord, hc, hkind, _⟩ := ports.2 hsource
  have hbflat (hb : coord.node.border = 2) : coord.node.h = 0 := by
    have hsource' : p.nodes[v]? = some source := by
      simpa only [alloc.hPlacement] using hsource
    rw [← hcoord] at hsource'
    obtain ⟨original, horiginal, hborder⟩ := coordinateBottomOrigin hsource' (hkind.symm.trans hb)
    rcases addLabelNodes_keys _ _ _ (normalize_keys hnorm) hlabels v original horiginal with
      ⟨candidate, hcandidate, _, hcb, _⟩ | ⟨_, hzero, _⟩
    · have hcb' : candidate.border = 2 := hcb.symm.trans hborder
      obtain ⟨actualCoord, _, hcoordAt, _, _, _, _, _, _, _, hz⟩ :=
        componentRunR_active_marker_records hrun hactive hcandidate (Or.inr hcb')
      have he : actualCoord = coord := Option.some.inj (hcoordAt.symm.trans hc)
      exact he ▸ (hz hcb').1
    · omega
  have hcoverage := (RouteImpl.layersOk_spec (regionBandLayersOk hrun)).2.2.2.1
  obtain ⟨layer, hl, _, hnonneg⟩ := hcoverage v hv
  have hlD : run.layers.getD (rk run.proper.rank v).toNat [] = layer := by
    rw [List.getD_eq_getElem?_getD, hl, Option.getD_some]
  have hb := (componentRunR_boundaryRankBands hrun).1 hc hbflat
  refine ⟨layer, hl, hnonneg, hb.1, ?_⟩
  have h := hb.2.1
  change run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤
    run.top.getD (rk run.proper.rank v).toNat 0 +
      CoordsImpl.layerHeight run.coordinateProper (run.layers.getD (rk run.proper.rank v).toNat []) at h
  simpa only [hlD] using h

private theorem frameMemberRectMem {cg : Graph} {run : Run} {decl v : Nat}
    {nd : ProperNode} (hn : run.proper.nodes[v]? = some nd)
    (hpath : nd.node.clusterPath.contains decl = true) :
    Labels.rectAt run.proper run.xs run.ys v ∈ groupMemberRects cg run decl := by
  apply List.mem_filterMap.mpr
  exact ⟨(nd, v), List.mem_zipIdx_iff_getElem?.mpr hn, by simp only [hpath, ↓reduceIte]⟩

/-- The active child group's entire emitted member hull, including dummy,
side and title contributors, is inside the parent with strict rank-axis margins. -/
theorem regionActiveChildGroup_strictVertical
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {s : RegionSpec} {index : Nat} {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) e.graph comp index) e.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) e.params inp
      (componentCandidateR (some s) e.graph comp index) = .ok (some rm))
    {u v : Nat} {parent child : Node}
    (hu : cg.nodes[u]? = some parent) (hp : parent.border = -2)
    (hv : cg.nodes[v]? = some child) (hc : child.border = -2)
    (hstep : child.clusterPath.dropLast = parent.clusterPath)
    (hparentPath : parent.clusterPath.contains parent.decl = true)
    (hchildPath : child.clusterPath.contains child.decl = true) :
    (frameRect e.params cg run u).y < (frameRect e.params cg run v).y ∧
    (frameRect e.params cg run v).y + (frameRect e.params cg run v).h <
      (frameRect e.params cg run u).y + (frameRect e.params cg run u).h := by
  let cand := componentCandidateR (some s) e.graph comp index
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes : cg.nodes = cand.nodes := rankEquivalentR_nodes_eq hrank
  obtain ⟨pb, pn, hpb, hpbKind, hpbDecl, hpbPath, hpbUniq, _⟩ :=
    activeCandidateOriginalFrameRankWindow e hwf hfp hcomp hrun hactive hu hp
  obtain ⟨cb, cn, hcb, hcbKind, hcbDecl, _, hcbUniq, hcWindow⟩ :=
    activeCandidateOriginalFrameRankWindow e hwf hfp hcomp hrun hactive hv hc
  have bottomFind {b decl : Nat} {bot : Node}
      (hbot : cg.nodes[b]? = some bot) (hb : bot.border = 2) (hd : bot.decl = decl)
      (huniq : ∀ {i : Nat} {m : Node}, cg.nodes[i]? = some m →
        m.border = 2 → m.decl = decl → i = b) :
      (cand.nodes.zipIdx.find? fun q => q.1.border == 2 && q.1.decl == decl) = some (bot, b) := by
    rw [← hnodes]
    have hbMem : (bot, b) ∈ cg.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hbot
    have hfind : (cg.nodes.zipIdx.find? fun q => q.1.border == 2 && q.1.decl == decl).isSome = true :=
      List.find?_isSome.mpr ⟨(bot, b), hbMem, by simp [hb, hd]⟩
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hfind
    have hlookup := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hq)
    have hkeys : q.1.border = 2 ∧ q.1.decl = decl := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hq
    have hi := huniq hlookup hkeys.1 hkeys.2
    have hlookup' : cg.nodes[b]? = some q.1 := by simpa only [hi] using hlookup
    have he : q.1 = bot := Option.some.inj (hlookup'.symm.trans hbot)
    rw [hq]
    exact congrArg some (Prod.ext he hi)
  have hu' : cand.nodes[u]? = some parent := by rwa [← hnodes]
  have hv' : cand.nodes[v]? = some child := by rwa [← hnodes]
  obtain ⟨htRank, hbRank⟩ := componentRunR_compound_child_strictRankWindow hrun
    (parent := (parent, u)) (child := (child, v))
    (List.mem_zipIdx_iff_getElem?.mpr hu') hp (bottomFind hpb hpbKind hpbDecl hpbUniq)
    (List.mem_zipIdx_iff_getElem?.mpr hv') hc hstep (bottomFind hcb hcbKind hcbDecl hcbUniq)
  change rk run.proper.rank u < rk run.proper.rank v at htRank
  change rk run.proper.rank cb < rk run.proper.rank pb at hbRank
  obtain ⟨_, pt, hptCoord, hpt, _, _, hptBorder, _, _, hptPath, _⟩ :=
    componentRunR_active_marker_records hrun hactive hu (Or.inl hp)
  obtain ⟨_, pbot, hpbCoord, hpbot, _, _, hpbBorder, _, _, hpbotPath, hpbotZero⟩ :=
    componentRunR_active_marker_records hrun hactive hpb (Or.inr hpbKind)
  obtain ⟨_, _, _, hct, _, _, _, _, _, hctPath, _⟩ :=
    componentRunR_active_marker_records hrun hactive hv (Or.inl hc)
  have hptMem := frameMemberRectMem (cg := cg) hpt (by rw [hptPath]; exact hparentPath)
  have hpbMem := frameMemberRectMem (cg := cg) hpbot
    (by rw [hpbotPath, hpbPath]; exact hparentPath)
  have hctMem := frameMemberRectMem (cg := cg) hct (by rw [hctPath]; exact hchildPath)
  let r := fun j : Nat => (rk run.proper.rank j).toNat
  obtain ⟨topLayer, hTopL, hTopNN, _, _⟩ := activeContributorBand hrun hactive hpt
  obtain ⟨botLayer, hBotL, _, _, _⟩ := activeContributorBand hrun hactive hpbot
  obtain ⟨childTopLayer, hChildTopL, hChildTopNN, _, _⟩ := activeContributorBand hrun hactive hct
  change run.layers[r u]? = some topLayer at hTopL
  change run.layers[r pb]? = some botLayer at hBotL
  change run.layers[r v]? = some childTopLayer at hChildTopL
  have hTopY := ((componentRunR_boundaryRankBands hrun).1 hptCoord
    (by rw [hptBorder, hp]; omega)).2.2.1 (hptBorder.trans hp)
  have hBotY := ((componentRunR_boundaryRankBands hrun).1 hpbCoord
    (fun _ => (hpbotZero hpbKind).1)).2.2.2 (hpbBorder.trans hpbKind)
  change run.ys.getD u 0 = run.top.getD (r u) 0 at hTopY
  change run.ys.getD pb 0 = run.top.getD (r pb) 0 +
    CoordsImpl.layerHeight run.coordinateProper (run.layers.getD (r pb) []) at hBotY
  have hbotL : run.layers.getD (r pb) [] = botLayer := by
    rw [List.getD_eq_getElem?_getD, hBotL, Option.getD_some]
  rw [hbotL] at hBotY
  have hAll (rect : Rect) (hm : rect ∈ groupMemberRects cg run child.decl) :
      run.ys.getD u 0 + 1 ≤ rect.y ∧ rect.y + rect.h ≤ run.ys.getD pb 0 - 1 := by
    unfold groupMemberRects at hm
    obtain ⟨q, hq, hrect⟩ := List.mem_filterMap.mp hm
    split at hrect
    · rename_i howner
      rw [← Option.some.inj hrect, rectAt_eq_box]
      have hqGet := List.mem_zipIdx_iff_getElem?.mp hq
      obtain ⟨a, b, _, _, ha, hb, hpa, hpbOwner, hqa, hqb⟩ :=
        activeFrameContributorRankSources e hcomp hrun hactive hqGet howner
      have hqTop := Int.lt_of_lt_of_le htRank (Int.le_trans (hcWindow ha hpa).1 hqa)
      have hqBot := Int.lt_of_le_of_lt (Int.le_trans hqb (hcWindow hb hpbOwner).2) hbRank
      obtain ⟨layer, hLayer, hNN, hlow, hhigh⟩ := activeContributorBand hrun hactive hqGet
      change run.layers[r q.2]? = some layer at hLayer
      change run.top.getD (r q.2) 0 ≤ run.ys.getD q.2 0 at hlow
      change run.ys.getD q.2 0 + RouteImpl.nodeH run.proper q.2 ≤
        run.top.getD (r q.2) 0 + CoordsImpl.layerHeight run.coordinateProper layer at hhigh
      have hLoRank : r u < r q.2 :=
        (Int.toNat_lt_toNat (Int.lt_of_le_of_lt hTopNN hqTop)).mpr hqTop
      have hHiRank : r q.2 < r pb :=
        (Int.toNat_lt_toNat (Int.lt_of_le_of_lt hNN hqBot)).mpr hqBot
      have hLo := componentRunR_strictRankBandGap hrun hLoRank hTopL hLayer
      have hHi := componentRunR_strictRankBandGap hrun hHiRank hLayer hBotL
      have hTopHeight := CoordsImpl.layerHeight_nonneg run.coordinateProper topLayer
      have hBotHeight := CoordsImpl.layerHeight_nonneg run.coordinateProper botLayer
      change run.ys.getD u 0 + 1 ≤ run.ys.getD q.2 0 ∧
        run.ys.getD q.2 0 + RouteImpl.nodeH run.proper q.2 ≤ run.ys.getD pb 0 - 1
      exact ⟨by omega, by omega⟩
    · cases hrect
  have hChildNonempty : groupMemberRects cg run child.decl ≠ [] := by
    intro he
    rw [he] at hctMem
    cases hctMem
  have hChildLo := boundsOf_minY_ge_of_all hChildNonempty (fun rect hm => (hAll rect hm).1)
  have hChildUpperNonneg : 0 ≤ run.ys.getD pb 0 - 1 := by
    have hbefore : r v < r pb := by
      have hRank := Int.lt_of_le_of_lt (hcWindow hv hchildPath).2 hbRank
      exact (Int.toNat_lt_toNat (Int.lt_of_le_of_lt hChildTopNN hRank)).mpr hRank
    have hgap := componentRunR_strictRankBandGap hrun hbefore hChildTopL hBotL
    have htop0 := regionBandTopNonneg hrun (List.getElem?_eq_some_iff.mp hChildTopL).1
    have hcHeight := CoordsImpl.layerHeight_nonneg run.coordinateProper childTopLayer
    have hbHeight := CoordsImpl.layerHeight_nonneg run.coordinateProper botLayer
    omega
  have hChildHi := boundsOf_bottom_le_of_all hChildUpperNonneg (fun rect hm => (hAll rect hm).2)
  have hParentLo := boundsOf_minY_le_rect_y _ [] _ hptMem
  have hParentHi := rect_bottom_le_boundsOf_bottom _ [] _ hpbMem
  change (boundsOf (groupMemberRects cg run parent.decl) []).minY ≤ run.ys.getD u 0 at hParentLo
  rw [rectAt_eq_box] at hParentHi
  simp only [RouteImpl.yAt, RouteImpl.nodeH, hpbot,
    (hpbotZero hpbKind).2, Int.add_zero] at hParentHi
  rw [frameRect_group_span hu hp, frameRect_group_span hv hc]
  dsimp only
  exact ⟨by omega, by omega⟩

end Elegant.Layered.PipelineImpl


import Elegant.Layered.RegionActiveAncestorCaption
import Elegant.Layered.RegionSelectedCaptionClearance
import Elegant.Layered.RegionFallbackAncestorGroupVertical

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- The target is strictly below the caption owner in the active candidate.
A declared group lowered to a fixed box still has the plain-member rank bound. -/
def R8b_ActiveDescendantCaption {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) (i pos : Nat) : Prop :=
  ∃ (s : RegionSpec) (owner target : Node), selected.spec = some s ∧
    selected.cg.nodes[i]? = some owner ∧ owner.border = -2 ∧
    selected.cg.nodes[pos]? = some target ∧ (target.border = 0 ∨ target.border = -2) ∧
    owner.decl ≠ target.decl ∧ target.clusterPath.contains owner.decl = true

private theorem descendantCaption_titleSeed {P : Params} {exact : List Nat}
    {s : RegionSpec} {p : Proper} {i : Nat} {node : Node}
    (hnode : p.nodes[i]? = some ⟨node, false, none, false⟩)
    (hborder : node.border = -2) (halign : p.nodes.length = p.rank.length) :
    ∃ j, p.nodes.length ≤ j ∧
      (coordinateGraphR P exact (some s) p).nodes[j]? =
        some ⟨{ node with
          border := 3
          loopExtent := 0
          h := (s.titles.getD node.decl (0, 0)).2 + P.clusterPad }, false, none, false⟩ ∧
      rk (coordinateGraphR P exact (some s) p).rank j =
        rk (coordinateGraphR P exact (some s) p).rank i := by
  let original : ProperNode := ⟨node, false, none, false⟩
  let sized := sizeProperPortsX P exact p
  let tops := titleNodes sized
  let titled := titleReservationsR s.titles P.clusterPad sized
  let copy : ProperNode :=
    ⟨{ node with
      border := 3
      loopExtent := 0
      h := (s.titles.getD node.decl (0, 0)).2 + P.clusterPad }, false, none, false⟩
  have hsz : sized.nodes[i]? = some original := by
    have hne : (node.border != 0) = true := by rw [hborder]; decide
    simp only [sized, sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hnode,
      Option.map_some]
    simp [original, hne]
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp
    (show (original, i) ∈ tops from List.mem_filter.mpr
      ⟨List.mem_zipIdx_iff_getElem?.mpr hsz, by simp [original, hborder]⟩)
  let j := p.nodes.length + n
  have htitle : titled.nodes[j]? = some copy := by
    let titleCopy (q : ProperNode × Nat) : ProperNode :=
      { q.1 with
        node := { q.1.node with
          border := 3
          loopExtent := 0
          h := (s.titles.getD q.1.node.decl (0, 0)).2 + P.clusterPad } }
    change (sized.nodes.map titleF ++ tops.map titleCopy)[j]? = some copy
    have hsized_len : sized.nodes.length = p.nodes.length := sizeProperPortsX_length P exact p
    have hle : (sized.nodes.map titleF).length ≤ j := by
      rw [List.length_map, hsized_len]
      exact Nat.le_add_right _ _
    rw [List.getElem?_append_right hle]
    have hindex : j - (sized.nodes.map titleF).length = n := by
      change p.nodes.length + n - (sized.nodes.map titleF).length = n
      rw [List.length_map, hsized_len]
      exact Nat.add_sub_cancel_left _ _
    rw [hindex, List.getElem?_map, hn, Option.map_some]
  obtain ⟨_, he, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  have hb : bordered.nodes[j]? = some copy := by
    change (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes[j]? = some copy
    rw [he, List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents bordered).nodes[j]? = some copy := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hb] <;> rfl
  have hmat : (materializeDummyPaths (clearProxyExtents bordered)).nodes[j]? = some copy := by
    simp [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx, hclear, copy]
  refine ⟨j, Nat.le_add_right _ _, hmat, ?_⟩
  obtain ⟨_, hrank⟩ := addClusterBorders_rank_prefix titled P.clusterBorderW
  have htitleRank : titled.rank = p.rank ++ tops.map (fun q => rk p.rank q.2) := rfl
  change rk (OrderImpl.addClusterBorders titled P.clusterBorderW).rank j =
    rk (OrderImpl.addClusterBorders titled P.clusterBorderW).rank i
  have hin : i < p.rank.length := by
    rw [← halign]
    exact (List.getElem?_eq_some_iff.mp hnode).1
  have hj : j < (p.rank ++ tops.map (fun q => rk p.rank q.2)).length := by
    rw [List.length_append, List.length_map, ← halign]
    exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.mp hn).1 _
  have hii : i < (p.rank ++ tops.map (fun q => rk p.rank q.2)).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le hin (Nat.le_add_right _ _)
  have hle : p.rank.length ≤ j := by rw [← halign]; exact Nat.le_add_right _ _
  have hoffset : j - p.rank.length = n := by
    rw [← halign]
    exact Nat.add_sub_cancel_left _ _
  rw [hrank, htitleRank, NormalizeImpl.rk_append_left hj, NormalizeImpl.rk_append_left hii,
    NormalizeImpl.rk_append_right hle, hoffset, NormalizeImpl.rk_append_left hin]
  simp only [rk, List.getD_eq_getElem?_getD, List.getElem?_map, hn, Option.map_some,
    Option.getD_some]

private theorem descendantCaption_clusterBounds {P : Params} {inp : Input}
    {s : RegionSpec} {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp cg = .ok (some rm))
    {row : RegionCluster} (hrow : row ∈ rm.clusters) :
    row.top < cg.nodes.length ∧ row.bottom < cg.nodes.length := by
  have hrows : rm.clusters = clusterRows inp s cg := by
    unfold newComponentRegions at h
    dsimp only at h
    split at h
    · cases h
    · obtain ⟨_, _, h⟩ := bind_ok' h
      split at h
      · cases h
      · exact (congrArg ComponentRegions.clusters (Option.some.inj (Except.ok.inj h))).symm
  rw [hrows] at hrow
  unfold clusterRows at hrow
  obtain ⟨q, hq, hr⟩ := List.mem_filterMap.mp hrow
  dsimp only at hr
  split at hr
  · cases hr
  · rw [← Option.some.inj hr]
    have htop : q.2 < cg.nodes.length :=
      (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)).1
    refine ⟨htop, ?_⟩
    change (match cg.nodes.zipIdx.find? (fun b => b.1.border == 2 && b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2) < cg.nodes.length
    split
    · rename_i b hfind
      exact (List.getElem?_eq_some_iff.mp
        (List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfind))).1
    · exact htop

private theorem descendantCaption_layersOk {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    RouteImpl.layersOk run.proper run.layers = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages h
  rcases stages.hLanes with ⟨_, hlanes⟩ | ⟨_, hlanes⟩
  · exact (RouteImpl.routeWithLanes_geometry hlanes).1
  · obtain ⟨_, hbase, _, _⟩ := routeWithLanesR_spec hlanes
    exact (RouteImpl.route_spec hbase).1

private theorem descendantCaption_headerBand {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cand cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some s) inp cand labels orderOptions = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp cand = .ok (some rm))
    {i : Nat} {owner : Node} (hi : cg.nodes[i]? = some owner) (hb : owner.border = -2) :
    let r := (rk run.proper.rank i).toNat
    ∃ layer, run.layers[r]? = some layer ∧ 0 ≤ rk run.proper.rank i ∧
      (s.titles.getD owner.decl (0, 0)).2 + P.clusterPad ≤
        CoordsImpl.layerHeight run.coordinateProper layer := by
  dsimp only
  obtain ⟨_, _, labeled, p, _, _, _, _, hrank, hnorm, hlabels, hcoord, _, _, ⟨alloc⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hlabeled := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hi) rfl
  have halign : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hlabels, (Labels.addLabelNodes_metadata hlabels).2.1]
    exact (normalize_node_rank_alignment hnorm).1
  let seed : ProperNode :=
    ⟨{ owner with
      border := 3
      loopExtent := 0
      h := (s.titles.getD owner.decl (0, 0)).2 + P.clusterPad }, false, none, false⟩
  obtain ⟨j, hj, hseed, hjRank⟩ := descendantCaption_titleSeed (P := P) (exact := exact)
    (s := s) hlabeled hb halign
  change (coordinateGraphR P exact (some s) labeled).nodes[j]? = some seed at hseed
  rw [hcoord] at hseed hjRank
  have hcovered (k : Nat) (hk : k < cand.nodes.length) : k < labeled.nodes.length := by
    have hk' : k < cg.nodes.length := by rwa [rankEquivalentR_nodes_eq hrank]
    have hc : cg.nodes[k]? = some cg.nodes[k] := List.getElem?_eq_getElem hk'
    have hl := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hc) rfl
    exact (List.getElem?_eq_some_iff.mp hl).1
  have hsrc : alloc.placement.p.nodes[j]? = some seed := by rwa [alloc.hPlacement]
  obtain ⟨nd, hnd, _, hkeep⟩ := (groupPlain_reservedPorts_record alloc.hFramesAndPorts).2 hsrc
  have haway : ∀ row ∈ alloc.placement.rm.clusters, row.top ≠ j ∧ row.bottom ≠ j := by
    intro row hm
    have hm' : row ∈ rm.clusters := by simpa only [alloc.hPlacement] using hm
    obtain ⟨ht, hbt⟩ := descendantCaption_clusterBounds hactive hm'
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le (hcovered _ ht) hj),
      Nat.ne_of_lt (Nat.lt_of_lt_of_le (hcovered _ hbt) hj)⟩
  rw [(hkeep haway).1] at hnd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, proxied, _, _, stages⟩ := componentRunR_stages hrun
  have hproxy : proxyWidths run.coordinateProper run.coordinateXs = .ok (proxied, run.xs) := by
    rw [stages.hCoordProper]
    exact stages.hProxy
  have hjFinal : run.proper.nodes[j]? = some seed := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
    exact ((proxyWidths_rel hproxy).2.2.2.2.2 j seed hnd (by simp [seed])).1
  have hRank : run.proper.rank = p.rank := by
    have hp := alloc.hFramesAndPorts
    unfold reservedPortsR at hp
    obtain ⟨_, _, hp⟩ := bind_ok' hp
    have hcp := congrArg (fun q : List Int × Proper => q.2.rank) (Except.ok.inj hp)
    change alloc.placement.p.rank = run.coordinateProper.rank at hcp
    rw [alloc.hPlacement] at hcp
    rw [← stages.hDrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1, ← hcp]
  obtain ⟨layer, hlayer, hjMem, hjNonneg⟩ :=
    (RouteImpl.layersOk_spec (descendantCaption_layersOk hrun)).2.2.2.1 j
      (List.getElem?_eq_some_iff.mp hjFinal).1
  have he : rk run.proper.rank j = rk run.proper.rank i := by rwa [hRank]
  rw [he] at hlayer hjNonneg
  have hh := CoordsImpl.layerHeight_ge (p := run.coordinateProper) hjMem
  simp only [CoordsImpl.nodeH, hnd, seed] at hh
  exact ⟨layer, hlayer, hjNonneg, hh⟩

private theorem descendantCaption_specHeight {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) {s : RegionSpec} (hs : selected.spec = some s)
    {key : Nat} (hkey : key < e.lines.length) :
    (s.titles.getD key (0, 0)).2 = (titleCaptionSize e.params o (e.lines.getD key [])).h := by
  have he := selected.effective_eq
  rw [hs] at he
  change (some s : Option RegionSpec) = (if selected.regions.isSome then
    if idSets.isEmpty then none else some (RegionSpec.mk idSets (e.lines.map fun ls =>
      let width := ls.foldl (fun w line => max w line.width) 0
      let height := (max 1 ls.length : Int) * e.params.lineH
      match o.direction with
      | .LR | .RL => (height, width)
      | .TB | .BT => (width, height))) else none) at he
  split at he
  · split at he
    · cases he
    · rw [Option.some.inj he]
      have hline : e.lines[key]? = some e.lines[key] := List.getElem?_eq_getElem hkey
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hline, Option.map_some,
        Option.getD_some, List.getD_eq_getElem?_getD, hline, Option.getD_some]
      unfold titleCaptionSize
      cases o.direction <;> rfl
  · cases he

private theorem descendantCaption_contributorLow {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run)) {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd) :
    let r := (rk run.proper.rank v).toNat
    ∃ layer, run.layers[r]? = some layer ∧ run.top.getD r 0 ≤ run.ys.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, proxied, ⟨y, top⟩, ysMid, hs⟩ :=
    componentRunR_stages hrun
  have hvP := (List.getElem?_eq_some_iff.mp hv).1
  obtain ⟨layer, hlayer, hmem, hnonneg⟩ :=
    (RouteImpl.layersOk_spec (descendantCaption_layersOk hrun)).2.2.2.1 v hvP
  let r := (rk run.proper.rank v).toNat
  have hrank : run.proper.rank = placed.rank := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel hs.hProxy).2.1
  have hnodes : run.proper.nodes = proxied.nodes := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes]
  have hvC : v < placed.nodes.length := by
    rwa [hnodes, (proxyWidths_rel hs.hProxy).2.2.1] at hvP
  have hvPlaced : placed.nodes[v]? = some placed.nodes[v] := List.getElem?_eq_getElem hvC
  obtain ⟨hyLen, htopLen⟩ := CoordsImpl.rankCoordsWith_length hs.hYt
  have hvY : v < y.length := by rwa [hyLen]
  have hrTop : r < top.length := by
    rw [htopLen]
    exact (List.getElem?_eq_some_iff.mp hlayer).1
  have hr : rk placed.rank v = (r : Int) := by
    rw [← hrank]
    exact (Int.toNat_of_nonneg hnonneg).symm
  have hbefore := proxyYs_getD placed run.layers top y hvPlaced hvY
  have hrIdx : (rk placed.rank v).toNat = r := by rw [← hrank] <;> rfl
  have hlo := (rankAxis_node_in_band (r := r) hs.hYt hlayer hmem hvC hr).1
  have hh := CoordsImpl.layerHeight_nonneg placed (run.layers.getD r [])
  simp only [hrIdx] at hbefore
  have hmid : top.getD r 0 ≤ ysMid.getD v 0 := by
    rw [← hs.hYsMid, hbefore]
    split
    · exact Int.le_refl _
    · split
      · omega
      · exact hlo
  have hmidLen : ysMid.length = placed.nodes.length := by
    rw [← hs.hYsMid]
    simpa only [proxyYs, List.length_map, List.length_zipIdx] using hyLen
  obtain ⟨_, shifts, _, _, _, _, htopShift, hyShift⟩ :=
    (runHooksShift_exact P exactIds inp cg' labels).shifts placed run.layers ysMid top
      run.ys run.top hs.hReserve
  have hys := hyShift v (by rwa [hmidLen])
  change run.ys.getD v 0 = ysMid.getD v 0 + shifts.getD (rk placed.rank v).toNat 0 at hys
  rw [hrIdx] at hys
  refine ⟨layer, hlayer, ?_⟩
  change run.top.getD r 0 ≤ run.ys.getD v 0
  rw [htopShift r hrTop, hys]
  exact Int.add_le_add_right hmid _

private theorem descendantCaption_rawGap {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hpart : part ∈ e.componentsAcc.parts)
    {i pos : Nat} {raw : Rect} (hraw : (i, raw) ∈ componentTitles e.params selected.cg selected.run)
    (hdesc : R8b_ActiveDescendantCaption selected i pos) :
    let size := titleCaptionSize e.params o (e.lines.getD (part.1.getD i 0) [])
    raw.y + size.h < (frameRect e.params selected.cg selected.run pos).y := by
  obtain ⟨s, owner, target, hs, ho, htop, ht, htKind, hne, hdesc⟩ := hdesc
  let P := e.params
  let cg := selected.cg
  change cg.nodes[i]? = some owner at ho
  change cg.nodes[pos]? = some target at ht
  let run := selected.run
  let cand := componentCandidateR (some s) e.graph part.1 selected.candidate
  let orig := componentCandidate e.graph part.1 selected.candidate
  let rank := fun v : Nat => rk run.proper.rank v
  let r := fun v : Nat => (rank v).toNat
  let size := titleCaptionSize P o (e.lines.getD (part.1.getD i 0) [])
  have hcomp : part.1 ∈ components e.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) e.components_eq).1]
    exact List.mem_map_of_mem hpart
  have hrun := selected.run_eq
  rw [hs] at hrun
  have hactive : newComponentRegions selected.spec P inp
      (componentCandidateR selected.spec e.graph part.1 selected.candidate) = .ok selected.regions := by
    rw [selected.effective_eq]
    exact componentTrialR_selected_regions _ selected.regions_eq
  obtain ⟨rm, hrm⟩ : ∃ rm, selected.regions = some rm := by
    cases h : selected.regions with
    | none =>
      have he := selected.effective_eq
      rw [hs, h] at he
      cases he
    | some rm => exact ⟨rm, rfl⟩
  rw [hs, hrm] at hactive
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes : cg.nodes = cand.nodes := rankEquivalentR_nodes_eq hrank
  have horig : orig.nodes = cand.nodes := by
    dsimp only [orig, cand]
    rw [componentCandidate_nodes]
    rfl
  have hoCand : cand.nodes[i]? = some owner := by rwa [← hnodes]
  have hoOrig : orig.nodes[i]? = some owner := by rwa [horig]
  obtain ⟨hoKey, _, _, hsource⟩ := active_candidate_top_source e hcomp hoCand htop
  obtain ⟨oBox, hoBox, hoPath⟩ := X_cg_group_box e.graph0_eq e.graph_eq hoOrig htop
  have hlines := boxLines_length e.lines_eq
  have hiLine : owner.decl < e.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hiKey : part.1.getD i 0 = owner.decl := by
    simp only [List.getD_eq_getElem?_getD, hoKey, Option.getD_some]
  have hsize : (s.titles.getD owner.decl (0, 0)).2 = size.h := by
    dsimp only [size]
    rw [hiKey]
    exact descendantCaption_specHeight selected hs hiLine
  obtain ⟨ownerLayer, hOwnerLayer, hOwnerRank, hreserve⟩ :=
    descendantCaption_headerBand hrun hactive ho htop
  rw [hsize] at hreserve
  obtain ⟨_, oa, hOc, hOa, _, _, hOcKind, _, _, hOaPath, _⟩ :=
    componentRunR_active_marker_records hrun hactive ho (Or.inl htop)
  have hOwnerMember : owner.decl ∈ owner.clusterPath := by rw [hoPath]; simp
  have hOuterTop : (frameRect P cg run i).y ≤ run.ys.getD i 0 := by
    have hGet : cg.nodes.getD i default = owner := by
      rw [List.getD_eq_getElem?_getD, ho]
      rfl
    exact (frameRect_member_vertical (P := P) (q := (oa, i))
      (by rw [hGet]; exact htop) (List.mem_zipIdx_iff_getElem?.mpr hOa)
      (by rw [hGet, hOaPath]; exact List.contains_iff_mem.mpr hOwnerMember)).1
  have hTopY := ((componentRunR_boundaryRankBands (exactIds := exactIds) hrun).1 hOc
    (by rw [hOcKind, htop]; omega)).2.2.1 (hOcKind.trans htop)
  change run.ys.getD i 0 = run.top.getD (r i) 0 at hTopY
  have hRawY := componentTitles_y_eq_frame hraw
  have hCapBottom : raw.y + size.h ≤
      run.top.getD (r i) 0 + CoordsImpl.layerHeight run.coordinateProper ownerLayer := by
    change raw.y = (frameRect P cg run i).y + P.clusterPad at hRawY
    rw [hRawY, ← hTopY, Int.add_assoc, Int.add_comm P.clusterPad size.h]
    exact Int.add_le_add hOuterTop hreserve
  have later {v : Nat} {layer : List Nat} (hv : rank i < rank v)
      (hl : run.layers[r v]? = some layer) :
      raw.y + size.h < run.top.getD (r v) 0 := by
    have hlt : r i < r v :=
      (Int.toNat_lt_toNat (Int.lt_of_le_of_lt hOwnerRank hv)).mpr hv
    exact Int.lt_of_le_of_lt hCapBottom
      (componentRunR_strictRankBandGap (exactIds := exactIds) hrun hlt hOwnerLayer hl)
  have bottom {v : Nat} {n : Node} (hn : cand.nodes[v]? = some n) (hb : n.border = -2) :
      ∃ b, (cand.nodes.zipIdx.find? fun q => q.1.border == 2 && q.1.decl == n.decl) =
        some b := by
    rw [← horig]
    exact X_componentRun_cg_bottom_find e.graph0_eq e.graph_eq hlines hcomp
      (by rwa [horig]) hb
  change raw.y + size.h < (frameRect P cg run pos).y
  have htCand : cand.nodes[pos]? = some target := by rwa [← hnodes]
  rcases htKind with htPlain | htTop
  · obtain ⟨b, hb⟩ := bottom hoCand htop
    have hlt := (componentRunR_compound_leaf_rank_window hrun
      (top := (owner, i)) (member := (target, pos))
      (List.mem_zipIdx_iff_getElem?.mpr hoCand) htop hb
      (List.mem_zipIdx_iff_getElem?.mpr htCand) htPlain hdesc).1
    obtain ⟨layer, hlayer, _, hy, _⟩ :=
      (componentRunR_plain_rank_bands (exactIds := exactIds) hrun).1 ht htPlain
    exact Int.lt_of_lt_of_le (later hlt hlayer) hy
  · have htOrig : orig.nodes[pos]? = some target := by rwa [horig]
    obtain ⟨tBox, htBox, htPath⟩ := X_cg_group_box e.graph0_eq e.graph_eq htOrig htTop
    have hpref := X_cg_scope_prefix hwf hoBox hoPath htBox htPath hdesc
    have hpathNe : owner.clusterPath ≠ target.clusterPath := by
      intro he
      have hd := congrArg List.getLast? he
      exact hne (by simpa [hoPath, htPath] using hd)
    have hprefLt : owner.clusterPath.length < target.clusterPath.length := by
      obtain ⟨rest, he⟩ := hpref
      have hrest : rest ≠ [] := fun h => hpathNe (by simpa [h] using he)
      rw [← he, List.length_append]
      have := List.length_pos_iff.mpr hrest
      omega
    have hprefNe : owner.clusterPath ≠ [] := by rw [hoPath]; simp
    obtain ⟨parent, hparent⟩ := X_candidate_parent_top_exists e.graph0_eq e.graph_eq hlines
      hwf hfp hcomp selected.candidate (x := (target, pos))
      (List.mem_zipIdx_iff_getElem?.mpr htOrig) htTop hpref hprefLt hprefNe
    have hpOrig : orig.nodes[parent.2]? = some parent.1 :=
      List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hparent)
    have hpCand : cand.nodes[parent.2]? = some parent.1 := by rwa [horig] at hpOrig
    have hpNode : cg.nodes[parent.2]? = some parent.1 := by rwa [hnodes]
    have hpKindPath : parent.1.border = -2 ∧ parent.1.clusterPath = target.clusterPath.dropLast := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hparent
    obtain ⟨parentBottom, hpBottom⟩ := bottom hpCand hpKindPath.1
    obtain ⟨targetBottom, htBottom⟩ := bottom htCand htTop
    have hpMem : parent.1.clusterPath.contains owner.decl = true := by
      apply List.contains_iff_mem.mpr
      rw [hpKindPath.2]
      obtain ⟨rest, he⟩ := hpref
      have hrest : rest ≠ [] := fun h => hpathNe (by simpa [h] using he)
      rw [← he, List.dropLast_append_of_ne_nil hrest]
      exact List.mem_append.mpr (Or.inl hOwnerMember)
    obtain ⟨_, _, _, _, _, _, _, hoWindow⟩ :=
      activeCandidateOriginalFrameRankWindow e hwf hfp hcomp hrun hactive ho htop
    have hpRank := (hoWindow hpNode hpMem).1
    have htRank := (componentRunR_compound_child_strictRankWindow hrun
      (parent := parent) (child := (target, pos))
      (List.mem_zipIdx_iff_getElem?.mpr hpCand) hpKindPath.1 hpBottom
      (List.mem_zipIdx_iff_getElem?.mpr htCand) htTop hpKindPath.2.symm htBottom).1
    have hlt : rank i < rank pos := Int.lt_of_le_of_lt hpRank htRank
    obtain ⟨_, _, _, _, _, _, _, htWindow⟩ :=
      activeCandidateOriginalFrameRankWindow e hwf hfp hcomp hrun hactive ht htTop
    have hLower : ∀ rect ∈ groupMemberRects cg run target.decl, raw.y + size.h + 1 ≤ rect.y := by
      intro rect hm
      obtain ⟨v, nd, hv, hvPath, rfl⟩ := fbs_groupMemberRects_spec hm
      obtain ⟨_, _, _, _, hsrc, _, hpath, _, hlo, _⟩ :=
        activeFrameContributorRankSources e hcomp hrun hactive hv hvPath
      have hvRank : rank i < rank v :=
        Int.lt_of_lt_of_le hlt (Int.le_trans (htWindow hsrc hpath).1 hlo)
      obtain ⟨layer, hlayer, hy⟩ := descendantCaption_contributorLow (exactIds := exactIds) hrun hv
      change run.top.getD (r v) 0 ≤ run.ys.getD v 0 at hy
      change raw.y + size.h + 1 ≤ run.ys.getD v 0
      exact Int.add_one_le_of_lt (Int.lt_of_lt_of_le (later hvRank hlayer) hy)
    obtain ⟨_, tActual, _, hActual, _, _, _, _, _, hActualPath, _⟩ :=
      componentRunR_active_marker_records hrun hactive ht (Or.inl htTop)
    have hself : tActual.node.clusterPath.contains target.decl = true := by
      rw [hActualPath, htPath]
      exact List.contains_iff_mem.mpr (by simp)
    have hmember := fbs_groupMemberRects_mem (cg := cg) hActual hself
    have hnonempty : groupMemberRects cg run target.decl ≠ [] := by
      intro he
      rw [he] at hmember
      cases hmember
    have hlo := boundsOf_minY_ge_of_all hnonempty hLower
    rw [frameRect_group_span ht htTop]
    exact Int.lt_of_add_one_le hlo

/-- The measured caption ends strictly before a descendant frame along the
selected part's rank axis. Both rectangles receive the same placement shift. -/
theorem r8b_activeDescendantCaption_rankGap {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hpart : part ∈ e.componentsAcc.parts)
    {i pos : Nat} {stored frame : Rect}
    (hmem : (i, stored) ∈ part.2.titles) (hframe : part.2.rects[pos]? = some frame)
    (hdesc : R8b_ActiveDescendantCaption selected i pos) :
    let size := titleCaptionSize e.params o (e.lines.getD (part.1.getD i 0) [])
    stored.y + size.h < frame.y := by
  let bounds := placeBoundsX e.params selected.cg selected.run e.measured selected.loops
  let dx := 0 - bounds.minX
  let dy := -bounds.minY
  let size := titleCaptionSize e.params o (e.lines.getD (part.1.getD i 0) [])
  rw [selected.part_eq] at hmem hframe
  change (i, stored) ∈ (componentTitles e.params selected.cg selected.run).map
    (fun q => (q.1, shiftRect dx dy q.2)) at hmem
  obtain ⟨⟨j, raw⟩, hraw, hpair⟩ := List.mem_map.mp hmem
  obtain ⟨hji, hstored⟩ := Prod.mk.inj hpair
  change j = i at hji
  subst j
  change (((List.range selected.cg.nodes.length).map
    (frameRect e.params selected.cg selected.run)).map (shiftRect dx dy))[pos]? =
      some frame at hframe
  have hpos : pos < selected.cg.nodes.length := by
    simpa only [List.length_map, List.length_range] using (List.getElem?_eq_some_iff.mp hframe).1
  simp only [List.getElem?_map, List.getElem?_range hpos, Option.map_some, Option.some.injEq] at hframe
  have hgap := descendantCaption_rawGap selected hwf hfp hpart hraw hdesc
  change raw.y + size.h < (frameRect e.params selected.cg selected.run pos).y at hgap
  change stored.y + size.h < frame.y
  rw [← hstored, ← hframe]
  simp only [shiftRect]
  omega

theorem r8b_activeDescendantCaption_disjoint {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hpart : part ∈ e.componentsAcc.parts)
    {i pos : Nat} {stored frame : Rect}
    (hmem : (i, stored) ∈ part.2.titles) (hframe : part.2.rects[pos]? = some frame)
    (hdesc : R8b_ActiveDescendantCaption selected i pos) :
    let size := titleCaptionSize e.params o (e.lines.getD (part.1.getD i 0) [])
    Disjoint frame { stored with w := size.w, h := size.h } :=
  rect_disjoint_of_y (Or.inr (Int.le_of_lt
    (r8b_activeDescendantCaption_rankGap selected hwf hfp hpart (stored := stored) hmem hframe hdesc)))

private theorem descendantCaption_remaining_inactive {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) (hpart : part ∈ e.componentsAcc.parts)
    {i pos key : Nat} {stored : Rect} {source : ModelBox}
    (hm : (i, stored) ∈ part.2.titles) (hk : part.1[pos]? = some key)
    (hsource : inp.boxes[key]? = some source)
    (hforeign : ¬ R8b_ActiveForeignCaption selected i pos)
    (hown : ¬ (i = pos ∧ ∃ s, selected.spec = some s))
    (hancestor : ¬ R8b_ActiveAncestorCaption selected i pos)
    (hdescendant : ¬ R8b_ActiveDescendantCaption selected i pos) : selected.spec = none := by
  cases hs : selected.spec with
  | none => rfl
  | some s =>
    exfalso
    let bounds := placeBoundsX e.params selected.cg selected.run e.measured selected.loops
    rw [selected.part_eq] at hm
    change (i, stored) ∈ (componentTitles e.params selected.cg selected.run).map
      (fun q => (q.1, shiftRect (0 - bounds.minX) (-bounds.minY) q.2)) at hm
    obtain ⟨⟨j, raw⟩, hraw, hpair⟩ := List.mem_map.mp hm
    have he : j = i := congrArg Prod.fst hpair
    subst j
    obtain ⟨entry, hentry, hb, hi, _, _⟩ :=
      componentTitles_dimension_source e.params selected.cg selected.run hraw
    change i = entry.2 at hi
    have ho : selected.cg.nodes[i]? = some entry.1 := by
      rw [hi]
      exact List.mem_zipIdx_iff_getElem?.mp hentry
    let cand := componentCandidateR (some s) e.graph part.1 selected.candidate
    have hrun := selected.run_eq
    rw [hs] at hrun
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
    have hnodes : selected.cg.nodes = cand.nodes := by
      rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, h⟩
      · rw [he]
      · exact rankEquivalentR_nodes_eq h
    have hcomp : part.1 ∈ components e.graph := by
      rw [← (actual_components_parts_geometryR (by rfl) e.components_eq).1]
      exact List.mem_map_of_mem hpart
    have hoCand : cand.nodes[i]? = some entry.1 := by rwa [← hnodes]
    have hcandLen : cand.nodes.length = part.1.length := by
      change (componentGraph e.graph part.1).nodes.length = _
      simp only [componentGraph, List.length_map]
    have hpos : pos < cand.nodes.length := hcandLen.symm ▸ (List.getElem?_eq_some_iff.mp hk).1
    let target := cand.nodes[pos]
    have ht : cand.nodes[pos]? = some target := List.getElem?_eq_getElem hpos
    have htOut : selected.cg.nodes[pos]? = some target := by rwa [hnodes]
    have htKind := active_candidate_source_border e hcomp ht hk
      (List.getElem?_eq_some_iff.mp hsource).1
    have htargetKey : part.1[pos]? = some target.decl := by
      rcases htKind with htop | hplain
      · exact (active_candidate_top_source e hcomp ht htop).1
      · simpa only [active_candidate_plain_decl e hcomp ht hplain hk hsource] using hk
    have hownerKey := (active_candidate_top_source e hcomp hoCand hb).1
    have hd : entry.1.decl ≠ target.decl := by
      intro h
      obtain ⟨hil, hOi⟩ := List.getElem?_eq_some_iff.mp hownerKey
      obtain ⟨hpl, hTi⟩ := List.getElem?_eq_some_iff.mp htargetKey
      have hip := (List.Nodup.getElem_inj (hi := hil) (hj := hpl)
        (components_nodup e.graph part.1 hcomp)).mp (hOi.trans (h.trans hTi.symm))
      exact hown ⟨hip, s, hs⟩
    cases htargetPath : target.clusterPath.contains entry.1.decl with
    | true => exact hdescendant ⟨s, entry.1, target, hs, ho, hb, htOut,
        htKind.elim Or.inr Or.inl, hd, htargetPath⟩
    | false =>
      rcases htKind with htop | hplain
      · cases ha : entry.1.clusterPath.contains target.decl with
        | false => exact hforeign ⟨s, entry.1, target, hs, ho, hb, htOut, htargetPath,
            Or.inr ⟨htop, hd, ha⟩⟩
        | true => exact hancestor ⟨s, entry.1, target, hs, ho, hb, htOut, htop, hd,
            List.contains_iff_mem.mp ha⟩
      · exact hforeign ⟨s, entry.1, target, hs, ho, hb, htOut, htargetPath, Or.inl hplain⟩

/-- Only inactive chosen parts still need the installed-caption case.
The same-part route exclusions are unchanged. -/
def R_ExecutedPartFrameCoresB8ActiveDescendantCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ part ∈ execution.componentsAcc.parts,
      (∀ (selected : R8b_ChosenPart execution part)
        (index : Nat) (stored : Rect) (pos key : Nat) (src : ModelBox) (frame : Rect),
        (index, stored) ∈ part.2.labels → part.1[pos]? = some key →
        inp.boxes[key]? = some src → src.role = .group → part.2.rects[pos]? = some frame →
        ¬ R8b_EmittedOuterReversedAt selected index stored pos →
        ¬ R8b_EmittedReservedChildAt selected index pos →
        ¬ R8b_EmittedDemotedReversedAt selected index stored pos src →
        ¬ R8b_EmittedSelectedLoopFrameAt selected index pos →
        ¬ R8b_EmittedForwardChildAt selected index pos →
        Disjoint frame stored ∨ frame.StrictInside stored) ∧
      (∀ (selected : R8b_ChosenPart execution part)
        (i : Nat) (stored : Rect) (pos key : Nat) (src : ModelBox) (frame : Rect),
        (i, stored) ∈ part.2.titles → part.1[pos]? = some key →
        inp.boxes[key]? = some src → src.role = .group → part.2.rects[pos]? = some frame →
        selected.spec = none →
        let size := titleCaptionSize execution.params o (execution.lines.getD (part.1.getD i 0) [])
        Disjoint frame { stored with w := size.w, h := size.h } ∨
          frame.StrictInside { stored with w := size.w, h := size.h })

theorem R_activeAncestorCaptionRemainder_iff_activeDescendantCaptionRemainder
    (exactIds : List String) (idSets : List (String × List String)) :
    R_ExecutedPartFrameCoresB8ActiveAncestorCaptionRemainder exactIds idSets ↔
      R_ExecutedPartFrameCoresB8ActiveDescendantCaptionRemainder exactIds idSets := by
  classical
  constructor
  · intro h inp o res e hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := h e hwf hfp part hpart
    refine ⟨hroute, ?_⟩
    intro selected i stored pos key src frame hm hk hs hg hf hnone
    have inactive {s : RegionSpec} (he : selected.spec = some s) : False := by
      rw [hnone] at he
      cases he
    exact hcaption selected i stored pos key src frame hm hk hs hg hf
      (by rintro ⟨s, _, _, he, _⟩; exact inactive (s := s) he)
      (by rintro ⟨_, s, he⟩; exact inactive (s := s) he)
      (by rintro ⟨s, _, _, he, _⟩; exact inactive (s := s) he)
  · intro h inp o res e hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := h e hwf hfp part hpart
    refine ⟨hroute, ?_⟩
    intro selected i stored pos key src frame hm hk hs hg hf hforeign hown hancestor
    by_cases hd : R8b_ActiveDescendantCaption selected i pos
    · exact Or.inl (r8b_activeDescendantCaption_disjoint selected hwf hfp hpart hm hf hd)
    · exact hcaption selected i stored pos key src frame hm hk hs hg hf
        (descendantCaption_remaining_inactive selected hpart hm hk hs hforeign hown hancestor hd)

theorem flatC8bB_layoutRIds_activeDescendantCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String))
    (hcores : R_ExecutedPartFrameCoresB8ActiveDescendantCaptionRemainder exactIds idSets)
    (hfallW : R_FallbackCaptionClearBW exactIds idSets)
    (hres : R_PartSizingRResidual exactIds idSets)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    FlatC8bB (layoutRIds exactIds idSets) :=
  flatC8bB_layoutRIds_activeAncestorCaptionRemainder exactIds idSets
    ((R_activeAncestorCaptionRemainder_iff_activeDescendantCaptionRemainder exactIds idSets).mpr hcores)
    hfallW hres hcap

end Elegant.Layered.PipelineImpl

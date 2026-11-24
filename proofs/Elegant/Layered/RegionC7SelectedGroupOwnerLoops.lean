import Elegant.Layered.RegionFlatC7Selected
import Elegant.Layered.RegionFallbackAncestorFrameSides
import Elegant.Layered.RegionC5ContributorRank
import Elegant.Layered.RegionC5TerminalOrigRank
import Elegant.Layered.ForeignBorderSpansProof

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem rooted_suffix_at_member {pl : RegionPlacement} {resolve : Nat → Nat}
    {root member : Nat} {path : List Nat}
    (hpath : GroupPlainRootedPath pl resolve root path) (hmem : member ∈ path) :
    ∃ pre suffix, path = pre ++ member :: suffix ∧
      GroupPlainRootedPath pl resolve (resolve member) suffix := by
  induction path generalizing root with
  | nil => simp at hmem
  | cons first rest ih =>
    change resolve first ∈ pl.children.getD root [] ∧
      GroupPlainRootedPath pl resolve (resolve first) rest at hpath
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨[], rest, rfl, hpath.2⟩
    · obtain ⟨pre, suffix, he, hrest⟩ := ih hpath.2 hmem
      exact ⟨first :: pre, suffix, congrArg (List.cons first) he, hrest⟩

private theorem active_descendant_right
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
    {u v : Nat} {owner target : Node}
    (hu : cg.nodes[u]? = some owner) (hgroup : owner.border = -2)
    (hv : cg.nodes[v]? = some target) (hplain : target.border = 0)
    (hdesc : owner.decl ∈ target.clusterPath) :
    (frameRect e.params cg run v).x + (frameRect e.params cg run v).w ≤
      (frameRect e.params cg run u).x + (frameRect e.params cg run u).w := by
  let cand := componentCandidateR (some s) e.graph comp index
  obtain ⟨_, _, _, _, _, _, _, _, hrank, hnorm, hlabels, hcoord, hmin, _, ⟨st⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes : cg.nodes = cand.nodes := rankEquivalentR_nodes_eq hrank
  have huCand : cand.nodes[u]? = some owner := by rwa [← hnodes]
  have hvCand : cand.nodes[v]? = some target := by rwa [← hnodes]
  obtain ⟨group, cluster, hgroupOf, hcluster, hdecl⟩ :=
    active_candidate_top_cluster hactive huCand hgroup
  obtain ⟨bucket, _, hownerOf, _, _, htargetRight⟩ :=
    st.activePlain_frame_in_ownerBucket hrun hactive hrank hnorm hlabels hcoord hmin hv hplain
  have hrooted := r8b_executed_endpoint_rooted e hwf hfp hcomp hactive st hmin hvCand hownerOf
  let resolve := fun d => (clusterOfDecl rm d).getD rm.clusters.length
  have hresolve : resolve owner.decl = group := by simp only [resolve, hgroupOf, Option.getD_some]
  have hparents := activeRegion_parent_count hactive
  have hbounded := (r8b_executed_rooted_path_bounds st hparents hmin hrooted).2
  obtain ⟨pre, suffix, hpath, htail⟩ := rooted_suffix_at_member hrooted hdesc
  cases hlast : (owner.decl :: suffix).getLast? with
  | none => simp [List.getLast?_cons] at hlast
  | some last =>
    have hlastPath : target.clusterPath.getLast? = some last := by
      simp only [hpath, List.getLast?_append, hlast, Option.some_or]
    have hlastOf : clusterOfDecl rm last = some bucket := by simpa only [hlastPath] using hownerOf
    have hlastRead : resolve last = bucket := by simp only [resolve, hlastOf, Option.getD_some]
    have hinTail (d : Nat) (hd : d ∈ owner.decl :: suffix) : resolve d < rm.clusters.length :=
      hbounded d (by rw [hpath]; exact List.mem_append_right _ hd)
    let widths := reserveWidths st.placement e.params
    let fullRight := fun g => st.allocation.lefts.getD g 0 + widths.getD g 0
    let frameRight := fun g => fullRight g - st.placement.buckets.loopWidth.getD g 0
    have hplLen : st.placement.rm.clusters.length = rm.clusters.length := by rw [st.hPlacement]
    have hpad := (checkedParams_sizing_nonneg e.checked).2.1
    have hborder := checkedParams_clusterBorderW_ge_one e.checked
    have hinset : 0 ≤ regionInsetOf e.params := by unfold regionInsetOf; omega
    have hslot : 0 ≤ e.params.slot := by have := componentRunR_slot_pos hrun; omega
    obtain ⟨hown, hlane, hloop⟩ := componentRunR_active_bucket_signs hrun st
    have hwidths : ∀ j, 0 ≤ widths.getD j 0 := reserveWidths_nonnegative hinset hown hlane hloop
    have hsum (row : List Nat) : 0 ≤ (row.map fun j => widths.getD j 0).sum := by
      induction row with
      | nil => simp
      | cons first rest ih =>
        rw [List.map_cons, List.sum_cons]
        exact Int.add_nonneg (hwidths first) ih
    have bucketRight (g : Nat) (hg : g < rm.clusters.length) :
        groupPlain_bucketRight st.placement e.params st.allocation g ≤ frameRight g := by
      have hp : g < st.placement.rm.clusters.length := by rwa [hplLen]
      obtain ⟨_, _, ho, hf, hc⟩ := (st.reservation_order hparents hmin).2 g (Nat.le_of_lt hg)
      have hroom := reserveWidths_room_from_last_writes (pl := st.placement)
        (P := e.params) ho hp hf hc
      change 2 * regionInsetOf e.params + st.placement.buckets.widths.getD g 0 +
        ((st.placement.children.getD g []).map fun j => widths.getD j 0).sum +
        laneExtentOf st.placement.buckets e.params.slot g ≤
        widths.getD g 0 - st.placement.buckets.loopWidth.getD g 0 at hroom
      have hsum0 := hsum (st.placement.children.getD g [])
      have hlane0 := hlane g
      unfold groupPlain_bucketRight groupPlain_bucketLeft groupPlain_allocLeft frameRight fullRight
      rw [ite_eq_right (Nat.ne_of_lt hp)]
      omega
    have childRight {g child : Nat} (hg : g < rm.clusters.length)
        (hm : child ∈ st.placement.children.getD g []) : fullRight child ≤ frameRight g := by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
      have hleft := st.childBudget_left_from_allocation hactive hmin (Nat.le_of_lt hg) hk
      rw [ite_eq_right (Nat.ne_of_lt hg)] at hleft
      have hright := st.childBudget_precedes_laneBand (o := o) hactive e.checked hslot hmin hg hk
      dsimp only at hright
      have hlane0 := hlane g
      dsimp only [frameRight, fullRight, widths]
      rw [hleft]
      omega
    have walk (d : Nat) (ds : List Nat)
        (hr : GroupPlainRootedPath st.placement resolve (resolve d) ds)
        (hb : ∀ a ∈ d :: ds, resolve a < rm.clusters.length)
        (hl : (d :: ds).getLast? = some last) :
        groupPlain_bucketRight st.placement e.params st.allocation (resolve last) ≤
          frameRight (resolve d) := by
      induction ds generalizing d with
      | nil =>
        have he : d = last := Option.some.inj hl
        rw [← he]
        exact bucketRight (resolve d) (hb d (by simp))
      | cons child rest ih =>
        change resolve child ∈ st.placement.children.getD (resolve d) [] ∧
          GroupPlainRootedPath st.placement resolve (resolve child) rest at hr
        have hnext := ih (d := child) hr.2 (fun a ha => hb a (List.mem_cons_of_mem _ ha))
          (by simpa only [List.getLast?_cons_cons] using hl)
        have hupper := childRight (hb d (by simp)) hr.1
        have hchildFrame : frameRight (resolve child) ≤ fullRight (resolve child) :=
          Int.sub_le_self _ (hloop (resolve child))
        exact Int.le_trans hnext (Int.le_trans hchildFrame hupper)
    have hbefore := walk owner.decl suffix htail hinTail hlast
    rw [hresolve, hlastRead] at hbefore
    have hframe := st.activeGroup_frame_covers_reservation e.graph0_eq e.graph_eq hcomp hrun
      hactive hrank hnorm hlabels hcoord e.checked hcluster hu hgroup hdecl.symm
    exact Int.le_trans htargetRight (Int.le_trans hbefore hframe.2)

private theorem member_rank_band_lower {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cand cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cand labels orderOptions =
      .ok (cg, run)) {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd) :
    let r := (rk run.proper.rank v).toNat
    ∃ layer, run.layers[r]? = some layer ∧ run.top.getD r 0 ≤ run.ys.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, proxied, ⟨y, top⟩, ysMid, st⟩ :=
    componentRunR_stages hrun
  have hlayers : RouteImpl.layersOk run.proper run.layers = true := by
    rcases st.hLanes with ⟨_, hlanes⟩ | ⟨_, hlanes⟩
    · exact (RouteImpl.routeWithLanes_geometry hlanes).1
    · obtain ⟨_, hbase, _, _⟩ := routeWithLanesR_spec hlanes
      exact (RouteImpl.route_spec hbase).1
  have hvP := (List.getElem?_eq_some_iff.mp hv).1
  obtain ⟨layer, hlayer, hmem, hnonneg⟩ := (RouteImpl.layersOk_spec hlayers).2.2.2.1 v hvP
  let r := (rk run.proper.rank v).toNat
  have hrank : run.proper.rank = placed.rank := by
    rw [← st.hDrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel st.hProxy).2.1
  have hnodes : run.proper.nodes = proxied.nodes := by
    rw [← st.hDrop, OrderImpl.dropSynthetic_nodes]
  have hvC : v < placed.nodes.length := by
    rwa [hnodes, (proxyWidths_rel st.hProxy).2.2.1] at hvP
  have hvPlaced : placed.nodes[v]? = some placed.nodes[v] := List.getElem?_eq_getElem hvC
  obtain ⟨hyLen, htopLen⟩ := CoordsImpl.rankCoordsWith_length st.hYt
  have hvY : v < y.length := by rwa [hyLen]
  have hrTop : r < top.length := by
    rw [htopLen]
    exact (List.getElem?_eq_some_iff.mp hlayer).1
  have hr : rk placed.rank v = (r : Int) := by
    rw [← hrank]
    exact (Int.toNat_of_nonneg hnonneg).symm
  have hbefore := proxyYs_getD placed run.layers top y hvPlaced hvY
  have hrIdx : (rk placed.rank v).toNat = r := by rw [← hrank] <;> rfl
  have hlo := (rankAxis_node_in_band (r := r) st.hYt hlayer hmem hvC hr).1
  have hh := CoordsImpl.layerHeight_nonneg placed (run.layers.getD r [])
  simp only [hrIdx] at hbefore
  have hmid : top.getD r 0 ≤ ysMid.getD v 0 := by
    rw [← st.hYsMid, hbefore]
    split
    · exact Int.le_refl _
    · split
      · omega
      · exact hlo
  have hmidLen : ysMid.length = placed.nodes.length := by
    rw [← st.hYsMid]
    simpa only [proxyYs, List.length_map, List.length_zipIdx] using hyLen
  obtain ⟨_, shifts, _, _, _, _, htopShift, hyShift⟩ :=
    (runHooksShift_exact P exactIds inp cg labels).shifts placed run.layers ysMid top
      run.ys run.top st.hReserve
  have hys := hyShift v (by rwa [hmidLen])
  change run.ys.getD v 0 = ysMid.getD v 0 + shifts.getD (rk placed.rank v).toNat 0 at hys
  rw [hrIdx] at hys
  refine ⟨layer, hlayer, ?_⟩
  change run.top.getD r 0 ≤ run.ys.getD v 0
  rw [htopShift r hrTop, hys]
  exact Int.add_le_add_right hmid _

private theorem active_earlier_bottom_le_frame_top
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
    {u v : Nat} {owner target : Node}
    (hu : cg.nodes[u]? = some owner) (hgroup : owner.border = -2)
    (hv : cg.nodes[v]? = some target) (hplain : target.border = 0)
    (hearlier : (rk run.proper.rank v).toNat < (rk run.proper.rank u).toNat) :
    (frameRect e.params cg run v).y + (frameRect e.params cg run v).h ≤
      (frameRect e.params cg run u).y := by
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes : cg.nodes = (componentCandidate e.graph comp index).nodes := by
    rw [rankEquivalentR_nodes_eq hrank, componentCandidate_nodes] <;> rfl
  have huExact : (componentCandidate e.graph comp index).nodes[u]? = some owner := by
    rwa [← hnodes]
  obtain ⟨_, _, hownerPath⟩ := X_cg_group_box e.graph0_eq e.graph_eq huExact hgroup
  obtain ⟨_, actual, _, ha, _, _, _, _, _, hactualPath, _⟩ :=
    componentRunR_active_marker_records hrun hactive hu (Or.inl hgroup)
  have hownerMem : actual.node.clusterPath.contains owner.decl = true := by
    rw [hactualPath, hownerPath]
    exact List.contains_iff_mem.mpr (by simp)
  have hmem := fbs_groupMemberRects_mem (cg := cg) ha hownerMem
  have hnonempty : groupMemberRects cg run owner.decl ≠ [] := by
    intro hnone
    rw [hnone] at hmem
    cases hmem
  obtain ⟨_, _, _, _, _, _, _, hwindow⟩ :=
    activeCandidateOriginalFrameRankWindow e hwf hfp hcomp hrun hactive hu hgroup
  obtain ⟨hband, hsep⟩ := componentRunR_plain_rank_bands hrun
  obtain ⟨targetLayer, ht, _, _, htargetBottom⟩ := hband hv hplain
  have hall : ∀ r ∈ groupMemberRects cg run owner.decl,
      (frameRect e.params cg run v).y + (frameRect e.params cg run v).h ≤ r.y := by
    intro r hr
    obtain ⟨j, n, hj, hpath, rfl⟩ := fbs_groupMemberRects_spec hr
    obtain ⟨_, _, _, _, hkey, _, hkeyPath, _, hlo, _⟩ :=
      activeFrameContributorRankSources e hcomp hrun hactive hj hpath
    have htopRank := Int.le_trans (hwindow hkey hkeyPath).1 hlo
    have hjRank : (rk run.proper.rank v).toNat < (rk run.proper.rank j).toNat := by omega
    obtain ⟨layer, hl, hy⟩ := member_rank_band_lower (exactIds := exactIds) hrun hj
    change (frameRect e.params cg run v).y + (frameRect e.params cg run v).h ≤ run.ys.getD j 0
    exact Int.le_trans htargetBottom (Int.le_trans (hsep hjRank ht hl) hy)
  have hmin := boundsOf_minY_ge_of_all hnonempty hall
  rw [frameRect_group_span hu hgroup]
  exact hmin

def R7_SelectedActiveGroupLoop {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b) : Prop :=
  pair.edge.tail = pair.edge.head ∧
  ∃ (s : RegionSpec) (owner target : Node),
    r7Eff idSets o execution.params execution.lines pair.rs = some s ∧
    pair.cg.nodes[pair.edge.tail]? = some owner ∧ owner.border = -2 ∧
    pair.cg.nodes[pair.target]? = some target ∧ target.border = 0 ∧
    (owner.decl ∈ target.clusterPath ∨
      (rk pair.run.proper.rank pair.target).toNat < (rk pair.run.proper.rank pair.edge.tail).toNat)

theorem r7Selected_activeGroupLoop_footprint_miss {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_SelectedRoutePair execution l b) (hcase : R7_SelectedActiveGroupLoop pair) :
    ¬ (loopFootprintExt pair.cg pair.run execution.measured pair.edge.tail).meetsInterior
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  obtain ⟨_, s, owner, target, hs, hu, hgroup, hv, hplain, hbranch⟩ := hcase
  have hresolve := componentTrialR_selected_regions pair.candidate pair.regions_eq
  change newComponentRegions (r7Eff idSets o execution.params execution.lines pair.rs)
    execution.params inp
    (componentCandidateR (r7Eff idSets o execution.params execution.lines pair.rs)
      execution.graph pair.part.1 pair.candidate) = .ok pair.rs at hresolve
  rw [hs] at hresolve
  have hsome : ∃ rm, pair.rs = some rm := by
    cases he : pair.rs with
    | none => simp [r7Eff, he] at hs
    | some rm => exact ⟨rm, rfl⟩
  obtain ⟨rm, hrm⟩ := hsome
  rw [hrm] at hresolve
  have hrun := pair.run_eq
  change componentRunR execution.params (exactDecls exactIds inp)
    (r7Eff idSets o execution.params execution.lines pair.rs) inp
    (componentCandidateR (r7Eff idSets o execution.params execution.lines pair.rs)
      execution.graph pair.part.1 pair.candidate) execution.measured
    (candidateOrder pair.candidate) = .ok (pair.cg, pair.run) at hrun
  rw [hs] at hrun
  have hframe := plain_frame_eq_boxRect execution.params pair.cg pair.run pair.target
    pair.target_size (by simp [List.getD_eq_getElem?_getD, hv, hplain])
  rw [← hframe]
  rcases hbranch with hdesc | hearlier
  · have hright := active_descendant_right execution hwf hfp pair.comp_mem hrun hresolve
      hu hgroup hv hplain hdesc
    exact rect_disjoint_of_x (Or.inr hright)
  · have htop := active_earlier_bottom_le_frame_top execution hwf hfp pair.comp_mem hrun hresolve
      hu hgroup hv hplain hearlier
    exact rect_disjoint_of_y (Or.inr htop)

private theorem selected_activeGroupLoop_label_miss {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_SelectedRoutePair execution l b) (hcase : R7_SelectedActiveGroupLoop pair) :
    ¬ pair.rect.meetsInterior (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  have hloop := hcase.1
  have hfoot := r7Selected_activeGroupLoop_footprint_miss hwf hfp pair hcase
  have hslot : 0 ≤ pair.cg.slot := by
    rw [r7ComponentRun_slot_of_scene execution (comp := pair.part.1)
      (candidate := pair.candidate) pair.run_eq]
    have hpos := componentRunR_slot_pos pair.run_eq
    omega
  have hmeasured := execution.measured_nonnegR
  have henv := pair.envelope_eq
  unfold labelEnvelope at henv
  obtain ⟨_, _, hplacement⟩ := Option.bind_eq_some_iff.mp henv
  have hsame : (pair.edge.tail == pair.edge.head) = true := by simp [hloop]
  have hcontain : (loopFootprintExt pair.cg pair.run execution.measured pair.edge.tail).Contained
      pair.envelope := by
    cases he : pair.run.exact.contains pair.edge.tail with
    | false =>
      simp only [hsame, he] at hplacement
      exact X_loopEnvelope_containedExt hslot hmeasured he pair.edge_eq hloop
        (Option.some.inj hplacement).symm
    | true =>
      simp only [hsame, he] at hplacement
      exact X_loopExactEnvelope_containedExt hslot hmeasured pair.edge_eq hloop
        (Option.some.inj hplacement).symm he
  exact Elegant.Layered.loop_branch_clear pair.edge_eq hloop pair.envelope_eq hslot hmeasured
    (List.of_mem_zip pair.stack).2 (Elegant.Layered.not_meetsInterior_of_contained hcontain hfoot)

theorem r7Selected_activeGroupLoop_xgap {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_SelectedRoutePair execution l b) (hcase : R7_SelectedActiveGroupLoop pair) :
    R7_OverlapRowsXGap pair.rect (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  have hclear := selected_activeGroupLoop_label_miss hwf hfp pair hcase
  unfold R7_OverlapRowsXGap Rect.meetsInterior at *
  intro hy hleft hright
  omega

theorem r7Selected_activeGroupLoop_scene_miss {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_SelectedRoutePair execution l b) (hcase : R7_SelectedActiveGroupLoop pair) :
    ¬ l.rect.meetsInterior b.rect := by
  rw [pair.label_rect, pair.box_rect]
  unfold r7SelectedTransport
  exact not_meetsInterior_transport (selected_activeGroupLoop_label_miss hwf hfp pair hcase)

end Elegant.Layered.PipelineImpl

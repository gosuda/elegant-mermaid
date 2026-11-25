import Elegant.Layered.RegionC7SelectedGroupOwnerLoops
import Elegant.Layered.RegionC5NonexactLoopHeight

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

elab "exteriorResolvedTables%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC8aGroupPlain
    `Elegant.Layered.PipelineImpl.gp_resolved_tables))

elab "exteriorClusterSources%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC8aGroupPlain
    `Elegant.Layered.PipelineImpl.gp_candidate_cluster_sources))

elab "exteriorParentIndex%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC8aGroupPlain
    `Elegant.Layered.PipelineImpl.gp_parentGroup_table))

elab "exteriorPathFork%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC8aGroupPlain
    `Elegant.Layered.PipelineImpl.gp_path_fork))

private theorem allocation_loopWidth_at {rm : ComponentRegions} {g : Nat} {c : RegionCluster}
    (hc : rm.clusters[g]? = some c) (cg : Graph) (p : Proper) (groups : List Nat)
    (labelWidths xs : List Int) :
    (newRegionBuckets rm cg p groups labelWidths xs).loopWidth.getD g 0 = (c.extent : Int) := by
  let write (widths : List Int) (q : RegionCluster × Nat) :=
    setAt widths q.2 (q.1.extent : Int)
  have write_length (widths : List Int) (i : Nat) (a : Int) :
      (setAt widths i a).length = widths.length := by
    induction widths generalizing i with
    | nil => rfl
    | cons x xs ih => cases i <;> simp [setAt, ih]
  have write_other (widths : List Int) (i j : Nat) (a : Int) (hne : i ≠ j) :
      (setAt widths i a).getD j 0 = widths.getD j 0 := by
    induction widths generalizing i j with
    | nil => rfl
    | cons x xs ih =>
      cases i with
      | zero => cases j with
        | zero => exact (hne rfl).elim
        | succ j => rfl
      | succ i => cases j with
        | zero => rfl
        | succ j => exact ih i j (fun he => hne (congrArg Nat.succ he))
  have write_here (widths : List Int) (i : Nat) (a : Int) (hi : i < widths.length) :
      (setAt widths i a).getD i 0 = a := by
    induction widths generalizing i with
    | nil => simp at hi
    | cons x xs ih => cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using hi)
  have foldRead (rows : List (RegionCluster × Nat)) (widths : List Int)
      (hlen : g < widths.length)
      (hkeys : ∀ q ∈ rows, rm.clusters[q.2]? = some q.1) :
      (rows.foldl write widths).getD g 0 =
        if (c, g) ∈ rows then (c.extent : Int) else widths.getD g 0 := by
    induction rows generalizing widths with
    | nil => simp
    | cons q rows ih =>
      rw [List.foldl_cons, ih (write widths q)
        (by simpa only [write, write_length] using hlen) (fun a ha => hkeys a (by simp [ha]))]
      by_cases hq : q.2 = g
      · have hread := hkeys q (by simp)
        rw [hq, hc] at hread
        have hrow : q = (c, g) := Prod.ext (Option.some.inj hread).symm hq
        subst q
        by_cases hm : (c, g) ∈ rows
        · simp [hm]
        · rw [ite_eq_right hm, ite_eq_left (List.mem_cons_self : (c, g) ∈ (c, g) :: rows)]
          exact write_here widths g (c.extent : Int) hlen
      · have hne : (c, g) ≠ q := fun he => hq (congrArg Prod.snd he.symm)
        simp only [List.mem_cons, hne, false_or, write, write_other widths _ _ _ hq]
  have hmem : (c, g) ∈ rm.clusters.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hc
  have hbound := (List.getElem?_eq_some_iff.mp hc).1
  change (rm.clusters.zipIdx.foldl write (List.replicate (rm.clusters.length + 1) 0)).getD g 0 = _
  rw [foldRead _ _ (by simp only [List.length_replicate]; omega)
    (fun q hq => List.mem_zipIdx_iff_getElem?.mp hq), ite_eq_left hmem]

private theorem active_cluster_extent {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {comp : List Nat}
    (hcomp : comp ∈ components e.graph) {s : RegionSpec} {candidate : Nat} {rm : ComponentRegions}
    (hactive : newComponentRegions (some s) e.params inp
      (componentCandidateR (some s) e.graph comp candidate) = .ok (some rm))
    {u g : Nat} {owner : Node} {c : RegionCluster}
    (hu : (componentCandidateR (some s) e.graph comp candidate).nodes[u]? = some owner)
    (hgroup : owner.border = -2) (hc : rm.clusters[g]? = some c) (hd : c.decl = owner.decl) :
    c.extent = owner.loopExtent := by
  have hm := List.mem_of_getElem? hc
  rw [(exteriorResolvedTables% hactive).1] at hm
  unfold clusterRows at hm
  obtain ⟨q, hq, hrow⟩ := List.mem_filterMap.mp hm
  dsimp only at hrow
  split at hrow
  · cases hrow
  · rename_i hb
    have htag : q.1.border = -2 := by simpa using hb
    have he := Option.some.inj hrow
    have hdq : q.1.decl = c.decl := congrArg RegionCluster.decl he
    have hExtent : q.1.loopExtent = c.extent := congrArg RegionCluster.extent he
    have hsource := (active_candidate_top_source e hcomp hu hgroup).2.1
    have hqSource := (active_candidate_top_source e hcomp
      (List.mem_zipIdx_iff_getElem?.mp hq) htag).2.1
    rw [hdq, hd, hsource] at hqSource
    exact hExtent.symm.trans (congrArg Node.loopExtent (Option.some.inj hqSource).symm)

private theorem active_group_footprint_width {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {comp : List Nat}
    (hcomp : comp ∈ components e.graph) {s : RegionSpec} {candidate : Nat}
    {cg : Graph} {run : Run}
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) e.graph comp candidate) e.measured
      (candidateOrder candidate) = .ok (cg, run))
    {u : Nat} {owner : Node} (huCand :
      (componentCandidateR (some s) e.graph comp candidate).nodes[u]? = some owner)
    (hu : cg.nodes[u]? = some owner) (hgroup : owner.border = -2) :
    (loopFootprintExt cg run e.measured u).w ≤ (owner.loopExtent : Int) := by
  obtain ⟨hkey, hglobal, source, hsource⟩ := active_candidate_top_source e hcomp huCand hgroup
  have hi := (List.getElem?_eq_some_iff.mp hglobal).1
  rw [exactGraph_length e.graph_eq] at hi
  let old := e.graph0.nodes[owner.decl]
  have hold : e.graph0.nodes[owner.decl]? = some old := List.getElem?_eq_getElem hi
  obtain ⟨now, hnow, hb, _, hd⟩ := exactGraph_node_key e.graph_eq hold
  have he : now = owner := Option.some.inj (hnow.symm.trans hglobal)
  subst now
  have holdGroup : old.border = -2 := hb.symm.trans hgroup
  obtain ⟨hdecl, effective, heffective, hrole, _⟩ :=
    measuredGraph_group_origin e.graph0_eq hold holdGroup
  have hsrc : inp.boxes[old.decl]? = some source := by rwa [hdecl]
  have hslot := r7ComponentRun_slot_of_scene e (comp := comp) (candidate := candidate) hrun
  obtain ⟨huComp, hkeyRead⟩ := List.getElem?_eq_some_iff.mp hkey
  have hsizes : loopSizes cg.edges e.measured u cg.slot =
      loopSizes e.graph0.edges e.measured owner.decl e.params.slot := by
    rw [componentRunR_loopSizes_eq hrun u cg.slot,
      componentCandidateR_loopSizes_preserved (some s) e.graph comp
        (components_nodup _ _ hcomp) candidate u huComp,
      hkeyRead, exactGraph_edges e.graph_eq, hslot]
  have hflag := rC5RunExact% hrun hu
  have hsize := rC5ExactGraphSize% e.graph_eq hold hglobal hsrc
  change (if run.exact.contains u then Loops.exactExtent else Loops.extent) cg.slot
    (loopSizes cg.edges e.measured u cg.slot) ≤ _
  rw [hsizes, hslot]
  by_cases hex : run.exact.contains u = true
  · have hexDecl : (exactDecls exactIds inp).contains old.decl = true := by
      rw [← hd]
      exact hflag.mp hex
    rw [ite_eq_left hexDecl, hdecl] at hsize
    simpa only [hex, ↓reduceIte] using hsize
  · have hexDecl : (exactDecls exactIds inp).contains old.decl = false :=
      Bool.eq_false_iff.mpr (fun h => hex (hflag.mpr (by rwa [hd])))
    have heq : owner = old := by
      simpa only [hexDecl, Bool.false_eq_true, ↓reduceIte] using hsize
    simp only [Bool.eq_false_iff.mpr hex, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨metric, measured, raw, titles, hm, hmeas, _, hlen, hprep, hraw⟩ :=
      rC5RawSize% e.graph0_eq
    have hMetric : metric = e.metric := Except.ok.inj (hm.symm.trans e.metric_eq)
    subst metric
    have hMeasured : measured = e.measured := Except.ok.inj (hmeas.symm.trans e.measured_eq)
    subst measured
    let boxes := inp.boxes.map fun box => if inp.fixedSizes.any (·.1 == box.id)
      then { box with role := .node } else box
    have heff : boxes[owner.decl]? = some effective := by simpa only [hdecl] using heffective
    have hrawLen : raw.nodes.length = boxes.length := by
      rw [hlen, boxLines_length e.lines_eq]
      simp only [boxes, List.length_map]
    have hbox := (List.getElem?_eq_some_iff.mp heff).1
    have hbefore : owner.decl < raw.nodes.length := by rwa [hrawLen]
    have hrawRecord := Compound.prepare_group_title_record boxes e.params.clusterPad titles raw
      hbefore heff hrole
    change e.graph0 = Compound.prepare boxes e.params.clusterPad titles raw at hprep
    have holdExtent : old.loopExtent = raw.nodes[owner.decl].loopExtent := by
      rw [← hprep, hold] at hrawRecord
      have hpreparedEq := Option.some.inj hrawRecord
      have hloopExtent := congrArg Node.loopExtent hpreparedEq
      exact hloopExtent
    have hRawSizes := prepare_loopSizes_preserved boxes e.params.clusterPad titles raw owner.decl
      hbox e.measured e.params.slot
    rw [congrArg Node.loopExtent heq, holdExtent, hprep, hRawSizes]
    exact (hraw (List.getElem?_eq_getElem hbefore)).1

private theorem active_exterior_slot_gap {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {s : RegionSpec} {candidate : Nat} {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) e.graph comp candidate) e.measured
      (candidateOrder candidate) = .ok (cg, run))
    (hactive : newComponentRegions (some s) e.params inp
      (componentCandidateR (some s) e.graph comp candidate) = .ok (some rm))
    {u v : Nat} {owner target : Node}
    (hu : cg.nodes[u]? = some owner) (hgroup : owner.border = -2)
    (hv : cg.nodes[v]? = some target) (hplain : target.border = 0)
    (hforeign : target.clusterPath.contains owner.decl = false) :
    let foot := loopFootprintExt cg run e.measured u
    let dst := frameRect e.params cg run v
    (foot.x + foot.w ≤ dst.x ∨ dst.x + dst.w ≤ foot.x) ∧
      let r := (rk run.proper.rank v).toNat
      ∃ layer, run.layers[r]? = some layer ∧ v ∈ layer ∧
        run.top.getD r 0 ≤ dst.y ∧
        dst.y + dst.h ≤ run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper layer := by
  let cand := componentCandidateR (some s) e.graph comp candidate
  obtain ⟨_, _, _, _, minimum, _, _, _, hrank, hnorm, hlabels, hcoord, hmin, _, ⟨st⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes : cg.nodes = cand.nodes := rankEquivalentR_nodes_eq hrank
  have huCand : cand.nodes[u]? = some owner := by rwa [← hnodes]
  have hvCand : cand.nodes[v]? = some target := by rwa [← hnodes]
  have huBase : (componentCandidate e.graph comp candidate).nodes[u]? = some owner := by
    rw [componentCandidate_nodes]
    exact huCand
  obtain ⟨_, _, hownerPath⟩ := X_cg_group_box e.graph0_eq e.graph_eq huBase hgroup
  obtain ⟨group, cluster, hgroupOf, hcluster, hdecl⟩ :=
    active_candidate_top_cluster hactive huCand hgroup
  obtain ⟨bucket, _, hownerOf, _, hplainLeft, hplainRight⟩ :=
    st.activePlain_frame_in_ownerBucket hrun hactive hrank hnorm hlabels hcoord hmin hv hplain
  have hlast : owner.clusterPath.getLast? = some owner.decl := by simp [hownerPath]
  have hownerOf' : (match owner.clusterPath.getLast? with
      | none => group = rm.clusters.length
      | some d => clusterOfDecl rm d = some group) := by rw [hlast]; exact hgroupOf
  have hrootedG := r8b_executed_endpoint_rooted e hwf hfp hcomp hactive st hmin huCand hownerOf'
  have hrootedT := r8b_executed_endpoint_rooted e hwf hfp hcomp hactive st hmin hvCand hownerOf
  let resolve := fun d => (clusterOfDecl rm d).getD rm.clusters.length
  let pl := st.placement
  let alloc := st.allocation
  have hplEq : pl = st.placement := rfl
  have hallocEq : alloc = st.allocation := rfl
  have hplLen : pl.rm.clusters.length = rm.clusters.length := by rw [hplEq, st.hPlacement]
  have hparents := activeRegion_parent_count hactive
  have hpaths := (st.group_paths hparents hmin).1
  have hginj := (r8b_executed_rooted_path_bounds st hparents hmin hrootedG).2
  have hfork : GroupPlainOwnerFork owner.clusterPath target.clusterPath := by
    apply exteriorPathFork% owner.clusterPath target.clusterPath
    rintro ⟨suffix, hs⟩
    have hm : owner.decl ∈ target.clusterPath := by rw [← hs, hownerPath]; simp
    have htrue := List.contains_iff_mem.mpr hm
    rw [hforeign] at htrue
    cases htrue
  have hgroupEnd : ((owner.clusterPath.map resolve).getLast?).getD pl.rm.clusters.length = group := by
    simp only [List.getLast?_map, hlast, Option.map_some, Option.getD_some, resolve, hgroupOf]
  have htargetEnd : ((target.clusterPath.map resolve).getLast?).getD pl.rm.clusters.length = bucket := by
    cases hl : target.clusterPath.getLast? with
    | none =>
      have hb : bucket = rm.clusters.length := by simpa only [hl] using hownerOf
      simpa only [List.getLast?_map, hl, Option.map_none, Option.getD_none, hplLen] using hb.symm
    | some d =>
      have hd : clusterOfDecl rm d = some bucket := by simpa only [hl] using hownerOf
      simp only [List.getLast?_map, hl, Option.map_some, Option.getD_some, resolve, hd]
  obtain ⟨common, branchG, hbranchG, htrailG, hbranches⟩ := groupPlain_common_path_branches
    (pl := pl) (resolve := resolve) hfork (by rwa [hplLen]) (by rwa [hplLen])
    (fun d hd _ _ he => r8b_executed_resolver_injective (hginj d hd) he)
  rw [hgroupEnd] at htrailG
  rw [htargetEnd] at hbranches
  have hchildBound {a c : Nat} (hc : c ∈ pl.children.getD a []) : c < pl.rm.clusters.length := by
    rw [hplLen]
    exact (hpaths a c hc).1
  obtain ⟨hownStage, hlaneStage, hloopStage⟩ := componentRunR_active_bucket_signs hrun st
  have hown (g : Nat) : 0 ≤ pl.buckets.widths.getD g 0 := by
    rw [hplEq]
    exact hownStage g
  have hlane (g : Nat) : 0 ≤ laneExtentOf pl.buckets e.params.slot g := by
    rw [hplEq]
    exact hlaneStage g
  have hloop (g : Nat) : 0 ≤ pl.buckets.loopWidth.getD g 0 := by
    rw [hplEq]
    exact hloopStage g
  have hpad := (checkedParams_sizing_nonneg e.checked).2.1
  have hborder := checkedParams_clusterBorderW_ge_one e.checked
  have hinset : 0 ≤ regionInsetOf e.params := by unfold regionInsetOf; omega
  have hrawWidths := reserveWidths_nonnegative hinset hown hlane hloop
  have hAllocation : allocatePl pl e.params st.before = .ok (alloc, st.shifted) := by
    rw [hplEq, hallocEq]
    exact st.hAllocation
  have hwidthEq : alloc.widths = reserveWidths pl e.params :=
    groupPlain_allocation_width_eq hAllocation
  have hwidths (g : Nat) : 0 ≤ alloc.widths.getD g 0 := by rw [hwidthEq]; exact hrawWidths g
  have horigin (g : Nat) : 0 ≤ pl.minimum.origins.getD g 0 := by
    rw [hplEq, st.hPlacement]
    change 0 ≤ minimum.origins.getD g 0
    rw [constrainR_origins hmin, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split
    · exact hinset
    · exact Int.le_refl _
  have hleftNonneg := groupPlain_allocation_lefts_nonneg hAllocation horigin hown hrawWidths
  have hsum (row : List Nat) : 0 ≤ (row.map fun j => alloc.widths.getD j 0).sum := by
    induction row with
    | nil => simp
    | cons j rest ih =>
      rw [List.map_cons, List.sum_cons]
      exact Int.add_nonneg (hwidths j) ih
  have hleft {g i child : Nat} (hg : g ≤ pl.rm.clusters.length)
      (hi : (pl.children.getD g [])[i]? = some child) :
      groupPlain_allocLeft alloc child = groupPlain_bucketRight pl e.params alloc g +
        (((pl.children.getD g []).take i).map fun j => alloc.widths.getD j 0).sum := by
    rw [hplLen] at hg
    have h := st.childBudget_left_from_allocation hactive hmin hg hi
    simpa only [hwidthEq, groupPlain_allocLeft, groupPlain_bucketRight, groupPlain_bucketLeft,
      hplLen, alloc, pl] using h
  have hroom (g : Nat) (hg : g < pl.rm.clusters.length) :
      2 * regionInsetOf e.params + pl.buckets.widths.getD g 0 +
        ((pl.children.getD g []).map fun j => alloc.widths.getD j 0).sum +
          laneExtentOf pl.buckets e.params.slot g ≤ alloc.widths.getD g 0 - pl.buckets.loopWidth.getD g 0 := by
    have hg' : g ≤ rm.clusters.length := Nat.le_of_lt (by rwa [hplLen] at hg)
    obtain ⟨_, _, ho, hf, hc⟩ := (st.reservation_order hparents hmin).2 g hg'
    rw [hwidthEq]
    exact reserveWidths_room_from_last_writes (pl := pl) (P := e.params) ho hg hf hc
  have hrealRoom (g : Nat) (hg : g < pl.rm.clusters.length) :
      regionInsetOf e.params + pl.buckets.widths.getD g 0 +
        ((pl.children.getD g []).map fun j => alloc.widths.getD j 0).sum ≤ alloc.widths.getD g 0 := by
    have hb := hroom g hg
    have hl := hlane g
    have hw := hloop g
    omega
  have trailBounds {base last : Nat} (htrail : GroupPlainAllocatedTrail pl base last)
      (hbase : base < pl.rm.clusters.length) :
      last < pl.rm.clusters.length ∧ groupPlain_allocLeft alloc base ≤ groupPlain_allocLeft alloc last ∧
        groupPlain_allocRight alloc last ≤ groupPlain_allocRight alloc base := by
    induction htrail with
    | here g => exact ⟨hbase, Int.le_refl _, Int.le_refl _⟩
    | @down parent child last hchild _ ih =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hchild
      have hb := groupPlain_child_slot_bounds hi hinset (hown parent) hwidths
        (hleft (Nat.le_of_lt hbase) hi)
        (by rw [ite_eq_right (Nat.ne_of_lt hbase)]; exact hrealRoom parent hbase)
      obtain ⟨hl, hlo, hhi⟩ := ih (hchildBound hchild)
      exact ⟨hl, Int.le_trans hb.1 hlo, Int.le_trans hhi hb.2⟩
  have hgroupLt : group < pl.rm.clusters.length := by rw [hplLen]; exact (List.getElem?_eq_some_iff.mp hcluster).1
  let left := groupPlain_allocLeft alloc group
  let right := groupPlain_allocRight alloc group - pl.buckets.loopWidth.getD group 0
  have hgapRoom : left + e.params.clusterBorderW ≤ right := by
    have hr := hroom group hgroupLt
    have ho := hown group
    have hl := hlane group
    have hs := hsum (pl.children.getD group [])
    unfold regionInsetOf at hr
    dsimp only [right, groupPlain_allocRight]
    omega
  have hright0 : 0 ≤ right := by have hl := hleftNonneg group; change 0 ≤ left at hl; omega
  have hframeLo := (st.activeGroup_frame_covers_reservation e.graph0_eq e.graph_eq hcomp
    hrun hactive hrank hnorm hlabels hcoord e.checked hcluster hu hgroup hdecl.symm).2
  rw [← hwidthEq] at hframeLo
  change right ≤ (frameRect e.params cg run u).x + (frameRect e.params cg run u).w at hframeLo
  have hframeHi := activeFrame_right_of_side_centers (P := e.params) hu hgroup
    (by omega) hright0 hgapRoom (fun hi hb hp => by
      have hout := st.activeChild_side_centers e.graph0_eq e.graph_eq hcomp hrun hactive
        hrank hnorm hlabels hcoord hcluster hi hb (hp.trans (congrArg some hdecl.symm))
      rw [← hwidthEq] at hout
      simpa only [left, right, groupPlain_allocLeft, groupPlain_allocRight, pl, alloc] using hout)
  have hw := active_group_footprint_width e hcomp hrun huCand hu hgroup
  have hbucketWidth : pl.buckets.loopWidth.getD group 0 = (owner.loopExtent : Int) := by
    have he := active_cluster_extent e hcomp hactive huCand hgroup hcluster hdecl
    rw [hplEq, st.hPlacement]
    change (newRegionBuckets rm cg _ _ _ _).loopWidth.getD group 0 = _
    rw [allocation_loopWidth_at hcluster, he]
  let foot := loopFootprintExt cg run e.measured u
  have hfootLo : left ≤ foot.x := by
    change left + e.params.clusterBorderW ≤ right at hgapRoom
    change left ≤ (frameRect e.params cg run u).x + (frameRect e.params cg run u).w
    omega
  have hfootHi : foot.x + foot.w ≤ groupPlain_allocRight alloc group := by
    change (frameRect e.params cg run u).x + (frameRect e.params cg run u).w + foot.w ≤ _
    change foot.w ≤ (owner.loopExtent : Int) at hw
    change (frameRect e.params cg run u).x + (frameRect e.params cg run u).w ≤
      groupPlain_allocRight alloc group - pl.buckets.loopWidth.getD group 0 at hframeHi
    omega
  have hgBounds := (trailBounds htrailG (hchildBound hbranchG)).2
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hbranchG
  have hcommon : common ≤ pl.rm.clusters.length := by
    obtain ⟨hbound, hpar⟩ := hpaths common branchG hbranchG
    let row := rm.clusters[branchG]
    have hrow : rm.clusters[branchG]? = some row := List.getElem?_eq_getElem hbound
    obtain ⟨hrows, hparentsTable⟩ := exteriorResolvedTables% hactive
    obtain ⟨_, hsources⟩ := exteriorClusterSources% e hcomp hrows
    obtain ⟨src, _, hsrc, _, _, _⟩ := hsources row (List.mem_of_getElem? hrow)
    rw [hplLen, ← hpar, exteriorParentIndex% hparentsTable hrow hsrc]
    split
    · exact Nat.le_refl _
    · cases hx : rm.clusters.findIdx? (fun c => c.id == src.parent) with
      | none => exact Nat.le_refl _
      | some pos => exact Nat.le_of_lt (List.findIdx?_eq_some_iff_getElem.mp hx).1
  refine ⟨?_, (componentRunR_plain_rank_bands hrun).1 hv hplain⟩
  rcases hbranches with he | ⟨branchT, hbranchT, hne, htrailT⟩
  · rw [he] at hplainRight
    have hbefore := groupPlain_bucket_before_child hwidths (hleft hcommon hi)
    exact Or.inr (Int.le_trans hplainRight (Int.le_trans hbefore (Int.le_trans hgBounds.1 hfootLo)))
  · obtain ⟨htLt, htLo, htHi⟩ := trailBounds htrailT (hchildBound hbranchT)
    have hr := hrealRoom bucket htLt
    have hs := hsum (pl.children.getD bucket [])
    obtain ⟨hlo, hhi⟩ := groupPlain_bucket_in_owner (pl := pl) (P := e.params)
      (alloc := alloc) (owner := bucket) hinset (by omega)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hbranchT
    rcases groupPlain_sibling_slot_gap hi hj hne hwidths (hleft hcommon hi) (hleft hcommon hj) with h | h
    · exact Or.inl (Int.le_trans hfootHi (Int.le_trans hgBounds.2 (Int.le_trans h
        (Int.le_trans htLo (Int.le_trans hlo hplainLeft)))))
    · exact Or.inr (Int.le_trans hplainRight (Int.le_trans hhi (Int.le_trans htHi
        (Int.le_trans h (Int.le_trans hgBounds.1 hfootLo)))))

/-- A selected active group loop against an exterior plain target no earlier than the owner. -/
def R7_SelectedActiveExteriorGroupLoop {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b) : Prop :=
  pair.edge.tail = pair.edge.head ∧
  ∃ (s : RegionSpec) (owner target : Node),
    r7Eff idSets o execution.params execution.lines pair.rs = some s ∧
    pair.cg.nodes[pair.edge.tail]? = some owner ∧ owner.border = -2 ∧
    pair.cg.nodes[pair.target]? = some target ∧ target.border = 0 ∧
    target.clusterPath.contains owner.decl = false ∧
    (rk pair.run.proper.rank pair.edge.tail).toNat ≤ (rk pair.run.proper.rank pair.target).toNat

theorem r7Selected_activeExteriorGroupLoop_footprint_miss {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_SelectedRoutePair execution l b) (hcase : R7_SelectedActiveExteriorGroupLoop pair) :
    ¬ (loopFootprintExt pair.cg pair.run execution.measured pair.edge.tail).meetsInterior
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  obtain ⟨_, s, owner, target, hs, hu, hgroup, hv, hplain, hforeign, _⟩ := hcase
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
  exact rect_disjoint_of_x
    (active_exterior_slot_gap execution hwf hfp pair.comp_mem hrun hresolve hu hgroup hv hplain hforeign).1

private theorem activeExteriorGroupLoop_label_miss {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_SelectedRoutePair execution l b) (hcase : R7_SelectedActiveExteriorGroupLoop pair) :
    ¬ pair.rect.meetsInterior (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  have hloop := hcase.1
  have hfoot := r7Selected_activeExteriorGroupLoop_footprint_miss hwf hfp pair hcase
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

theorem r7Selected_activeExteriorGroupLoop_xgap {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_SelectedRoutePair execution l b) (hcase : R7_SelectedActiveExteriorGroupLoop pair) :
    R7_OverlapRowsXGap pair.rect (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  have hclear := activeExteriorGroupLoop_label_miss hwf hfp pair hcase
  unfold R7_OverlapRowsXGap Rect.meetsInterior at *
  intro hy hleft hright
  omega

theorem r7Selected_activeExteriorGroupLoop_scene_miss {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_SelectedRoutePair execution l b) (hcase : R7_SelectedActiveExteriorGroupLoop pair) :
    ¬ l.rect.meetsInterior b.rect := by
  rw [pair.label_rect, pair.box_rect]
  unfold r7SelectedTransport
  exact not_meetsInterior_transport (activeExteriorGroupLoop_label_miss hwf hfp pair hcase)

end Elegant.Layered.PipelineImpl

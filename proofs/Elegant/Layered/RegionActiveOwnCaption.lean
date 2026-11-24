import Elegant.Layered.RegionForeignPartCaptions
import Elegant.Layered.RegionFallbackAncestorFrameSides
import Elegant.Layered.RegionC5ActiveSelected
import Elegant.Layered.BottomClearanceClosure
import Elegant.Layered.FrameClearanceBottomFacts
import Elegant.Layered.ExactCaptionSelfProof
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.ParentContainmentFacts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem ownCaption_emission {P : Params} {cg : Graph} {run : Run}
    {i : Nat} {raw : Rect} (hm : (i, raw) ∈ componentTitles P cg run) :
    ∃ (owner : Node) (t : Nat) (title : ProperNode),
      cg.nodes[i]? = some owner ∧ owner.border = -2 ∧
      run.proper.nodes[t]? = some title ∧ title.node.border = 3 ∧
      title.node.clusterPath = owner.clusterPath ∧
      raw.x = run.xs.getD t 0 - Int.fdiv title.node.w 2 ∧ raw.w = owner.w := by
  unfold componentTitles at hm
  obtain ⟨top, htop, hemit⟩ := List.mem_filterMap.mp hm
  dsimp only at hemit
  by_cases hb : top.1.border = -2
  · cases hfind : run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
    | none => simp [hb, hfind] at hemit
    | some title =>
      simp [hb, hfind] at hemit
      obtain ⟨hi, hrect⟩ := hemit
      have ht := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfind)
      have hkeys : title.1.node.border = 3 ∧ title.1.node.clusterPath = top.1.clusterPath := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hfind
      have ho : cg.nodes[i]? = some top.1 := by
        rw [← hi]
        exact List.mem_zipIdx_iff_getElem?.mp htop
      exact ⟨top.1, title.2, title.1, ho, hb, ht, hkeys.1, hkeys.2,
        (congrArg Rect.x hrect).symm, (congrArg Rect.w hrect).symm⟩
  · simp [hb] at hemit

private theorem ownCaption_resolved_rows {P : Params} {s : RegionSpec} {inp : Input}
    {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    rm.clusters = clusterRows inp s cg := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bind_ok' h
    split at h
    · cases h
    · exact (congrArg ComponentRegions.clusters (Option.some.inj (Except.ok.inj h))).symm

private def ownCaptionClusterRow (inp : Input) (s : RegionSpec) (cg : Graph)
    (q : Node × Nat) : RegionCluster :=
  { id := boxId inp q.1.decl, decl := q.1.decl,
    node := match cg.nodes.zipIdx.find? (fun b => b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2,
    top := q.2,
    bottom := match cg.nodes.zipIdx.find? (fun b => b.1.border == 2 && b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2,
    titleW := q.1.w, titleH := (s.titles.getD q.1.decl (0, 0)).2, extent := q.1.loopExtent }

private theorem ownCaption_cluster_get {inp : Input} {s : RegionSpec}
    {cg : Graph} {rm : ComponentRegions} (hrows : rm.clusters = clusterRows inp s cg)
    {i : Nat} {owner : Node} (ho : cg.nodes[i]? = some owner) (hb : owner.border = -2) :
    ∃ (g : Nat) (row : RegionCluster), rm.clusters[g]? = some row ∧
      row.decl = owner.decl ∧ row.titleW = owner.w := by
  have hm : ownCaptionClusterRow inp s cg (owner, i) ∈ rm.clusters := by
    rw [hrows]
    unfold clusterRows
    refine List.mem_filterMap.mpr ⟨(owner, i), List.mem_zipIdx_iff_getElem?.mpr ho, ?_⟩
    change (if owner.border != -2 then none else some (ownCaptionClusterRow inp s cg (owner, i))) =
      some (ownCaptionClusterRow inp s cg (owner, i))
    simp [hb]
  obtain ⟨g, hg⟩ := List.mem_iff_getElem?.mp hm
  exact ⟨g, _, hg, rfl, rfl⟩

private theorem ownCaption_cluster_bounds {inp : Input} {s : RegionSpec} {cg : Graph}
    {row : RegionCluster} (hm : row ∈ clusterRows inp s cg) :
    row.top < cg.nodes.length ∧ row.bottom < cg.nodes.length := by
  unfold clusterRows at hm
  obtain ⟨q, hq, hrow⟩ := List.mem_filterMap.mp hm
  change (if q.1.border != -2 then none else some (ownCaptionClusterRow inp s cg q)) =
    some row at hrow
  split at hrow
  · cases hrow
  · rw [← Option.some.inj hrow]
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

private theorem ownCaption_coordinate_copy {P : Params} {exact : List Nat}
    {s : RegionSpec} {cg : Graph} {normalized labeled : Proper} {ranks : List Int}
    {labels : List MeasuredLabel} (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    (hshape : ∀ {i : Nat} {n : Node}, cg.nodes[i]? = some n → n.border ≠ 3)
    {i : Nat} {n : ProperNode}
    (hn : (coordinateGraphR P exact (some s) labeled).nodes[i]? = some n)
    (hb : n.node.border = 3) :
    labeled.nodes.length ≤ i ∧ ∃ (j : Nat) (old : Node), cg.nodes[j]? = some old ∧
      old.border = -2 ∧ n.node.clusterPath = old.clusterPath ∧
      n.node.h = (s.titles.getD old.decl (0, 0)).2 + P.clusterPad ∧
      rk (coordinateGraphR P exact (some s) labeled).rank i =
        rk (coordinateGraphR P exact (some s) labeled).rank j := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  let copy (q : ProperNode × Nat) : ProperNode :=
    let height := (s.titles.getD q.1.node.decl (0, 0)).2 + P.clusterPad
    { q.1 with node := { q.1.node with border := 3, loopExtent := 0, h := height } }
  have hkeys := addLabelNodes_keys _ _ _ (normalize_keys hnorm) hlabels
  change (materializeDummyPaths (clearProxyExtents bordered)).nodes[i]? = some n at hn
  obtain ⟨before, hbefore, _, hbBefore, _, hreal⟩ := materialize_lookup _ hn
  rw [clearProxyExtents_nodes, List.getElem?_map] at hbefore
  obtain ⟨t, ht, hclear⟩ := Option.map_eq_some_iff.mp hbefore
  have htB : t.node.border = 3 := (clearF_keys t).2.1.symm.trans
    ((congrArg (fun q : ProperNode => q.node.border) hclear).trans (hbBefore.symm.trans hb))
  obtain ⟨extra, hbordered, hextra⟩ := addClusterBorders_extra titled P.clusterBorderW
  rw [show bordered.nodes = titled.nodes ++ extra from hbordered] at ht
  have hiT : i < titled.nodes.length := by
    apply Classical.byContradiction
    intro h
    rw [List.getElem?_append_right (Nat.le_of_not_gt h)] at ht
    rcases (hextra t (List.mem_of_getElem? ht)).2 with h | h <;> omega
  rw [List.getElem?_append_left hiT] at ht
  change (sized.nodes.map titleF ++ (titleNodes sized).map copy)[i]? = some t at ht
  have hsizedLen : sized.nodes.length = labeled.nodes.length := sizeProperPortsX_length _ _ _
  have hi : sized.nodes.length ≤ i := by
    apply Classical.byContradiction
    intro h
    rw [List.getElem?_append_left (by simpa only [List.length_map] using Nat.lt_of_not_ge h),
      List.getElem?_map] at ht
    obtain ⟨sz, hsz, rfl⟩ := Option.map_eq_some_iff.mp ht
    obtain ⟨l, hl, _, hborder, _⟩ := X_sizeProperPorts_node_origin P exact labeled hsz
    rw [(titleF_keys sz).2.1, hborder] at htB
    rcases hkeys i l hl with ⟨old, ho, _, he, _⟩ | ⟨_, he, _⟩
    · exact hshape ho (he.symm.trans htB)
    · omega
  rw [List.getElem?_append_right (by simpa only [List.length_map] using hi),
    List.getElem?_map] at ht
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp ht
  obtain ⟨hsz, htop⟩ := titleNodes_spec hq
  obtain ⟨l, hl, _, hBorder, _⟩ := X_sizeProperPorts_node_origin P exact labeled hsz
  have hlTop := hBorder.symm.trans htop
  rcases hkeys q.2 l hl with ⟨old, hold, _, hOldB, _⟩ | ⟨_, hzero, _⟩
  · have htopOld := hOldB.symm.trans hlTop
    have hsource : labeled.nodes[q.2]? = some ⟨old, false, none, false⟩ :=
      addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hold) rfl
    have hszSource : sized.nodes[q.2]? = some ⟨old, false, none, false⟩ := by
      simp [sized, sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hsource, htopOld]
    have hqEq : q.1 = ⟨old, false, none, false⟩ := Option.some.inj (hsz.symm.trans hszSource)
    have hclear' : before = copy q := by simpa [clearF, copy] using hclear.symm
    have hcopyReal : (copy q).dummy = false := congrArg ProperNode.dummy hqEq
    have hnEq : n = copy q :=
      (hreal ((congrArg ProperNode.dummy hclear').trans hcopyReal)).trans hclear'
    refine ⟨by simpa only [hsizedLen] using hi, q.2, old, hold, htopOld, ?_, ?_, ?_⟩
    · rw [hnEq, show (copy q).node.clusterPath = q.1.node.clusterPath from rfl, hqEq]
    · rw [hnEq, show (copy q).node.h = (s.titles.getD q.1.node.decl (0, 0)).2 +
        P.clusterPad from rfl, hqEq]
    · have ha : labeled.nodes.length = labeled.rank.length := by
        rw [(Labels.addLabelNodes_metadata hlabels).2.1, ← addLabelNodes_node_length hlabels]
        exact (normalize_node_rank_alignment hnorm).1
      have hszRank : sized.rank = labeled.rank := rfl
      have hiRank : sized.rank.length ≤ i := by rw [hszRank, ← ha, ← hsizedLen]; exact hi
      have hoffset : i - sized.rank.length = i - (sized.nodes.map titleF).length := by
        rw [hszRank, ← ha, ← hsizedLen, List.length_map]
      have htCopy : titled.rank[i]? = some (rk labeled.rank q.2) := by
        change (sized.rank ++ (titleNodes sized).map (fun entry => rk sized.rank entry.2))[i]? = _
        rw [List.getElem?_append_right hiRank, hoffset, List.getElem?_map, hq, Option.map_some,
          hszRank]
      obtain ⟨extraRanks, hborderRanks⟩ := addClusterBorders_rank_prefix titled P.clusterBorderW
      have hcCopy : (coordinateGraphR P exact (some s) labeled).rank[i]? =
          some (rk labeled.rank q.2) := by
        change bordered.rank[i]? = _
        rw [show bordered.rank = titled.rank ++ extraRanks from hborderRanks,
          List.getElem?_append_left (List.getElem?_eq_some_iff.mp htCopy).1]
        exact htCopy
      obtain ⟨tail, hprefix⟩ := (coordinateGraphR_label_prefix P exact (some s) labeled).2
      have hj : q.2 < labeled.rank.length := by
        rw [← ha]
        exact (List.getElem?_eq_some_iff.mp hl).1
      calc
        rk (coordinateGraphR P exact (some s) labeled).rank i = rk labeled.rank q.2 := by
          simp only [rk, List.getD_eq_getElem?_getD, hcCopy, Option.getD_some]
        _ = rk (coordinateGraphR P exact (some s) labeled).rank q.2 := by
          rw [hprefix, NormalizeImpl.rk_append_left hj]
  · omega

private theorem ownCaption_ports_rank {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper}
    (h : reservedPortsR pl cg labels xs = .ok (ys, placed)) : placed.rank = pl.p.rank := by
  unfold reservedPortsR at h
  obtain ⟨_, _, hret⟩ := bind_ok' h
  exact (congrArg (fun q : List Int × Proper => q.2.rank) (Except.ok.inj hret)).symm

private theorem ownCaption_allocation_widths {pl : RegionPlacement} {P : Params}
    {xs moved : List Int} {allocation : RegionAllocation}
    (h : allocatePl pl P xs = .ok (allocation, moved)) :
    allocation.widths = reserveWidths pl P := by
  unfold allocatePl at h
  obtain ⟨_, _, hret⟩ := bind_ok' h
  exact (congrArg (fun q : RegionAllocation × List Int => q.1.widths) (Except.ok.inj hret)).symm

private theorem ownCaption_center_strict {left span rawW width inset : Int}
    (hwidth : 0 ≤ width) (hfit : width ≤ rawW) (hinset : 0 < inset)
    (hroom : rawW + 2 * inset ≤ span) :
    let x := left + Int.tdiv span 2 - Int.fdiv rawW 2
    left < x ∧ x + width < left + span := by
  have hs : 0 ≤ span := by omega
  dsimp only
  rw [Int.tdiv_eq_ediv_of_nonneg (b := 2) hs,
    Int.fdiv_eq_ediv_of_nonneg rawW (b := 2) (by decide)]
  constructor <;> omega

private def ownCaptionBottom (cg : Graph) (top : Node) : Option (Node × Nat) :=
  cg.nodes.zipIdx.find? fun q => q.1.border == 2 && q.1.decl == top.decl

private theorem ownCaption_bottom_rank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {s : RegionSpec} {index : Nat} {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hrun : componentRunR e.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) e.graph comp index) e.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) e.params inp
      (componentCandidateR (some s) e.graph comp index) = .ok (some rm))
    {i : Nat} {owner : Node} (ho : cg.nodes[i]? = some owner) (howner : owner.border = -2) :
    ∃ (b : Nat) (bottom : Node), cg.nodes[b]? = some bottom ∧ bottom.border = 2 ∧
      bottom.clusterPath.contains owner.decl = true ∧ rk run.proper.rank i < rk run.proper.rank b := by
  let g := componentCandidateR (some s) e.graph comp index
  let c := componentCandidate e.graph comp index
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes : cg.nodes = g.nodes := rankEquivalentR_nodes_eq hrank
  have hcnodes : c.nodes = g.nodes := by
    dsimp [c]
    rw [componentCandidate_nodes]
    rfl
  have hget {j : Nat} {n : Node} (h : g.nodes[j]? = some n) : c.nodes[j]? = some n := by
    rwa [hcnodes]
  have hlines := boxLines_length e.lines_eq
  have bottomExists {j : Nat} {n : Node} (hj : g.nodes[j]? = some n) (hb : n.border = -2) :
      ∃ p, ownCaptionBottom g n = some p := by
    unfold ownCaptionBottom
    rw [← hcnodes]
    exact X_componentRun_cg_bottom_find e.graph0_eq e.graph_eq hlines hcomp (hget hj) hb
  have step {a b : Nat} (he : (⟨a, b, 1, 0, false⟩ : Edge) ∈ Compound.constraints g) :
      rk run.proper.rank a < rk run.proper.rank b := by
    obtain ⟨ha, hb⟩ := constraints_bounded g _ he
    have h := componentRunR_compound_feasible hrun he ha hb
    change 1 ≤ rk run.proper.rank b - rk run.proper.rank a at h
    omega
  have axisWidth : ∀ (fuel a : Nat) (an : Node) (ab : Node × Nat),
      g.nodes[a]? = some an → an.border = -2 → ownCaptionBottom g an = some ab →
      e.lines.length + 2 - an.clusterPath.length = fuel →
      rk run.proper.rank a < rk run.proper.rank ab.2 := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro a an ab ha hta hab hfuel
      let leaves := g.nodes.zipIdx.filter fun m => m.1.border == 0 && m.1.clusterPath.contains an.decl
      let children := (g.nodes.zipIdx.filter fun m => m.1.border == -2).filter
        fun m => m.1.clusterPath.dropLast == an.clusterPath
      by_cases hl : leaves.isEmpty = true
      · by_cases hc : children.isEmpty = true
        · exact step (compound_empty_group_constraint_edge (top := (an, a))
            (List.mem_zipIdx_iff_getElem?.mpr ha) hta hab hl hc)
        · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil children (fun he => hc (by simp [he]))
          obtain ⟨hq', hpath⟩ := List.mem_filter.mp hq
          obtain ⟨hq'', htag⟩ := List.mem_filter.mp hq'
          have hch := List.mem_zipIdx_iff_getElem?.mp hq''
          have htag' : q.1.border = -2 := by simpa only [beq_iff_eq] using htag
          have hpath' : q.1.clusterPath.dropLast = an.clusterPath := by
            simpa only [beq_iff_eq] using hpath
          obtain ⟨qb, hqb⟩ := bottomExists hch htag'
          obtain ⟨qbox, _, hqp⟩ := X_cg_group_box e.graph0_eq e.graph_eq (hget hch) htag'
          have hqpos : 0 < q.1.clusterPath.length := by simp [hqp]
          have hqmax : q.1.clusterPath.length ≤ e.lines.length + 1 := by
            rw [hqp, List.length_append, List.length_singleton, hlines]
            change (Compound.ancestors inp.boxes inp.boxes.length qbox.parent).length + 1 ≤ _
            have hbnd := ancestors_length_le inp.boxes inp.boxes.length qbox.parent
            omega
          have hlen := congrArg List.length hpath'
          rw [List.length_dropLast] at hlen
          have hlt : e.lines.length + 2 - q.1.clusterPath.length < fuel := by omega
          obtain ⟨hlo, hhi⟩ := compound_child_constraint_edges (parent := (an, a)) (child := q)
            (List.mem_zipIdx_iff_getElem?.mpr ha) hta hab hq'' htag' hpath' hqb
          exact Int.lt_trans (step hlo)
            (Int.lt_trans (ih _ hlt _ _ _ hch htag' hqb rfl) (step hhi))
      · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil leaves (fun he => hl (by simp [he]))
        obtain ⟨hq', hcond⟩ := List.mem_filter.mp hq
        obtain ⟨hq0, hpath⟩ := Bool.and_eq_true_iff.mp hcond
        have hwin := componentRunR_compound_leaf_rank_window hrun (top := (an, a)) (member := q)
          (List.mem_zipIdx_iff_getElem?.mpr ha) hta hab hq' (by simpa using hq0) hpath
        exact Int.lt_trans hwin.1 hwin.2
  have ho' : g.nodes[i]? = some owner := by rwa [← hnodes]
  obtain ⟨b, hfind⟩ := bottomExists ho' howner
  have hfind' := hfind
  unfold ownCaptionBottom at hfind'
  have hb := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfind')
  have hkeys : b.1.border = 2 ∧ b.1.decl = owner.decl := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hfind'
  obtain ⟨_, _, hpath⟩ := X_cg_bottom_box e.graph0_eq e.graph_eq (hget hb) hkeys.1
  have hmem : b.1.clusterPath.contains owner.decl = true := by simp [hpath, hkeys.2]
  exact ⟨b.2, b.1, by rwa [hnodes], hkeys.1, hmem, axisWidth _ i owner b ho' howner hfind rfl⟩

private theorem ownCaption_rank_bands_strict {P : Params} {exactIds : List String}
    {spec : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) (some spec) inp cg labels orderOptions =
      .ok (cg', run)) {r s : Nat} (hrs : r < s) (hsLayer : s < run.layers.length) :
    run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper (run.layers.getD r []) <
      run.top.getD s 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, _, ⟨_, top⟩, ysMid, hs⟩ :=
    componentRunR_stages hrun
  obtain ⟨_, htopLen⟩ := CoordsImpl.rankCoordsWith_length hs.hYt
  obtain ⟨extra, shifts, _, heNonneg, hprefix, hshiftLen, htopShift, _⟩ :=
    (runHooksShift_exact P exactIds inp cg' labels).shifts placed run.layers ysMid top
      run.ys run.top hs.hReserve
  have hpair : shifts.Pairwise (· ≤ ·) := by
    rw [hprefix]
    exact reserveShift_prefix_pairwise extra heNonneg 0 [] (by simp) (by simp)
  have hrLayer : r < run.layers.length := by omega
  have hr : r < top.length := by rwa [htopLen]
  have hsTop : s < top.length := by rwa [htopLen]
  have hrShift : r < shifts.length := by rwa [hshiftLen]
  have hsShift : s < shifts.length := by rwa [hshiftLen]
  have hmono : shifts.getD r 0 ≤ shifts.getD s 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hrShift, List.getElem?_eq_getElem hsShift,
      Option.getD_some, Option.getD_some]
    exact hpair.rel_getElem_of_lt hrShift hsShift hrs
  have hseq := rankAxis_band_top_strict hs.hYt r s run.layers[r] run.layers[s]
    hrs (List.getElem?_eq_getElem hrLayer) (List.getElem?_eq_getElem hsLayer)
  have hget : run.layers.getD r [] = run.layers[r] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrLayer, Option.getD_some]
  rw [hs.hCoordProper, hget, htopShift r hr, htopShift s hsTop]
  omega

private theorem ownCaption_final_title {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {candidate cg : Graph} {labels : List MeasuredLabel}
    {run : Run} {orderOptions : OrderOptions} {rm : ComponentRegions}
    {ranks : List Int} {normalized labeled p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)} {reserved : List (Option Int)}
    (hrun : componentRunR P exact (some s) inp candidate labels orderOptions = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hnodes : cg.nodes = candidate.nodes)
    (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    (hcoord : coordinateGraphR P exact (some s) labeled = p)
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    (hshape : ∀ {i : Nat} {n : Node}, cg.nodes[i]? = some n → n.border ≠ 3)
    {t : Nat} {title : ProperNode} (ht : run.proper.nodes[t]? = some title)
    (hkind : title.node.border = 3) :
    run.coordinateProper.nodes[t]? = some title ∧
      ∃ (j : Nat) (old : Node), cg.nodes[j]? = some old ∧ old.border = -2 ∧
        title.node.clusterPath = old.clusterPath ∧
        title.node.h = (s.titles.getD old.decl (0, 0)).2 + P.clusterPad ∧
        rk run.proper.rank t = rk run.proper.rank j := by
  have hpp : stages.placement.p = p := by rw [stages.hPlacement]
  have hpr : stages.placement.rm = rm := by rw [stages.hPlacement]
  obtain ⟨hlen, hports⟩ := groupPlain_reservedPorts_record stages.hFramesAndPorts
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, proxied, _, _, actual⟩ := componentRunR_stages hrun
  have hproxy : proxyWidths run.coordinateProper run.coordinateXs = .ok (proxied, run.xs) := by
    rw [actual.hCoordProper]
    exact actual.hProxy
  obtain ⟨_, hpxRank, hpxLen, _, hmetadata, hnonproxy⟩ := proxyWidths_rel hproxy
  have hfinalNodes : run.proper.nodes = proxied.nodes := by
    rw [← actual.hDrop, OrderImpl.dropSynthetic_nodes]
  have htP : t < p.nodes.length := by
    have hi := (List.getElem?_eq_some_iff.mp ht).1
    rwa [hfinalNodes, hpxLen, hlen, hpp] at hi
  let n := p.nodes[t]
  have hn : p.nodes[t]? = some n := List.getElem?_eq_getElem htP
  have hnP : stages.placement.p.nodes[t]? = some n := by rwa [hpp]
  obtain ⟨m, hm, hportKind, hrestore⟩ := hports hnP
  obtain ⟨q, hq, _, hproxyKind, _⟩ := hmetadata t m hm
  have heq : q = title := Option.some.inj (hq.symm.trans (by rwa [← hfinalNodes]))
  subst q
  have hb : n.node.border = 3 := hportKind.symm.trans (hproxyKind.symm.trans hkind)
  have hnc : (coordinateGraphR P exact (some s) labeled).nodes[t]? = some n := by rwa [hcoord]
  obtain ⟨htCopy, j, old, hold, holdKind, hpath, hh, hr⟩ :=
    ownCaption_coordinate_copy hnorm hlabels (fun h => hshape h) hnc hb
  have hcovered (k : Nat) (hk : k < candidate.nodes.length) : k < labeled.nodes.length := by
    have hk' : k < cg.nodes.length := by rwa [hnodes]
    have hc : cg.nodes[k]? = some cg.nodes[k] := List.getElem?_eq_getElem hk'
    have hl := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hc) rfl
    exact (List.getElem?_eq_some_iff.mp hl).1
  have haway : ∀ row ∈ stages.placement.rm.clusters, row.top ≠ t ∧ row.bottom ≠ t := by
    intro row hrow
    have hm : row ∈ clusterRows inp s candidate := by
      rwa [hpr, ownCaption_resolved_rows hactive] at hrow
    obtain ⟨hlo, hhi⟩ := ownCaption_cluster_bounds hm
    exact ⟨by have := hcovered _ hlo; omega, by have := hcovered _ hhi; omega⟩
  obtain ⟨hmn, _⟩ := hrestore haway
  have hnCoord : run.coordinateProper.nodes[t]? = some n := by rwa [hmn] at hm
  have hnon : ¬ (n.node.border = -2 ∨ n.node.border = 2) := by omega
  have hnFinal : run.proper.nodes[t]? = some n := by
    rw [hfinalNodes]
    exact (hnonproxy t n hnCoord hnon).1
  have hnTitle : n = title := Option.some.inj (hnFinal.symm.trans ht)
  subst title
  have hrFinal : run.proper.rank = (coordinateGraphR P exact (some s) labeled).rank := by
    rw [← actual.hDrop, OrderImpl.dropSynthetic_rank, hpxRank,
      ownCaption_ports_rank stages.hFramesAndPorts, hpp, hcoord]
  exact ⟨hnCoord, j, old, hold, holdKind, hpath, hh, by rwa [hrFinal]⟩

private theorem ownCaption_selected_height {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) {s : RegionSpec} (hs : selected.spec = some s)
    {key : Nat} (hkey : key < e.lines.length) :
    (s.titles.getD key (0, 0)).2 =
      (titleCaptionSize e.params o (e.lines.getD key [])).h := by
  have he := selected.effective_eq
  rw [hs] at he
  change (some s : Option RegionSpec) =
    (if selected.regions.isSome then
      if idSets.isEmpty then none else some (RegionSpec.mk idSets (e.lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * e.params.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height)))
      else none) at he
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

private theorem ownCaption_placed_pair {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) {i : Nat} {stored frame : Rect}
    (hm : (i, stored) ∈ part.2.titles) (hf : part.2.rects[i]? = some frame) :
    let bounds := placeBoundsX e.params selected.cg selected.run e.measured selected.loops
    let dx := 0 - bounds.minX
    let dy := -bounds.minY
    ∃ raw : Rect, (i, raw) ∈ componentTitles e.params selected.cg selected.run ∧
      shiftRect dx dy raw = stored ∧
      shiftRect dx dy (frameRect e.params selected.cg selected.run i) = frame := by
  let bounds := placeBoundsX e.params selected.cg selected.run e.measured selected.loops
  let dx := 0 - bounds.minX
  let dy := -bounds.minY
  rw [selected.part_eq] at hm hf
  change (i, stored) ∈ (componentTitles e.params selected.cg selected.run).map
    (fun q => (q.1, shiftRect dx dy q.2)) at hm
  obtain ⟨⟨j, raw⟩, hraw, hpair⟩ := List.mem_map.mp hm
  obtain ⟨hji, hstored⟩ := Prod.mk.inj hpair
  change j = i at hji
  subst j
  change (((List.range selected.cg.nodes.length).map
    (frameRect e.params selected.cg selected.run)).map (shiftRect dx dy))[i]? =
      some frame at hf
  have hi : i < selected.cg.nodes.length := by
    simpa only [List.length_map, List.length_range] using (List.getElem?_eq_some_iff.mp hf).1
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq] at hf
  exact ⟨raw, hraw, hstored, hf⟩

/-- The selected active part emits its caption inside the frame at the same
component index. This uses neither an arbitrary group frame nor a caption-fit premise. -/
theorem r8b_activeOwnCaption_strictInside {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) (hpart : part ∈ e.componentsAcc.parts)
    {s : RegionSpec} (hs : selected.spec = some s)
    {i : Nat} {stored frame : Rect}
    (hm : (i, stored) ∈ part.2.titles) (hf : part.2.rects[i]? = some frame) :
    let size := titleCaptionSize e.params o (e.lines.getD (part.1.getD i 0) [])
    frame.StrictInside { stored with w := size.w, h := size.h } := by
  let size := titleCaptionSize e.params o (e.lines.getD (part.1.getD i 0) [])
  obtain ⟨raw, hraw, hstored, hframe⟩ := ownCaption_placed_pair selected hm hf
  obtain ⟨owner, t, title, ho, howner, ht, hkind, htPath, hrawX, hrawW⟩ :=
    ownCaption_emission hraw
  have hcomp : part.1 ∈ components e.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) e.components_eq).1]
    exact List.mem_map_of_mem hpart
  have hrun := selected.run_eq
  rw [hs] at hrun
  have hresolve : newComponentRegions selected.spec e.params inp
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
  rw [hs, hrm] at hresolve
  obtain ⟨_, _, _, _, _, _, _, _, hrank, hnorm, hlabels, hcoord, hmin, _, ⟨stages⟩⟩ :=
    componentRunR_active_allocation_stages hrun hresolve
  have hnodes := rankEquivalentR_nodes_eq hrank
  have horiginal {j : Nat} {n : Node} (h : selected.cg.nodes[j]? = some n) :
      (componentCandidate e.graph part.1 selected.candidate).nodes[j]? = some n := by
    have hcandidateNodes :
        (componentCandidate e.graph part.1 selected.candidate).nodes =
          (componentCandidateR (some s) e.graph part.1 selected.candidate).nodes := by
      rw [componentCandidate_nodes] <;> rfl
    rwa [hcandidateNodes, ← hnodes]
  have hshape {j : Nat} {n : Node} (h : selected.cg.nodes[j]? = some n) : n.border ≠ 3 := by
    rcases (X_componentCandidate_marker_shape e.graph0_eq e.graph_eq (horiginal h)).1 with
      h | h | h <;> omega
  have ho' := ho
  rw [hnodes] at ho'
  obtain ⟨hkey, _, source, hsource⟩ := active_candidate_top_source e hcomp ho' howner
  have hget : part.1.getD i 0 = owner.decl := by
    simp only [List.getD_eq_getElem?_getD, hkey, Option.getD_some]
  have hline : owner.decl < e.lines.length := by
    rw [boxLines_length e.lines_eq]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hsize : (s.titles.getD owner.decl (0, 0)).2 = size.h := by
    dsimp only [size]
    rw [hget]
    exact ownCaption_selected_height selected hs hline
  obtain ⟨_, _, hownerPath⟩ := X_cg_group_box e.graph0_eq e.graph_eq (horiginal ho) howner
  have hownerLast : owner.clusterPath.getLast? = some owner.decl := by
    rw [hownerPath]
    simp
  have hownerMem : owner.clusterPath.contains owner.decl = true :=
    List.contains_iff_mem.mpr (List.mem_of_getLast? hownerLast)
  have hrows := ownCaption_resolved_rows hresolve
  obtain ⟨g, row, hg, hdecl, hrowWidth⟩ := ownCaption_cluster_get hrows ho' howner
  have hg' : stages.placement.rm.clusters[g]? = some row := by rwa [stages.hPlacement]
  have hrowBound := (List.getElem?_eq_some_iff.mp hg).1
  obtain ⟨pre, post, horder, hlast, _⟩ :=
    (stages.reservation_order (activeRegion_parent_count hresolve) hmin).2 g (Nat.le_of_lt hrowBound)
  let left := stages.allocation.lefts.getD g 0
  let span := (reserveWidths stages.placement e.params).getD g 0 -
    stages.placement.buckets.loopWidth.getD g 0
  have hroom : raw.w + 2 * regionInsetOf e.params ≤ span := by
    have hw := reserveWidths_title_from_last_write (P := e.params) hg' horder hlast
    rwa [hrowWidth, ← hrawW] at hw
  have htitleLast : title.node.clusterPath.getLast? = some row.decl := by
    rw [htPath, hdecl, hownerLast]
  obtain ⟨hwidth, hcenter⟩ := stages.activeChild_title_center e.graph0_eq e.graph_eq hcomp hrun
    hresolve hrank hnorm hlabels hcoord hg ht hkind htitleLast
  have hleft : raw.x = left + Int.tdiv span 2 - Int.fdiv raw.w 2 := by
    rw [hrawX, hcenter, ownCaption_allocation_widths stages.hAllocation, hwidth, hrowWidth, ← hrawW]
  let outer := frameRect e.params selected.cg selected.run i
  have hbounds := stages.activeGroup_frame_covers_reservation e.graph0_eq e.graph_eq hcomp hrun
    hresolve hrank hnorm hlabels hcoord e.checked hg ho howner hdecl.symm
  have houterX : outer.x ≤ left ∧ left + span ≤ outer.x + outer.w := by
    refine ⟨hbounds.1, ?_⟩
    have h := hbounds.2
    dsimp only [left, span, outer]
    omega
  have hfit := R_exactTitleCaptionFitB8_holds exactIds idSets e hpart hm
  change 0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ stored.w ∧ size.h ≤ stored.h at hfit
  have hfitW : size.w ≤ raw.w := by
    have h := hfit.2.2.1
    rwa [← hstored] at h
  have hpad := checkedParams_clusterPad_pos e.checked
  have hinset : 0 < regionInsetOf e.params := by
    have hb := checkedParams_clusterBorderW_ge_one e.checked
    unfold regionInsetOf
    omega
  have hx := ownCaption_center_strict (left := left) hfit.1 hfitW hinset hroom
  dsimp only at hx
  rw [← hleft] at hx
  obtain ⟨htCoord, j, old, hold, holdKind, holdPath, holdHeight, holdRank⟩ :=
    ownCaption_final_title hrun hresolve hnodes hnorm hlabels hcoord stages
      (fun h => hshape h) ht hkind
  have hji := X_cg_top_unique e.graph0_eq e.graph_eq hcomp (horiginal hold) (horiginal ho)
    holdKind howner (holdPath.symm.trans htPath)
  rw [hji] at hold holdRank
  have he := Option.some.inj (hold.symm.trans ho)
  subst old
  have htitleH : RouteImpl.nodeH selected.run.proper t = size.h + e.params.clusterPad := by
    simp only [RouteImpl.nodeH, ht, holdHeight, hsize]
  obtain ⟨b, bottom, hb, hbKind, hbPath, hrankLT⟩ :=
    ownCaption_bottom_rank e hcomp hrun hresolve ho howner
  obtain ⟨bc, bf, hbc, hbf, _, _, _, _, _, hbfPath, hzero⟩ :=
    componentRunR_active_marker_records hrun hresolve hb (Or.inr hbKind)
  have hlayers : RouteImpl.layersOk selected.run.proper selected.run.layers = true := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, actual⟩ := componentRunR_stages hrun
    rcases actual.hLanes with ⟨_, h⟩ | ⟨_, h⟩
    · exact (RouteImpl.routeWithLanes_geometry h).1
    · exact (rcbRouteWithLanesR_geometry h).1
  have hcoverage := (RouteImpl.layersOk_spec hlayers).2.2.2.1
  obtain ⟨_, _, _, hrT⟩ := hcoverage t (List.getElem?_eq_some_iff.mp ht).1
  obtain ⟨_, hLayerB, _, hrB⟩ := hcoverage b (List.getElem?_eq_some_iff.mp hbf).1
  have hslt : (rk selected.run.proper.rank t).toNat < (rk selected.run.proper.rank b).toNat := by
    have htNat := Int.toNat_of_nonneg hrT
    have hbNat := Int.toNat_of_nonneg hrB
    omega
  have hsep := ownCaption_rank_bands_strict hrun hslt (List.getElem?_eq_some_iff.mp hLayerB).1
  have hbandT := ((componentRunR_boundaryRankBands hrun).1 htCoord (fun h => by omega)).2.1
  have hbandB := ((componentRunR_boundaryRankBands hrun).1 hbc (fun _ => (hzero hbKind).1)).1
  have hoGet : selected.cg.nodes.getD i default = owner := by
    simp only [List.getD_eq_getElem?_getD, ho, Option.getD_some]
  have htMem : title.node.clusterPath.contains (selected.cg.nodes.getD i default).decl = true := by
    rw [htPath, hoGet]
    exact hownerMem
  have hbMem : bf.node.clusterPath.contains (selected.cg.nodes.getD i default).decl = true := by
    rw [hbfPath, hoGet]
    exact hbPath
  have hgKind : (selected.cg.nodes.getD i default).border = -2 := by rwa [hoGet]
  have hTitleHull := (frameRect_member_vertical (P := e.params) (q := (title, t))
    hgKind (List.mem_zipIdx_iff_getElem?.mpr ht) htMem).1
  have hBottomHull := (frameRect_member_vertical (P := e.params) (q := (bf, b))
    hgKind (List.mem_zipIdx_iff_getElem?.mpr hbf) hbMem).2
  change outer.y ≤ selected.run.ys.getD t 0 at hTitleHull
  simp only [Labels.rectAt, Labels.labelRect, RouteImpl.yAt, RouteImpl.nodeH, hbf,
    (hzero hbKind).2, Int.add_zero] at hBottomHull
  change selected.run.ys.getD b 0 ≤ outer.y + outer.h at hBottomHull
  change selected.run.top.getD (rk selected.run.proper.rank b).toNat 0 ≤
    selected.run.ys.getD b 0 at hbandB
  change selected.run.ys.getD t 0 + RouteImpl.nodeH selected.run.proper t ≤
    selected.run.top.getD (rk selected.run.proper.rank t).toNat 0 +
      CoordsImpl.layerHeight selected.run.coordinateProper
        (selected.run.layers.getD (rk selected.run.proper.rank t).toNat []) at hbandT
  have hy := componentTitles_y_eq_frame hraw
  change raw.y = outer.y + e.params.clusterPad at hy
  have hstrict : outer.StrictInside { raw with w := size.w, h := size.h } := by
    change outer.x < raw.x ∧ raw.x + size.w < outer.x + outer.w ∧
      outer.y < raw.y ∧ raw.y + size.h < outer.y + outer.h
    exact ⟨by omega, by omega, by omega, by omega⟩
  change frame.StrictInside { stored with w := size.w, h := size.h }
  rw [← hframe, ← hstored]
  exact strictInside_shiftRect hstrict

/-- The route remainder is unchanged. The caption remainder excludes the
proved active foreign pairs and active own captions at the same index. -/
def R_ExecutedPartFrameCoresB8ActiveCaptionRemainder (exactIds : List String)
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
        ¬ R8b_ActiveForeignCaption selected i pos →
        ¬ (i = pos ∧ ∃ s, selected.spec = some s) →
        let size := titleCaptionSize execution.params o (execution.lines.getD (part.1.getD i 0) [])
        Disjoint frame { stored with w := size.w, h := size.h } ∨
          frame.StrictInside { stored with w := size.w, h := size.h })

theorem R_foreignCaptionRemainder_iff_activeCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String)) :
    R_ExecutedPartFrameCoresB8ForeignCaptionRemainder exactIds idSets ↔
      R_ExecutedPartFrameCoresB8ActiveCaptionRemainder exactIds idSets := by
  classical
  constructor
  · intro h inp o res execution hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := h execution hwf hfp part hpart
    refine ⟨hroute, ?_⟩
    intro selected i stored pos key src frame hm hk hs hg hf hforeign _
    exact hcaption selected i stored pos key src frame hm hk hs hg hf hforeign
  · intro h inp o res execution hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := h execution hwf hfp part hpart
    refine ⟨hroute, ?_⟩
    intro selected i stored pos key src frame hm hk hs hg hf hforeign
    by_cases hown : i = pos ∧ ∃ s, selected.spec = some s
    · obtain ⟨heq, s, hspec⟩ := hown
      subst pos
      exact Or.inr (r8b_activeOwnCaption_strictInside selected hpart (s := s) hspec hm hf)
    · exact hcaption selected i stored pos key src frame hm hk hs hg hf hforeign hown

theorem flatC8bB_layoutRIds_activeCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String))
    (hcores : R_ExecutedPartFrameCoresB8ActiveCaptionRemainder exactIds idSets)
    (hfallW : R_FallbackCaptionClearBW exactIds idSets)
    (hres : R_PartSizingRResidual exactIds idSets)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    FlatC8bB (layoutRIds exactIds idSets) :=
  flatC8bB_layoutRIds_foreignCaptionRemainder exactIds idSets
    ((R_foreignCaptionRemainder_iff_activeCaptionRemainder exactIds idSets).mpr hcores)
    hfallW hres hcap

end Elegant.Layered.PipelineImpl

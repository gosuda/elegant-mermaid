import Elegant.Layered.RegionReservedChildMarkerHull
import Elegant.Layered.RegionC8aGroupPlain

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private def hasSide (p : Proper) (decl : Nat) (side : Int) : Prop :=
  ∃ (i : Nat) (n : ProperNode), p.nodes[i]? = some n ∧ n.node.border = side ∧
    n.node.clusterPath.getLast? = some decl

private theorem clusterPortR_hasSides {pl : RegionPlacement} {g v : Nat} {before after : List Int}
    (h : clusterPortR pl g v before = .ok after) :
    hasSide pl.p (pl.rm.clusters.getD g default).decl (-1) ∧
      hasSide pl.p (pl.rm.clusters.getD g default).decl 1 := by
  let decl := (pl.rm.clusters.getD g default).decl
  let rank := rk pl.p.rank v
  let pick (acc : Option Nat × Option Nat) (q : ProperNode × Nat) :=
    if q.1.node.clusterPath.getLast? != some decl || rk pl.p.rank q.2 != rank then acc
    else
      match q.1.node.border with
      | -1 => (some q.2, acc.2)
      | 1 => (acc.1, some q.2)
      | _ => acc
  let inv (acc : Option Nat × Option Nat) :=
    (∀ i, acc.1 = some i → ∃ n, pl.p.nodes[i]? = some n ∧ n.node.border = -1 ∧
      n.node.clusterPath.getLast? = some decl) ∧
    (∀ i, acc.2 = some i → ∃ n, pl.p.nodes[i]? = some n ∧ n.node.border = 1 ∧
      n.node.clusterPath.getLast? = some decl)
  have hpick : inv (pl.p.nodes.zipIdx.foldl pick (none, none)) := by
    apply OrderImpl.foldl_inv inv _ _ _ (by simp [inv])
    intro acc ha q hq
    unfold pick
    split
    · exact ha
    · rename_i hkey
      have hpath : q.1.node.clusterPath.getLast? = some decl := by
        apply Classical.byContradiction
        intro hne
        exact hkey (Bool.or_eq_true_iff.mpr (Or.inl (bne_iff_ne.mpr hne)))
      have hqget := List.mem_zipIdx_iff_getElem?.mp hq
      split
      · rename_i hb
        refine ⟨?_, ha.2⟩
        intro i hi
        cases hi
        exact ⟨q.1, hqget, hb, hpath⟩
      · rename_i hb
        refine ⟨ha.1, ?_⟩
        intro i hi
        cases hi
        exact ⟨q.1, hqget, hb, hpath⟩
      · exact ha
  change ((match pl.p.nodes.zipIdx.foldl pick (none, none) with
    | (some l, some r) =>
      let lo := RouteImpl.xAt before l - Int.tdiv (RouteImpl.nodeW pl.p l) 2
      let hi := RouteImpl.xAt before r - Int.tdiv (RouteImpl.nodeW pl.p r) 2 + RouteImpl.nodeW pl.p r
      if hi < lo then throw LayoutError.domain
      else pure (setAt before v (lo + Int.tdiv (hi - lo) 2))
    | _ => throw LayoutError.domain) : Except LayoutError (List Int)) = Except.ok after at h
  generalize pl.p.nodes.zipIdx.foldl pick (none, none) = found at h hpick
  rcases found with ⟨left, right⟩
  cases left with
  | none => cases right <;> cases h
  | some li =>
    cases right with
    | none => cases h
    | some ri =>
      obtain ⟨l, hl, hlb, hlp⟩ := hpick.1 li rfl
      obtain ⟨r, hr, hrb, hrp⟩ := hpick.2 ri rfl
      exact ⟨⟨li, l, hl, hlb, hlp⟩, ⟨ri, r, hr, hrb, hrp⟩⟩

private abbrev PortState := List Int × Array ProperNode

private def portStep (pl : RegionPlacement) (cg : Graph) (labels : List MeasuredLabel)
    (acc : PortState) (q : RegionCluster × Nat) : Except LayoutError PortState := do
  let c := q.1
  let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
  if c.titleW < 0 ∨ footprint < 0 then throw .domain
  else
    let x ← clusterPortR pl q.2 c.top acc.1
    let x ← clusterPortR pl q.2 c.bottom x
    let top := acc.2.getD c.top default
    pure (x, acc.2.set! c.top
      { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } })

private theorem portFold_keys_and_visits {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {jobs : List (RegionCluster × Nat)} {start out : PortState}
    (h : jobs.foldlM (portStep pl cg labels) start = .ok out) :
    (∀ q ∈ jobs, hasSide pl.p (pl.rm.clusters.getD q.2 default).decl (-1) ∧
      hasSide pl.p (pl.rm.clusters.getD q.2 default).decl 1) ∧
    ∀ {i : Nat} {n : ProperNode}, start.2[i]? = some n →
      ∃ m, out.2[i]? = some m ∧ m.node.border = n.node.border ∧ m.node.clusterPath = n.node.clusterPath := by
  induction jobs generalizing start with
  | nil =>
    change Except.ok start = .ok out at h
    rw [← Except.ok.inj h]
    exact ⟨by simp, fun hn => ⟨_, hn, rfl, rfl⟩⟩
  | cons q rest ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hm, hr⟩ := bind_ok h
    dsimp only [portStep] at hm
    split at hm
    · cases hm
    · obtain ⟨_, htop, hm⟩ := bind_ok hm
      obtain ⟨_, _, hm⟩ := bind_ok hm
      obtain ⟨hvisits, hkeys⟩ := ih hr
      refine ⟨?_, ?_⟩
      · intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · exact clusterPortR_hasSides htop
        · exact hvisits entry hentry
      · intro i n hn
        have hupdated : ∃ m, mid.2[i]? = some m ∧ m.node.border = n.node.border ∧
            m.node.clusterPath = n.node.clusterPath := by
          rw [← Except.ok.inj hm]
          dsimp only
          rw [Array.set!_eq_setIfInBounds]
          by_cases he : q.1.top = i
          · have hlt := (Array.getElem?_eq_some_iff.mp hn).1
            have hget : start.2.getD i default = n := by
              simp only [Array.getD_eq_getD_getElem?, hn, Option.getD_some]
            rw [he, Array.getElem?_setIfInBounds_self_of_lt hlt, hget]
            exact ⟨_, rfl, rfl, rfl⟩
          · rw [Array.getElem?_setIfInBounds_ne he]
            exact ⟨n, hn, rfl, rfl⟩
        obtain ⟨m, hm, hb, hp⟩ := hupdated
        obtain ⟨fin, hf, hb', hp'⟩ := hkeys hm
        exact ⟨fin, hf, hb'.trans hb, hp'.trans hp⟩

private theorem reservedPortsR_hasSides {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper}
    (h : reservedPortsR pl cg labels xs = .ok (ys, placed))
    {g : Nat} {c : RegionCluster} (hc : pl.rm.clusters[g]? = some c) :
    hasSide placed c.decl (-1) ∧ hasSide placed c.decl 1 := by
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM (portStep pl cg labels)
    (xs, pl.p.nodes.toArray)).bind _) = _ at h
  obtain ⟨out, hfold, hret⟩ := bind_ok h
  have hnodes : placed.nodes = out.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hret)).symm
  obtain ⟨hv, hkeys⟩ := portFold_keys_and_visits hfold
  have hp := hv (c, g) (List.mem_zipIdx_iff_getElem?.mpr hc)
  have hcluster : pl.rm.clusters.getD g default = c := by
    simp only [List.getD_eq_getElem?_getD, hc, Option.getD_some]
  change hasSide pl.p (pl.rm.clusters.getD g default).decl (-1) ∧
    hasSide pl.p (pl.rm.clusters.getD g default).decl 1 at hp
  rw [hcluster] at hp
  have carry {side : Int} (hside : hasSide pl.p c.decl side) : hasSide placed c.decl side := by
    obtain ⟨i, n, hn, hb, hpath⟩ := hside
    obtain ⟨m, hm, hb', hp'⟩ := hkeys (i := i) (n := n) (by rwa [List.getElem?_toArray])
    refine ⟨i, m, ?_, hb'.trans hb, (congrArg List.getLast? hp').trans hpath⟩
    rwa [hnodes, Array.getElem?_toList]
  exact ⟨carry hp.1, carry hp.2⟩

/-- For an active group, positions of actual signed side markers bound its
emitted frame from the inside, even when no route attaches to the group. -/
theorem RegionCrossAllocationStages.activeGroup_frame_covers_reservation
    {P : Params} {exact : List Nat} {s : RegionSpec} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph cg : Graph}
    {labels : List MeasuredLabel} {run : Run} {comp : List Nat} {candidate : Nat}
    {orderOptions : OrderOptions} {rm : ComponentRegions} {ranks : List Int} {budget : Bool}
    {normalized labeled p : Proper} {minimum : RegionConstraints} {layers : List (List Nat)}
    {reserved : List (Option Int)}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraph : exactGraph P exactIds inp o labels graph0 = .ok graph)
    (hcomp : comp ∈ components graph)
    (hrun : componentRunR P exact (some s) inp
      (componentCandidateR (some s) graph comp candidate) labels orderOptions = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp
      (componentCandidateR (some s) graph comp candidate) = .ok (some rm))
    (hrank : rankEquivalentR rm (componentCandidateR (some s) graph comp candidate) =
      .ok (ranks, cg, budget))
    (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    (hcoord : coordinateGraphR P exact (some s) labeled = p)
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    (hparams : checkedParams o.profile inp.kind = .ok P)
    {g pos : Nat} {c : RegionCluster} {frame : Node}
    (hg : rm.clusters[g]? = some c) (hnode : cg.nodes[pos]? = some frame)
    (hgroup : frame.border = -2) (hdecl : frame.decl = c.decl) :
    let left := stages.allocation.lefts.getD g 0
    let right := left + (reserveWidths stages.placement P).getD g 0 -
      stages.placement.buckets.loopWidth.getD g 0
    (frameRect P cg run pos).x ≤ left ∧
      right ≤ (frameRect P cg run pos).x + (frameRect P cg run pos).w := by
  have hcluster : stages.placement.rm.clusters[g]? = some c := by rwa [stages.hPlacement]
  obtain ⟨hl, hr⟩ := reservedPortsR_hasSides stages.hFramesAndPorts hcluster
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, proxied, _, _, hs⟩ := componentRunR_stages hrun
  have hproxy : proxyWidths run.coordinateProper run.coordinateXs = .ok (proxied, run.xs) := by
    rw [hs.hCoordProper]
    exact hs.hProxy
  have hfinalNodes : run.proper.nodes = proxied.nodes := by rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes]
  have carry {sign : Int} (hside : hasSide run.coordinateProper c.decl sign)
      (htag : sign = -1 ∨ sign = 1) : hasSide run.proper frame.decl sign := by
    obtain ⟨i, n, hi, hb, hp⟩ := hside
    have hplain : ¬(n.node.border = -2 ∨ n.node.border = 2) := by rcases htag with h | h <;> omega
    have hn := ((proxyWidths_rel hproxy).2.2.2.2.2 i n hi hplain).1
    exact ⟨i, n, by rwa [hfinalNodes], hb, hp.trans (congrArg some hdecl.symm)⟩
  obtain ⟨li, l, hl, hlTag, hlPath⟩ := carry hl (Or.inl rfl : (-1 : Int) = -1 ∨ -1 = 1)
  obtain ⟨ri, r, hr, hrTag, hrPath⟩ := carry hr (Or.inr rfl : (1 : Int) = -1 ∨ (1 : Int) = 1)
  obtain ⟨hLW, hLX⟩ := stages.activeChild_side_centers hgraph0 hgraph hcomp hrun hactive
    hrank hnorm hlabels hcoord hg hl (Or.inl hlTag) (hlPath.trans (congrArg some hdecl))
  obtain ⟨hRW, hRX⟩ := stages.activeChild_side_centers hgraph0 hgraph hcomp hrun hactive
    hrank hnorm hlabels hcoord hg hr (Or.inr hrTag) (hrPath.trans (congrArg some hdecl))
  rw [hlTag, ite_eq_left rfl] at hLX
  rw [hrTag, ite_eq_right (by decide : (1 : Int) ≠ -1)] at hRX
  have hmL := groupBorderRects_mem_of_record (cg := cg) hl (Or.inl hlTag) hlPath
  have hmR := groupBorderRects_mem_of_record (cg := cg) hr (Or.inr hrTag) hrPath
  have hleft := boundsOf_minX_le_rect_x _ [] _ hmL
  have hright := rect_right_le_boundsOf_right _ [] _ hmR
  have hbw := checkedParams_clusterBorderW_ge_one hparams
  have hhalf : Int.tdiv P.clusterBorderW 2 = Int.fdiv P.clusterBorderW 2 := by
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW, hl, hLW, hLX, hhalf] at hleft
  simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW, hr, hRW, hRX, hhalf] at hright
  rw [frameRect_group_span hnode hgroup]
  dsimp only
  exact ⟨by omega, by omega⟩

end Elegant.Layered.PipelineImpl


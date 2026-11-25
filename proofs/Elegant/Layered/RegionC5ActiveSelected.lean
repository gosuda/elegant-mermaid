import Elegant.Layered.RegionActiveOrderProof
import Elegant.Layered.RegionBaseExecutedValidity
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.RunStagePathFacts
import Elegant.Layered.RegionC5RankBand
import Elegant.Layered.RegionGroupPortGeometry
import Elegant.Layered.RegionC5CompoundRank

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl
open CoordsImpl

private theorem activeCoordinateMarker (P : Params) (exact : List Nat) (s : RegionSpec)
    {labeled : Proper} {v : Nat} {n : Node}
    (hn : labeled.nodes[v]? = some ⟨n, false, none, false⟩)
    (hb : n.border = -2 ∨ n.border = 2) :
    ∃ m, (coordinateGraphR P exact (some s) labeled).nodes[v]? = some m ∧
      m.dummy = false ∧ m.node.border = n.border ∧ m.node.clusterPath = n.clusterPath ∧
      m.node.h = 0 := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  have hkeys := sizeProperPortsX_key P exact labeled v
  change (sized.nodes[v]?).map _ = _ at hkeys
  cases hs : sized.nodes[v]? with
  | none => simp [hs, hn] at hkeys
  | some sz =>
    simp only [hs, hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkeys
    obtain ⟨hd, hborder, hpath⟩ := hkeys
    have hcond : (sz.node.border == -2 || sz.node.border == 2) = true := by
      rcases hb with hb | hb <;> simp [hborder, hb]
    let t : ProperNode := { sz with node := { sz.node with w := 0, h := 0 } }
    have ht : titled.nodes[v]? = some t := by
      unfold titled titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by
        simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hs).1)]
      simp only [List.getElem?_map, hs, Option.map_some, hcond, ↓reduceIte, t]
    obtain ⟨_, hbordered, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    let cleared := clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)
    have hc : cleared.nodes[v]? = some (clearF t) := by
      unfold cleared
      rw [clearProxyExtents_nodes, List.getElem?_map, hbordered,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1, ht] <;> rfl
    obtain ⟨m, hm, _⟩ := materialize_exists cleared hc
    obtain ⟨old, hold, _, _, _, hunmodified⟩ := materialize_lookup cleared hm
    have heq : old = clearF t := Option.some.inj (hold.symm.trans hc)
    subst old
    obtain ⟨hcd, hcb, hcp, hch⟩ := clearF_keys t
    have hflat : (clearF t).node.h = 0 := hch
    have hreal : (clearF t).dummy = false := hcd.trans hd
    rw [hunmodified hreal] at hm
    exact ⟨clearF t, hm, hreal, hcb.trans hborder, hcp.trans hpath, hflat⟩

private theorem activeClusterWriter {P : Params} {s : RegionSpec} {inp : Input}
    {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp cg = .ok (some rm))
    {c : RegionCluster} (hc : c ∈ rm.clusters) :
    ∃ n, cg.nodes[c.top]? = some n ∧ n.border = -2 := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  split at h
  · cases h
  have hclusters : rm.clusters = clusterRows inp s cg :=
    (congrArg ComponentRegions.clusters (Option.some.inj (Except.ok.inj h))).symm
  rw [hclusters] at hc
  unfold clusterRows at hc
  obtain ⟨q, hq, hc⟩ := List.mem_filterMap.mp hc
  dsimp only at hc
  split at hc
  · cases hc
  · rename_i hb
    rw [← Option.some.inj hc]
    exact ⟨q.1, List.mem_zipIdx_iff_getElem?.mp hq, by simpa using hb⟩

private theorem reservedMarkerMetadata {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper} {v : Nat}
    {n : ProperNode} (h : reservedPortsR pl cg labels xs = .ok (ys, placed))
    (hn : pl.p.nodes[v]? = some n) :
    ∃ m, placed.nodes[v]? = some m ∧ m.dummy = n.dummy ∧
      m.node.border = n.node.border ∧ m.node.clusterPath = n.node.clusterPath ∧
      ((∀ c ∈ pl.rm.clusters, c.top ≠ v) → m.node.h = n.node.h) := by
  let step (acc : List Int × Array ProperNode) (q : RegionCluster × Nat) :
      Except LayoutError (List Int × Array ProperNode) := do
    let c := q.1
    let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      pure (x, acc.2.set! c.top
        { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } })
  have preserve (entries : List (RegionCluster × Nat)) (start out : List Int × Array ProperNode)
      (src : ProperNode) (hsrc : start.2[v]? = some src)
      (hfold : entries.foldlM step start = .ok out) :
      ∃ dst, out.2[v]? = some dst ∧ dst.dummy = src.dummy ∧
        dst.node.border = src.node.border ∧ dst.node.clusterPath = src.node.clusterPath ∧
        ((∀ q ∈ entries, q.1.top ≠ v) → dst.node.h = src.node.h) := by
    induction entries generalizing start src with
    | nil =>
      change Except.ok start = Except.ok out at hfold
      rw [← Except.ok.inj hfold]
      exact ⟨src, hsrc, rfl, rfl, rfl, fun _ => rfl⟩
    | cons q rest ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨mid, hmid, hrest⟩ := bind_ok hfold
      dsimp only [step] at hmid
      split at hmid
      · cases hmid
      · obtain ⟨_, _, hmid⟩ := bind_ok hmid
        obtain ⟨_, _, hmid⟩ := bind_ok hmid
        have hrecord : ∃ dst, mid.2[v]? = some dst ∧ dst.dummy = src.dummy ∧
            dst.node.border = src.node.border ∧ dst.node.clusterPath = src.node.clusterPath ∧
            (q.1.top ≠ v → dst.node.h = src.node.h) := by
          rw [← Except.ok.inj hmid]
          dsimp only
          rw [Array.set!_eq_setIfInBounds]
          by_cases he : q.1.top = v
          · have hlt := (Array.getElem?_eq_some_iff.mp hsrc).1
            have hget : start.2.getD v default = src := by
              simp only [Array.getD_eq_getD_getElem?, hsrc, Option.getD_some]
            rw [he, Array.getElem?_setIfInBounds_self_of_lt hlt, hget]
            exact ⟨_, rfl, rfl, rfl, rfl, fun hne => (hne rfl).elim⟩
          · rw [Array.getElem?_setIfInBounds_ne he]
            exact ⟨src, hsrc, rfl, rfl, rfl, fun _ => rfl⟩
        obtain ⟨m, hm, hd, hb, hp, hh⟩ := hrecord
        obtain ⟨dst, hout, hd', hb', hp', hh'⟩ := ih mid m hm hrest
        refine ⟨dst, hout, hd'.trans hd, hb'.trans hb, hp'.trans hp, ?_⟩
        intro haway
        exact (hh' (fun r hr => haway r (List.mem_cons_of_mem _ hr))).trans
          (hh (haway q List.mem_cons_self))
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = _ at h
  obtain ⟨out, hfold, hresult⟩ := bind_ok h
  have harray : placed.nodes = out.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hresult)).symm
  rw [harray, Array.getElem?_toList]
  obtain ⟨m, hm, hd, hb, hp, hh⟩ := preserve _ _ _ n
    (by rwa [List.getElem?_toArray]) hfold
  exact ⟨m, hm, hd, hb, hp, fun haway => hh (fun q hq => haway q.1
    (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq)))⟩

theorem componentRunR_active_marker_records {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm))
    {v : Nat} {n : Node} (hn : cg'.nodes[v]? = some n)
    (hb : n.border = -2 ∨ n.border = 2) :
    ∃ coord actual : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧ run.proper.nodes[v]? = some actual ∧
      coord.dummy = false ∧ actual.dummy = false ∧
      coord.node.border = n.border ∧ actual.node.border = n.border ∧
      coord.node.clusterPath = n.clusterPath ∧ actual.node.clusterPath = n.clusterPath ∧
      (n.border = 2 → coord.node.h = 0 ∧ actual.node.h = 0) := by
  obtain ⟨_, _, labeled, p, _, _, _, _, hrank, hnorm, hlabels, hcoord, _, _, ⟨alloc⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hlabel := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hn) rfl
  obtain ⟨m, hm, hd, hbo, hp, hh⟩ := activeCoordinateMarker P exact s hlabel hb
  rw [hcoord] at hm
  have hsrc : alloc.placement.p.nodes[v]? = some m := by rwa [alloc.hPlacement]
  obtain ⟨coord, hc, hcd, hcb, hcp, hch⟩ := reservedMarkerMetadata alloc.hFramesAndPorts hsrc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, q0, _, _, stages⟩ := componentRunR_stages hrun
  have hc' : placed.nodes[v]? = some coord := by simpa only [stages.hCoordProper] using hc
  obtain ⟨actual, ha, _, had, hab, hap⟩ := proxyWidths_decl_path stages.hProxy hc'
  obtain ⟨other, hother, _, _, hah⟩ := (proxyWidths_rel stages.hProxy).2.2.2.2.1 v coord hc'
  have he : other = actual := Option.some.inj (hother.symm.trans ha)
  subst other
  have ha' : run.proper.nodes[v]? = some actual := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
    exact ha
  refine ⟨coord, actual, hc, ha', hcd.trans hd, had.trans (hcd.trans hd), hcb.trans hbo,
    hab.trans (hcb.trans hbo), hcp.trans hp, hap.trans (hcp.trans hp), ?_⟩
  intro hbottom
  have hzero : coord.node.h = 0 := by
    apply Eq.trans (hch ?_) hh
    intro c hmem heq
    have hmem' : c ∈ rm.clusters := by rwa [alloc.hPlacement] at hmem
    obtain ⟨top, htop, htb⟩ := activeClusterWriter hactive hmem'
    rw [← rankEquivalentR_nodes_eq hrank, heq] at htop
    have he : n = top := Option.some.inj (hn.symm.trans htop)
    rw [he, htb] at hbottom
    omega
  exact ⟨hzero, hah.trans hzero⟩

private theorem activeC5LayersOk {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    RouteImpl.layersOk run.proper run.layers = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  rcases stages.hLanes with ⟨_, h⟩ | ⟨_, h⟩
  · exact (RouteImpl.routeWithLanes_geometry h).1
  · exact (rcbRouteWithLanesR_geometry h).1

private theorem activeC5BandTopNonneg {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions = .ok (cg', run))
    {r : Nat} (hr : r < run.layers.length) : 0 ≤ run.top.getD r 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, _, ⟨y, top⟩, ysMid, stages⟩ :=
    componentRunR_stages hrun
  obtain ⟨_, htopLen⟩ := CoordsImpl.rankCoordsWith_length stages.hYt
  have hrTop : r < top.length := by rwa [htopLen]
  obtain ⟨extra, shifts, _, he, hp, _, htop, _⟩ :=
    (runHooksShift_exact P exactIds inp cg' labels).shifts placed run.layers ysMid top
      run.ys run.top stages.hReserve
  have nonnegPrefix (es : List Int) (s : Int) (out : List Int)
      (hs : 0 ≤ s) (ho : ∀ e ∈ out, 0 ≤ e) (hes : ∀ e ∈ es, 0 ≤ e) :
      ∀ e ∈ (es.foldl (fun acc x => (acc.1 + x, acc.2 ++ [acc.1])) (s, out)).2,
        0 ≤ e := by
    induction es generalizing s out with
    | nil => exact ho
    | cons a as ih =>
      simp only [List.foldl_cons]
      apply ih
      · have ha := hes a List.mem_cons_self
        omega
      · intro e hem
        rcases List.mem_append.mp hem with hem | hem
        · exact ho e hem
        · have heq := List.mem_singleton.mp hem
          rwa [heq]
      · exact fun e hem => hes e (List.mem_cons_of_mem _ hem)
  have hs : 0 ≤ shifts.getD r 0 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : shifts[r]? with
    | none => exact Int.le_refl 0
    | some a =>
      have hm := List.mem_of_getElem? h
      rw [hp] at hm
      exact nonnegPrefix extra 0 [] (by omega) (by simp) he a hm
  obtain ⟨hg, hslot, _, hgaps, _, heq, _⟩ := CoordsImpl.rankCoordsWith_spec stages.hYt
  have hheights : ∀ x ∈ run.layers.map (CoordsImpl.layerHeight placed), 0 ≤ x := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
    exact CoordsImpl.layerHeight_nonneg _ _
  have hsteps : ∀ x ∈ CoordsImpl.rankSteps P.rankGap P.slot placed run.layers
      (run.lanes.routing.gaps.map (·.slots)), 0 ≤ x :=
    CoordsImpl.rankSteps_nonneg (by omega) (by omega) _ _ _ hgaps
  have hpre : 0 ≤ top.getD r 0 := by
    rw [heq, List.getD_eq_getElem?_getD]
    cases h : (CoordsImpl.topsFrom 0 1 0
        (run.layers.map (CoordsImpl.layerHeight placed))
        (CoordsImpl.rankSteps P.rankGap P.slot placed run.layers
          (run.lanes.routing.gaps.map (·.slots))))[r]? with
    | none => exact Int.le_refl 0
    | some t =>
      exact CoordsImpl.topsFrom_ge 0 1 (Int.le_refl 0) (by decide) _ _ _ hheights hsteps t
        (List.mem_of_getElem? h)
  rw [htop r hrTop]
  omega

private def bandIndex (run : Run) (v : Nat) : Nat := (rk run.proper.rank v).toNat

private def bandHeight (run : Run) (r : Nat) : Int :=
  CoordsImpl.layerHeight run.coordinateProper (run.layers.getD r [])

private theorem activeC5BandData {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions = .ok (cg', run)) :
    ProperDimsNonneg run.proper ∧
    (∀ v, v < run.proper.nodes.length →
      bandIndex run v < run.layers.length ∧ 0 ≤ rk run.proper.rank v) ∧
    (∀ {v : Nat} {n : ProperNode}, run.proper.nodes[v]? = some n →
      ∃ coord, run.coordinateProper.nodes[v]? = some coord ∧
        coord.node.border = n.node.border ∧ coord.node.h = n.node.h) := by
  have hok := RouteImpl.layersOk_spec (activeC5LayersOk hrun)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, q0, _, _, stages⟩ := componentRunR_stages hrun
  have hnodes : run.proper.nodes = q0.nodes := by rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
  have hlen := (proxyWidths_rel stages.hProxy).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro i n hi
    have hd := hok.2.1 i (List.getElem?_eq_some_iff.mp hi).1
    simpa only [RouteImpl.nodeW, RouteImpl.nodeH, hi] using hd
  · intro i hi
    obtain ⟨_, hget, _, hr⟩ := hok.2.2.2.1 i hi
    exact ⟨(List.getElem?_eq_some_iff.mp hget).1, hr⟩
  · intro v n hn
    have hv : v < placed.nodes.length := by
      have h := (List.getElem?_eq_some_iff.mp hn).1
      rwa [hnodes, hlen] at h
    let coord := placed.nodes[v]
    have hc : placed.nodes[v]? = some coord := List.getElem?_eq_getElem hv
    obtain ⟨actual, ha, _, hb, hh⟩ := (proxyWidths_rel stages.hProxy).2.2.2.2.1 v coord hc
    rw [hnodes] at hn
    have he : actual = n := Option.some.inj (ha.symm.trans hn)
    subst actual
    exact ⟨coord, by simpa only [stages.hCoordProper] using hc, hb.symm, hh.symm⟩

private theorem activeC5IndicesOrdered {run : Run} {a b : Nat}
    (ha : 0 ≤ rk run.proper.rank a) (hb : 0 ≤ rk run.proper.rank b)
    (hle : rk run.proper.rank a ≤ rk run.proper.rank b) : bandIndex run a ≤ bandIndex run b := by
  have hna := Int.toNat_of_nonneg ha
  have hnb := Int.toNat_of_nonneg hb
  change (rk run.proper.rank a).toNat ≤ (rk run.proper.rank b).toNat
  omega

/-- This is the remaining geometric input to the selected, non-loop group port proof.
Only the applicable side is required, and only for members of the actual emitted frame. -/
def RegionC5MarkerRankExtreme (run : Run) (v : Nat) (marker : Node) : Prop :=
  ∀ q ∈ run.proper.nodes.zipIdx, q.1.node.clusterPath.contains marker.decl = true →
    if marker.border = -2 then rk run.proper.rank v ≤ rk run.proper.rank q.2
    else rk run.proper.rank q.2 ≤ rk run.proper.rank v

/-- Direct compound edges discharge the rank residual for original leaf members.
The rank inequality accommodates both the active and fallback ranking implementations. -/
theorem componentRunR_compound_leaf_rank_window {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {top bottom member : Node × Nat} (htop : top ∈ cg.nodes.zipIdx) (ht : top.1.border = -2)
    (hbottom : cg.nodes.zipIdx.find? (fun q => q.1.border == 2 && q.1.decl == top.1.decl) =
      some bottom)
    (hmember : member ∈ cg.nodes.zipIdx) (hm : member.1.border = 0)
    (hp : member.1.clusterPath.contains top.1.decl = true) :
    rk run.proper.rank top.2 < rk run.proper.rank member.2 ∧
      rk run.proper.rank member.2 < rk run.proper.rank bottom.2 := by
  have ht' : top ∈ cg.nodes.zipIdx.filter (fun q => q.1.border == -2) :=
    List.mem_filter.mpr ⟨htop, by simp [ht]⟩
  let members := cg.nodes.zipIdx.filter (fun q => q.1.border == 0 && q.1.clusterPath.contains top.1.decl)
  have hm' : member ∈ members :=
    List.mem_filter.mpr ⟨hmember, Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr hm, hp⟩⟩
  have hnotEmpty : members.isEmpty = false := by
    cases h : members with
    | nil => rw [h] at hm'; cases hm'
    | cons _ _ => rfl
  have hconstraints : ∀ e ∈ ([⟨top.2, member.2, 1, 0, false⟩,
      ⟨member.2, bottom.2, 1, 0, false⟩] : List Edge), e ∈ Compound.constraints cg := by
    intro e he
    unfold Compound.constraints
    apply List.mem_flatMap.mpr
    refine ⟨top, ht', ?_⟩
    rw [hbottom]
    change e ∈ (if members.isEmpty && _ then _ else _)
    simp only [hnotEmpty, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨member, hm', he⟩))
  have step (e : Edge) (he : e ∈ Compound.constraints cg) :
      e.minLen ≤ rk run.proper.rank e.head - rk run.proper.rank e.tail := by
    obtain ⟨h0, h1⟩ := constraints_bounded cg e he
    exact componentRunR_compound_feasible hrun he h0 h1
  have h0 := step ⟨top.2, member.2, 1, 0, false⟩ (hconstraints _ (by simp))
  have h1 := step ⟨member.2, bottom.2, 1, 0, false⟩ (hconstraints _ (by simp))
  dsimp only at h0 h1
  omega

private theorem activeCoordinateBottomFlat {P : Params} {exact : List Nat}
    {s : RegionSpec} {labeled : Proper} {v : Nat} {n : ProperNode}
    (hn : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some n)
    (hb : n.node.border = 2) : n.node.h = 0 := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  change (materializeDummyPaths (clearProxyExtents bordered)).nodes[v]? = some n at hn
  obtain ⟨cleared, hc, _, hcb, hch, _⟩ := materialize_lookup _ hn
  rw [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hc
  obtain ⟨t, ht, he⟩ := hc
  subst cleared
  have htb : t.node.border = 2 := (clearF_keys t).2.1.symm.trans (hcb.symm.trans hb)
  obtain ⟨extra, hextra, hmarkers⟩ := addClusterBorders_extra titled P.clusterBorderW
  change (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes[v]? = some t at ht
  rw [hextra] at ht
  by_cases hv : v < titled.nodes.length
  · rw [List.getElem?_append_left hv] at ht
    let titleCopy (q : ProperNode × Nat) : ProperNode :=
      let height := (s.titles.getD q.1.node.decl (0, 0)).2 + P.clusterPad
      { q.1 with node := { q.1.node with border := 3, loopExtent := 0, h := height } }
    have htitled : titled.nodes = sized.nodes.map titleF ++
        (sized.nodes.zipIdx.filter fun q => q.1.node.border == -2).map titleCopy := rfl
    rw [htitled] at ht
    by_cases hs : v < sized.nodes.length
    · rw [List.getElem?_append_left (by simpa only [List.length_map] using hs),
        List.getElem?_map, Option.map_eq_some_iff] at ht
      obtain ⟨src, _, he⟩ := ht
      subst t
      have hk := titleF_keys src
      have hsv : src.node.border = 2 := hk.2.1.symm.trans htb
      exact hch.trans ((clearF_keys _).2.2.2.trans (hk.2.2.2 (Or.inr hsv)))
    · rw [List.getElem?_append_right (by simpa only [List.length_map] using Nat.le_of_not_gt hs),
        List.getElem?_map, Option.map_eq_some_iff] at ht
      obtain ⟨_, _, he⟩ := ht
      have htag : (3 : Int) = 2 :=
        (congrArg (fun p : ProperNode => p.node.border) he).trans htb
      cases htag
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hv)] at ht
    obtain ⟨_, htag⟩ := hmarkers t (List.mem_of_getElem? ht)
    omega

private theorem activePlacedBottomFlat {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm))
    {v : Nat} {coord : ProperNode} (hc : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) : coord.node.h = 0 := by
  obtain ⟨rs, _, _, _, labeled, p, _, _, _, _, placed, _, _, _, hs⟩ :=
    componentRunR_stages hrun
  have hrs : rs = some rm := Except.ok.inj (hs.hRs.symm.trans hactive)
  rcases hs.hPlaced with ⟨hnone, _, _, _, _⟩ | ⟨rm', _, hreg, _, hcross⟩
  · rw [hrs] at hnone
    cases hnone
  have he : rm' = rm := Option.some.inj (hreg.symm.trans hrs)
  subst rm'
  rcases hs.hRank with ⟨_, hnone, _, _, _, _⟩ | ⟨rm', hreg, hrank⟩
  · rw [hrs] at hnone
    cases hnone
  have he : rm' = rm := Option.some.inj (hreg.symm.trans hrs)
  subst rm'
  have hlen : placed.nodes.length = p.nodes.length := by
    have hmap := (crossCoordsR_label_metadata hcross).1
    have h := congrArg List.length hmap
    simpa only [List.length_map] using h
  have hc' : placed.nodes[v]? = some coord := by simpa only [hs.hCoordProper] using hc
  have hv : v < p.nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hc').1
    rwa [hlen] at h
  let src := p.nodes[v]
  have hsrc : p.nodes[v]? = some src := List.getElem?_eq_getElem hv
  obtain ⟨alloc⟩ := crossCoordsR_allocation_stages hcross
  have hinit : alloc.placement.p.nodes[v]? = some src := by rwa [alloc.hPlacement]
  obtain ⟨out, hout, _, hb', _, hh⟩ := reservedMarkerMetadata alloc.hFramesAndPorts hinit
  have he : out = coord := Option.some.inj (hout.symm.trans hc')
  subst out
  have hbSrc := hb'.symm.trans hb
  have hcoord : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some src := by
    rw [hs.hCoord]
    exact hsrc
  have hflat := activeCoordinateBottomFlat hcoord hbSrc
  apply (hh ?_).trans hflat
  intro c hmem he
  have hmem' : c ∈ rm.clusters := by rwa [alloc.hPlacement] at hmem
  obtain ⟨n, hn, htop⟩ := activeClusterWriter hactive hmem'
  rw [← rankEquivalentR_nodes_eq hrank, he] at hn
  have hlabel := addLabelNodes_untouched_node hs.hLabels (normalize_node_record hs.hNorm hn) rfl
  obtain ⟨top, hget, _, hborder, _, _⟩ := activeCoordinateMarker P exact s hlabel (Or.inl htop)
  rw [hs.hCoord] at hget
  have hsame : top = src := Option.some.inj (hget.symm.trans hsrc)
  rw [hsame, hbSrc, htop] at hborder
  cases hborder

/-- The executed active band contains the bottom of every routed node, including
raised top markers. Bottom markers sit at the band boundary and remain flat. -/
theorem componentRunR_active_node_rank_upper {P : Params} {exactIds : List String}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp cg labels orderOptions =
      .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm))
    {v : Nat} (hv : v < run.proper.nodes.length) :
    RouteImpl.yAt run.ys v + RouteImpl.nodeH run.proper v ≤
      run.top.getD (rk run.proper.rank v).toNat 0 +
        CoordsImpl.layerHeight run.coordinateProper
          (run.layers.getD (rk run.proper.rank v).toNat []) := by
  obtain ⟨_, _, hcoords⟩ := activeC5BandData hrun
  obtain ⟨_, hc, _, _⟩ := hcoords (List.getElem?_eq_getElem hv)
  exact ((componentRunR_boundaryRankBands hrun).1 hc
    (activePlacedBottomFlat hrun hactive hc)).2.1


theorem regionC5ActiveMarkerBoundary_of_rank {P : Params} {exactIds : List String}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp cg labels orderOptions =
      .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm))
    {v t : Nat} {n top : Node}
    (hn : cg'.nodes[v]? = some n) (ht : cg'.nodes[t]? = some top)
    (htop : top.border = -2) (hkind : (v = t ∧ n.border = -2) ∨ n.border = 2)
    (howner : n.clusterPath.getLast? = some top.decl) (hdecl : n.decl = top.decl)
    (hrank : RegionC5MarkerRankExtreme run v n)
    {x : Int}
    (hx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ x ∧
      x ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
    Validator.onBoundary ⟨x, RouteImpl.tailPortY run.proper run.ys v⟩ (frameRect P cg' run t) ∧
      Validator.onBoundary ⟨x, (RouteImpl.boxRect run.proper run.xs run.ys v).y⟩
        (frameRect P cg' run t) := by
  have hborder : n.border = -2 ∨ n.border = 2 := by
    rcases hkind with ⟨_, h⟩ | h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨coord, actual, hc, ha, _, had, hcb, hab, hcp, hap, hzero⟩ :=
    componentRunR_active_marker_records hrun hactive hn hborder
  have hbGraph : (cg'.nodes.getD t default).border = -2 := by
    simpa only [List.getD_eq_getElem?_getD, ht, Option.getD_some] using htop
  have hdGraph : (cg'.nodes.getD t default).decl = top.decl := by
    simp only [List.getD_eq_getElem?_getD, ht, Option.getD_some]
  have hcb' : coord.node.border = -2 ∨ coord.node.border = 2 := by rwa [hcb]
  have hco : coord.node.clusterPath.getLast? = some (cg'.nodes.getD t default).decl := by
    rw [hcp, hdGraph]
    exact howner
  have hcontains : actual.node.clusterPath.contains (cg'.nodes.getD t default).decl = true := by
    rw [hap, hdGraph]
    apply List.contains_iff_mem.mpr
    exact List.mem_of_getLast? howner
  have hframeX := regionGroupProxyPortX hrun hc hcb' hbGraph hco hx
  obtain ⟨hdims, hcover, hcoords⟩ := activeC5BandData hrun
  have htLen := componentRunR_original_nodes_covered hrun t (List.getElem?_eq_some_iff.mp ht).1
  have hvLen := (List.getElem?_eq_some_iff.mp ha).1
  have ⟨hvBand, hvRank⟩ := hcover v hvLen
  obtain ⟨hbands, hsep⟩ := componentRunR_boundaryRankBands hrun
  have hflatV (hb : coord.node.border = 2) : coord.node.h = 0 :=
    (hzero (hcb.symm.trans hb)).1
  have hbandV := hbands hc hflatV
  have axes {q : ProperNode × Nat} (hq : q ∈ run.proper.nodes.zipIdx) :
      run.top.getD (bandIndex run q.2) 0 ≤ run.ys.getD q.2 0 ∧
      run.ys.getD q.2 0 + RouteImpl.nodeH run.proper q.2 ≤
        run.top.getD (bandIndex run q.2) 0 + bandHeight run (bandIndex run q.2) ∧
      bandIndex run q.2 < run.layers.length ∧ 0 ≤ rk run.proper.rank q.2 := by
    have hqget := List.mem_zipIdx_iff_getElem?.mp hq
    obtain ⟨cq, hcq, _, _⟩ := hcoords hqget
    have ⟨hqBand, hqRank⟩ := hcover q.2 (List.getElem?_eq_some_iff.mp hqget).1
    have hqBand' := hbands hcq (activePlacedBottomFlat hrun hactive hcq)
    exact ⟨hqBand'.1, hqBand'.2.1, hqBand, hqRank⟩
  have hboundary : Validator.onBoundary ⟨x, run.ys.getD v 0⟩ (frameRect P cg' run t) := by
    rcases hkind with ⟨hvt, hb⟩ | hb
    · have hvY : run.ys.getD v 0 = run.top.getD (bandIndex run v) 0 :=
        hbandV.2.2.1 (hcb.trans hb)
      have hcontain : (run.proper.nodes.getD t default).node.clusterPath.contains
          (cg'.nodes.getD t default).decl = true := by
        have haTop : run.proper.nodes[t]? = some actual := by simpa only [hvt] using ha
        simpa only [List.getD_eq_getElem?_getD, haTop, Option.getD_some] using hcontains
      rw [hvt]
      apply regionGroupTopPortOfMemberY hbGraph htLen hcontain ?_ hdims hframeX
      intro q hq hp
      rw [← hvt]
      obtain ⟨hqlow, _, hqBand, hqRank⟩ := axes hq
      have hr := hrank q hq (by rwa [hdGraph, ← hdecl] at hp)
      rw [ite_eq_left hb] at hr
      have hle := activeC5IndicesOrdered hvRank hqRank hr
      by_cases heq : bandIndex run v = bandIndex run q.2
      · rwa [hvY, heq]
      · have hs := hsep (Nat.lt_of_le_of_ne hle heq) hqBand
        change run.top.getD (bandIndex run v) 0 + bandHeight run (bandIndex run v) ≤
          run.top.getD (bandIndex run q.2) 0 at hs
        have hheight := CoordsImpl.layerHeight_nonneg run.coordinateProper
          (run.layers.getD (bandIndex run v) [])
        change 0 ≤ bandHeight run (bandIndex run v) at hheight
        omega
    · have hvY : run.ys.getD v 0 =
          run.top.getD (bandIndex run v) 0 + bandHeight run (bandIndex run v) :=
        hbandV.2.2.2 (hcb.trans hb)
      have htNN := activeC5BandTopNonneg hrun hvBand
      have hhNN := CoordsImpl.layerHeight_nonneg run.coordinateProper
        (run.layers.getD (bandIndex run v) [])
      change 0 ≤ bandHeight run (bandIndex run v) at hhNN
      apply regionGroupBottomPortOfMemberY hbGraph htLen ha hcontains (hzero hb).2
        (by omega) ?_ hdims hframeX
      intro q hq hp
      obtain ⟨_, hqhigh, _, hqRank⟩ := axes hq
      have hr := hrank q hq (by rwa [hdGraph, ← hdecl] at hp)
      rw [ite_eq_right (show n.border ≠ -2 by omega)] at hr
      have hle := activeC5IndicesOrdered hqRank hvRank hr
      by_cases heq : bandIndex run q.2 = bandIndex run v
      · rw [heq] at hqhigh
        omega
      · have hs := hsep (Nat.lt_of_le_of_ne hle heq) hvBand
        change run.top.getD (bandIndex run q.2) 0 + bandHeight run (bandIndex run q.2) ≤
          run.top.getD (bandIndex run v) 0 at hs
        omega
  have hmarker : actual.node.border = -2 ∨ (actual.node.border = 2 ∧ actual.node.h = 0) := by
    rcases hborder with hb | hb
    · exact Or.inl (hab.trans hb)
    · exact Or.inr ⟨hab.trans hb, (hzero hb).2⟩
  obtain ⟨hTailY, _⟩ := regionRunPortRectEndpointHeights ha had hmarker
  rw [hTailY]
  exact ⟨hboundary, hboundary⟩

private theorem activeCandidateNodes {P : Params} {exactIds : List String}
    {s : RegionSpec} {inp : Input} {g cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {comp : List Nat} {index : Nat} {rm : ComponentRegions}
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) g comp index) labels (candidateOrder index) = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp
      (componentCandidateR (some s) g comp index) = .ok (some rm)) :
    cg'.nodes = (componentCandidate g comp index).nodes := by
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  rw [rankEquivalentR_nodes_eq hrank, componentCandidate_nodes] <;> rfl

private theorem selectedGroupMarkerOwner {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {index v : Nat} {n : Node}
    (hn : (componentCandidate execution.graph comp index).nodes[v]? = some n)
    (hb : n.border = -2 ∨ n.border = 2) :
    n.clusterPath.getLast? = some n.decl := by
  rcases hb with hb | hb
  · obtain ⟨_, _, hp⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq hn hb
    simp [hp]
  · obtain ⟨_, _, hp⟩ := X_cg_bottom_box execution.graph0_eq execution.graph_eq hn hb
    simp [hp]

def SelectedC5GroupMarker (cg : Graph) (run : Run) (v t : Nat) : Prop :=
  ∃ n top, cg.nodes[v]? = some n ∧ cg.nodes[t]? = some top ∧ top.border = -2 ∧
    ((v = t ∧ n.border = -2) ∨ n.border = 2) ∧ n.decl = top.decl ∧
    RegionC5MarkerRankExtreme run v n

def SelectedC5RouteGroupAttachment (P : Params) (cg : Graph) (run : Run)
    (i first last : Nat) : Prop :=
  ∃ rt, run.routes[i]? = some rt ∧
    let tail := (RouteImpl.edgeAt run.proper first).tail
    let head := (RouteImpl.edgeAt run.proper last).head
    let reversed := (cg.edges.map (·.reversed)).getD i false
    (∀ t, SelectedC5GroupMarker cg run tail t →
      ∃ p, (if reversed then rt.points.getLast? else rt.points.head?) = some p ∧
        Validator.onBoundary p (frameRect P cg run t)) ∧
    (∀ t, SelectedC5GroupMarker cg run head t →
      ∃ p, (if reversed then rt.points.head? else rt.points.getLast?) = some p ∧
        Validator.onBoundary p (frameRect P cg run t))

/-- Endpoints are read from the actual rewritten chain and actual route entry.
Reordering changes which published end carries the oriented tail or head. -/
theorem regionC5ActiveRouteGroups_of_rank {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {s : RegionSpec} {comp : List Nat} {index : Nat} {cg : Graph} {run : Run}
    {rm : ComponentRegions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) execution.graph comp index) execution.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) execution.params inp
      (componentCandidateR (some s) execution.graph comp index) = .ok (some rm))
    {i first last : Nat} (hi : i < cg.edges.length)
    (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last) :
    SelectedC5RouteGroupAttachment execution.params cg run i first last := by
  obtain ⟨rt, px, qx, hrt, hpx₀, hpx₁, hqx₀, hqx₁, hpoints⟩ :=
    regionRunPortEndpointsR hrun hi hfirst hlast
  have hnodes := activeCandidateNodes hrun hactive
  have boundary {v t : Nat} (hm : SelectedC5GroupMarker cg run v t)
      {x : Int} (hx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ x ∧
        x ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
          (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
      Validator.onBoundary ⟨x, RouteImpl.tailPortY run.proper run.ys v⟩
          (frameRect execution.params cg run t) ∧
        Validator.onBoundary ⟨x, (RouteImpl.boxRect run.proper run.xs run.ys v).y⟩
          (frameRect execution.params cg run t) := by
    obtain ⟨n, top, hn, ht, htop, hkind, hdecl, hrank⟩ := hm
    have hn' : (componentCandidate execution.graph comp index).nodes[v]? = some n := by
      rwa [← hnodes]
    have hborder : n.border = -2 ∨ n.border = 2 := by
      rcases hkind with ⟨_, hb⟩ | hb
      · exact Or.inl hb
      · exact Or.inr hb
    have howner := selectedGroupMarkerOwner execution hn' hborder
    rw [hdecl] at howner
    exact regionC5ActiveMarkerBoundary_of_rank hrun hactive hn ht htop hkind howner hdecl hrank hx
  refine ⟨rt, hrt, ?_⟩
  dsimp only at hpoints ⊢
  constructor
  · intro t ht
    refine ⟨_, ?_, (boundary ht ⟨hpx₀, hpx₁⟩).1⟩
    by_cases hrev : (cg.edges.map (·.reversed)).getD i false = true
    · simp only [hrev, ↓reduceIte] at hpoints ⊢
      exact hpoints.2
    · simp only [hrev] at hpoints ⊢
      exact hpoints.1
  · intro t ht
    refine ⟨_, ?_, (boundary ht ⟨hqx₀, hqx₁⟩).2⟩
    by_cases hrev : (cg.edges.map (·.reversed)).getD i false = true
    · simp only [hrev, ↓reduceIte] at hpoints ⊢
      exact hpoints.1
    · simp only [hrev] at hpoints ⊢
      exact hpoints.2

private def selectedC5Spec (idSets : List (String × List String)) (P : Params)
    (o : Options) (lines : List (List Measure.Line)) : Option RegionSpec :=
  if idSets.isEmpty then none
  else some ⟨idSets, lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * P.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)⟩

/-- Run-level attachment for the actual portfolio-selected active part of a
successful region scene. `rm` must resolve in this component, not just elsewhere
in the same scene. The rank premise is local to each route terminal. -/
theorem regionC5ChosenActiveRouteGroups_of_rank
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {rm : ComponentRegions}
    (hregion : newComponentRegions (selectedC5Spec idSets execution.params o execution.lines)
      execution.params inp (componentGraph execution.graph part.1) = .ok (some rm)) :
    ∃ s index chosen cg run loops area,
      selectedC5Spec idSets execution.params o execution.lines = some s ∧ index < 5 ∧
      Portfolio.portfolio o.thoroughness (componentTrialR execution.params exactIds (some s)
        inp o execution.graph part.1 execution.measured) = .ok chosen ∧
      chosen.value = (cg, run) ∧
      componentRunR execution.params (exactDecls exactIds inp) (some s) inp
        (componentCandidateR (some s) execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok (cg, run) ∧
      newComponentRegions (some s) execution.params inp
        (componentCandidateR (some s) execution.graph part.1 index) = .ok (some rm) ∧
      componentLoops execution.params cg run execution.measured = .ok loops ∧
      part.2 = { placeComponentExact execution.params cg run 0 execution.measured loops
        with area := area } ∧
      ∀ {i first last : Nat}, i < cg.edges.length →
        (RouteImpl.edgesOf run.proper i).head? = some first →
        (RouteImpl.edgesOf run.proper i).getLast? = some last →
        SelectedC5RouteGroupAttachment execution.params cg run i first last := by
  have hex : ∃ s, selectedC5Spec idSets execution.params o execution.lines = some s := by
    cases hs : selectedC5Spec idSets execution.params o execution.lines with
    | none => rw [hs] at hregion; cases hregion
    | some s => exact ⟨s, rfl⟩
  obtain ⟨s, hs⟩ := hex
  obtain ⟨_, hall⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  have hgeo : ActualPartGeometryR execution.params exactIds
      (selectedC5Spec idSets execution.params o execution.lines) inp o execution.graph
      execution.measured part := hall part hpart
  obtain ⟨index, chosen, cg, run, loops, area, selected, hindex, hportfolio, hvalue,
    ⟨rs, hrs, hselected⟩, hrun, hloops, hpartdef⟩ := hgeo
  have he : rs = some rm := Except.ok.inj (hrs.symm.trans hregion)
  have hsel : selected = some s := hselected.trans (by rw [he, hs] <;> rfl)
  rw [hsel] at hrun
  rw [hs] at hportfolio
  have hactive := componentTrialR_selected_regions index hregion
  have hactive' : newComponentRegions (some s) execution.params inp
      (componentCandidateR (some s) execution.graph part.1 index) = .ok (some rm) := by
    simpa only [hs, Option.isSome_some, ↓reduceIte] using hactive
  exact ⟨s, index, chosen, cg, run, loops, area, hs, hindex, hportfolio, hvalue, hrun,
    hactive', hloops, hpartdef,
    fun hi hf hl => regionC5ActiveRouteGroups_of_rank execution hrun hactive' hi hf hl⟩

end Elegant.Layered.PipelineImpl

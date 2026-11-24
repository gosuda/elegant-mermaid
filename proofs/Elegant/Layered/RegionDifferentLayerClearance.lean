import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.RegionFlatC4
import Elegant.Layered.RegionRunSpec

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem coordinateGraphR_plain_lookup (P : Params) (exact : List Nat)
    (spec : Option RegionSpec) {p : Proper} {v : Nat} {source : ProperNode}
    (hsource : p.nodes[v]? = some source) (hplain : source.node.border = 0) :
    ∃ n, (coordinateGraphR P exact spec p).nodes[v]? = some n ∧ n.node.border = 0 := by
  let sized := sizeProperPortsX P exact p
  let titled := match spec with
    | none => titleReservations sized
    | some s => titleReservationsR s.titles P.clusterPad sized
  have hkeys := sizeProperPortsX_key P exact p v
  change (sized.nodes[v]?).map _ = _ at hkeys
  rw [hsource, Option.map_some] at hkeys
  obtain ⟨n, hn, hkey⟩ := Option.map_eq_some_iff.mp hkeys
  have hb : n.node.border = 0 :=
    (congrArg (fun key : Bool × Int × List Nat => key.2.1) hkey).trans hplain
  have hv : v < sized.nodes.length := (List.getElem?_eq_some_iff.mp hn).1
  have ht : titled.nodes[v]? = some n := by
    cases spec with
    | none =>
      change (titleReservations sized).nodes[v]? = some n
      rw [titleReservations_nodes,
        List.getElem?_append_left (by simpa only [List.length_map] using hv),
        List.getElem?_map, hn]
      simp [titleF, hb]
    | some s =>
      change (titleReservationsR s.titles P.clusterPad sized).nodes[v]? = some n
      unfold titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by simpa only [List.length_map] using hv),
        List.getElem?_map, hn]
      simp [hb]
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  obtain ⟨extra, hbordered, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  have hc : (clearProxyExtents bordered).nodes[v]? = some (clearF n) := by
    rw [clearProxyExtents_nodes, List.getElem?_map]
    change (bordered.nodes[v]?).map clearF = _
    rw [show bordered.nodes = titled.nodes ++ extra from hbordered,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1, ht] <;> rfl
  obtain ⟨nd, hnd, _⟩ := materialize_exists _ hc
  obtain ⟨prior, hprior, _, hbnd, _, _⟩ := materialize_lookup _ hnd
  have he : prior = clearF n := Option.some.inj (hprior.symm.trans hc)
  have hbc : (clearF n).node.border = 0 := (clearF_keys n).2.1.trans hb
  rw [he, hbc] at hbnd
  exact ⟨nd, by cases spec <;> exact hnd, hbnd⟩

/-- Raising a top port changes its height, but preserves the border at every
existing index. -/
private theorem reservedPortsR_border_lookup {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs : List Int} {out : List Int × Proper}
    (h : reservedPortsR pl cg labels xs = .ok out)
    {v : Nat} {n : ProperNode} (hn : pl.p.nodes[v]? = some n) :
    ∃ nd, out.2.nodes[v]? = some nd ∧ nd.node.border = n.node.border := by
  let step (acc : List Int × Array ProperNode) (job : RegionCluster × Nat) :
      Except LayoutError (List Int × Array ProperNode) := do
    let c := job.1
    let footprint := max c.titleH
      (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw LayoutError.domain
    else
      let x ← clusterPortR pl job.2 c.top acc.1
      let x ← clusterPortR pl job.2 c.bottom x
      let top := acc.2.getD c.top default
      pure (x, acc.2.set! c.top
        { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } })
  have keepsBorder : ∀ (jobs : List (RegionCluster × Nat)) (acc res : List Int × Array ProperNode),
      jobs.foldlM step acc = .ok res → ∀ {before : ProperNode}, acc.2[v]? = some before →
      ∃ after, res.2[v]? = some after ∧ after.node.border = before.node.border := by
    intro jobs
    induction jobs with
    | nil =>
      intro acc res hf before hbefore
      simp only [List.foldlM_nil] at hf
      cases Except.ok.inj hf
      exact ⟨before, hbefore, rfl⟩
    | cons job rest ih =>
      intro acc res hf before hbefore
      rw [List.foldlM_cons] at hf
      obtain ⟨mid, hstep, hrest⟩ := bind_ok hf
      have hnext : ∃ next, mid.2[v]? = some next ∧ next.node.border = before.node.border := by
        unfold step at hstep
        dsimp only at hstep
        split at hstep
        · simp at hstep
        · obtain ⟨_, _, hstep⟩ := bind_ok hstep
          obtain ⟨_, _, hstep⟩ := bind_ok hstep
          have hset := (congrArg Prod.snd (Except.ok.inj hstep)).symm
          dsimp only at hset
          rw [hset, Array.set!_eq_setIfInBounds]
          by_cases heq : job.1.top = v
          · rw [heq, Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hbefore).1]
            exact ⟨_, rfl, by simp only [Array.getD_eq_getD_getElem?, hbefore, Option.getD_some]⟩
          · rw [Array.getElem?_setIfInBounds_ne heq]
            exact ⟨before, hbefore, rfl⟩
      obtain ⟨next, hnext, hb⟩ := hnext
      obtain ⟨after, hafter, hba⟩ := ih mid res hrest hnext
      exact ⟨after, hafter, hba.trans hb⟩
  unfold reservedPortsR at h
  obtain ⟨res, hfold, hfinal⟩ := bind_ok h
  have hstart : (pl.p.nodes.toArray)[v]? = some n := by rwa [List.getElem?_toArray]
  obtain ⟨nd, hnd, hb⟩ := keepsBorder pl.rm.clusters.zipIdx (xs, pl.p.nodes.toArray)
    res hfold hstart
  have hnodes : out.2.nodes = res.2.toList :=
    (congrArg (fun pair : List Int × Proper => pair.2.nodes) (Except.ok.inj hfinal)).symm
  exact ⟨nd, by rwa [hnodes, Array.getElem?_toList], hb⟩

private theorem crossCoordsR_border_lookup {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok (xs, pinned, reserved, placed))
    {v : Nat} {n : ProperNode} (hn : p.nodes[v]? = some n) :
    ∃ nd, placed.nodes[v]? = some nd ∧ nd.node.border = n.node.border := by
  unfold crossCoordsR at h
  obtain ⟨_, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    cases h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
    obtain ⟨ports, hports, h⟩ := bind_ok h
    have he : placed = ports.2 := (congrArg
      (fun q : List Int × List (List Nat) × List (Option Int) × Proper => q.2.2.2)
      (Except.ok.inj h)).symm
    rw [he]
    exact reservedPortsR_border_lookup hports hn

/-- Every border-0 frame is contained in its executed rank band, and the
reserved bands remain ordered. No cross-coordinate ordering is needed. -/
theorem componentRunR_plain_rank_bands {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run)) :
    (∀ {v : Nat} {source : Node}, cg'.nodes[v]? = some source → source.border = 0 →
      let r := (rk run.proper.rank v).toNat
      ∃ layer, run.layers[r]? = some layer ∧ v ∈ layer ∧
        run.top.getD r 0 ≤ (frameRect P cg' run v).y ∧
        (frameRect P cg' run v).y + (frameRect P cg' run v).h ≤
          run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper layer) ∧
    (∀ {r s : Nat} {left right : List Nat}, r < s →
      run.layers[r]? = some left → run.layers[s]? = some right →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper left ≤
        run.top.getD s 0) := by
  obtain ⟨_, _, _, _, labeled, pCoord, _, _, _, _, placed, q0, yt, ysMid, stages⟩ :=
    componentRunR_stages hrun
  obtain ⟨y, top⟩ := yt
  have hry := stages.hYt
  have htopLen := (CoordsImpl.rankCoordsWith_length hry).2
  have hyLen := (CoordsImpl.rankCoordsWith_length hry).1
  have hysLen : ysMid.length = placed.nodes.length := by
    rw [← stages.hYsMid]
    simpa only [proxyYs, List.length_map, List.length_zipIdx] using hyLen
  obtain ⟨extra, shifts, _, hnonneg, hprefix, hshiftLen, htopShift, hyShift⟩ :=
    (runHooksShift_exact P exactIds inp cg' labels).shifts placed run.layers ysMid top
      run.ys run.top stages.hReserve
  have hpair : shifts.Pairwise (· ≤ ·) := by
    rw [hprefix]
    exact reserveShift_prefix_pairwise extra hnonneg 0 [] (by simp) (by simp)
  have hlayers : RouteImpl.layersOk run.proper run.layers = true := by
    rcases stages.hLanes with ⟨_, hlanes⟩ | ⟨_, hlanes⟩
    · exact (RouteImpl.routeWithLanes_geometry hlanes).1
    · obtain ⟨base, hbase, _, _⟩ := routeWithLanesR_spec hlanes
      exact (RouteImpl.route_spec hbase).1
  have hcoverage := (RouteImpl.layersOk_spec hlayers).2.2.2.1
  have hrank : run.proper.rank = placed.rank := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel stages.hProxy).2.1
  have htopBound : ∀ {r : Nat} {layer : List Nat}, run.layers[r]? = some layer →
      r < top.length := fun h => htopLen.symm ▸ (List.getElem?_eq_some_iff.mp h).1
  constructor
  · intro v source hv hb
    let r := (rk run.proper.rank v).toNat
    have hlabeled : labeled.nodes[v]? = some ⟨source, false, none, false⟩ :=
      addLabelNodes_untouched_node stages.hLabels (normalize_node_record stages.hNorm hv) rfl
    obtain ⟨initial, hinit, hbinit⟩ := coordinateGraphR_plain_lookup P (exactDecls exactIds inp)
      spec hlabeled hb
    rw [stages.hCoord] at hinit
    obtain ⟨nd, hnd, hbnd⟩ : ∃ nd, placed.nodes[v]? = some nd ∧ nd.node.border = 0 := by
      rcases stages.hPlaced with ⟨_, _, _, _, hplaced⟩ | ⟨_, _, _, _, hplaced⟩
      · rw [hplaced]
        exact ⟨initial, hinit, hbinit⟩
      · obtain ⟨nd, hnd, hborder⟩ := crossCoordsR_border_lookup hplaced hinit
        exact ⟨nd, hnd, hborder.trans hbinit⟩
    have hnonproxy : ¬ (nd.node.border = -2 ∨ nd.node.border = 2) := by simp [hbnd]
    have hproper : run.proper.nodes[v]? = some nd := by
      rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
      exact ((proxyWidths_rel stages.hProxy).2.2.2.2.2 v nd hnd hnonproxy).1
    obtain ⟨layer, hly, hmem, hrnn⟩ := hcoverage v (List.getElem?_eq_some_iff.mp hproper).1
    have hvC := (List.getElem?_eq_some_iff.mp hnd).1
    have hvY : v < y.length := by rw [hyLen]; exact hvC
    have hr : rk placed.rank v = (r : Int) := by
      rw [← hrank]
      exact (Int.toNat_of_nonneg hrnn).symm
    have hrIndex : (rk run.proper.rank v).toNat = r := by
      rw [hrank, hr, Int.toNat_natCast]
    obtain ⟨hlo, hhi⟩ := rankAxis_node_in_band (r := r) hry hly hmem hvC hr
    have hheight : CoordsImpl.nodeH placed v = nd.node.h := by simp only [CoordsImpl.nodeH, hnd]
    rw [hheight] at hhi
    have hproxyY : ysMid.getD v 0 = y.getD v 0 := by
      rw [← stages.hYsMid, proxyYs_getD _ _ _ _ hnd hvY]
      simp [hbnd]
    have hvShift := hyShift v (by rw [hysLen]; exact hvC)
    change run.ys.getD v 0 = ysMid.getD v 0 + shifts.getD (rk placed.rank v).toNat 0 at hvShift
    rw [← hrank, hproxyY, hrIndex] at hvShift
    have hrShift := htopShift r (htopBound hly)
    have hframe : frameRect P cg' run v = nodeRect cg' run v := by
      unfold frameRect
      rw [List.getD_eq_getElem?_getD, hv]
      simp [hb]
    have hrecord : run.proper.nodes.getD v default = nd := by
      rw [List.getD_eq_getElem?_getD, hproper] <;> rfl
    refine ⟨layer, hly, hmem, ?_⟩
    rw [stages.hCoordProper, hframe]
    simp only [nodeRect, hrecord]
    change run.top.getD r 0 ≤ run.ys.getD v 0 ∧
      run.ys.getD v 0 + nd.node.h ≤ run.top.getD r 0 + CoordsImpl.layerHeight placed layer
    rw [hrShift, hvShift]
    exact ⟨by omega, by omega⟩
  · intro r s left right hrs hr hs
    have hsShift : s < shifts.length := by rw [hshiftLen]; exact htopBound hs
    have hrShift : r < shifts.length := by omega
    have hmonotone : shifts.getD r 0 ≤ shifts.getD s 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hrShift, List.getElem?_eq_getElem hsShift]
      exact hpair.rel_getElem_of_lt hrShift hsShift hrs
    have hsep := CoordsImpl.rankAxis_bands_disjoint hry r s left right hrs hr hs
    rw [stages.hCoordProper, htopShift r (htopBound hr), htopShift s (htopBound hs)]
    omega

/-- C2's different-rank case for two plain frames of one successful region
component run, regardless of their cross-axis order or parent. -/
theorem componentRunR_positions_disjointR_different_rank {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run))
    {u v : Nat} {nodeU nodeV : Node}
    (hu : cg'.nodes[u]? = some nodeU) (hv : cg'.nodes[v]? = some nodeV)
    (hbU : nodeU.border = 0) (hbV : nodeV.border = 0)
    (hrank : (rk run.proper.rank u).toNat ≠ (rk run.proper.rank v).toNat) :
    Disjoint (frameRect P cg' run u) (frameRect P cg' run v) := by
  obtain ⟨hband, hsep⟩ := componentRunR_plain_rank_bands hrun
  obtain ⟨_, hlyU, _, hloU, hhiU⟩ := hband hu hbU
  obtain ⟨_, hlyV, _, hloV, hhiV⟩ := hband hv hbV
  apply rect_disjoint_of_y
  rcases Nat.lt_or_gt_of_ne hrank with hlt | hgt
  · exact Or.inl (Int.le_trans (Int.le_def.mpr hhiU)
      (Int.le_trans (hsep hlt hlyU hlyV) (Int.le_def.mpr hloV)))
  · exact Or.inr (Int.le_trans (Int.le_def.mpr hhiV)
      (Int.le_trans (hsep hgt hlyV hlyU) (Int.le_def.mpr hloU)))

end Elegant.Layered.PipelineImpl

import Elegant.Layered.RegionC6TrunkPlacement
import Elegant.Layered.RegionOrdinaryC6Lanes

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Elegant.Layered.PipelineImpl.RegionOrdinaryC6

open RegionImpl RouteImpl

private theorem setAt_other {α : Type} (xs : List α) (i j : Nat) (a d : α) (hne : i ≠ j) :
    (setAt xs i a).getD j d = xs.getD j d := by
  induction xs generalizing i j with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => cases j <;> simp_all [setAt]
    | succ i =>
      cases j with
      | zero => rfl
      | succ j => exact ih _ _ (fun h => hne (congrArg Nat.succ h))

private def NotAnchor (rm : ComponentRegions) (v : Nat) : Prop :=
  ∀ c ∈ rm.clusters, c.top ≠ v ∧ c.bottom ≠ v

private theorem frames_read_plain {pl : RegionPlacement} {P : Params}
    {allocation : RegionAllocation} {xs : List Int} {v : Nat} {n : ProperNode}
    (hn : pl.p.nodes[v]? = some n) (hplain : n.node.border = 0) (haway : NotAnchor pl.rm v) :
    (regionFrames pl P allocation xs).getD v 0 = xs.getD v 0 := by
  unfold regionFrames
  apply OrderImpl.foldl_inv (fun x : List Int => x.getD v 0 = xs.getD v 0) _ _ _ rfl
  intro x hx job hj
  obtain ⟨ht, hb⟩ := haway job.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hj))
  dsimp only
  rw [setAt_other _ _ _ _ _ hb, setAt_other _ _ _ _ _ ht]
  apply OrderImpl.foldl_inv (fun x : List Int => x.getD v 0 = xs.getD v 0) _ _ _ hx
  intro y hy q hq
  by_cases he : q.2 = v
  · have hlookup := List.mem_zipIdx_iff_getElem?.mp hq
    rw [he, hn] at hlookup
    have hz : q.1.node.border = 0 := by rw [← Option.some.inj hlookup, hplain]
    simp only [hz]
    split <;> exact hy
  · have hwrite (value : Int) : (setAt y q.2 value).getD v 0 = xs.getD v 0 :=
      (setAt_other _ _ _ _ _ he).trans hy
    split
    · exact hy
    · split
      · exact hwrite _
      · exact hwrite _
      · exact hwrite _
      · exact hy

private theorem clusterPortR_other {pl : RegionPlacement} {g k v : Nat} {xs ys : List Int}
    (h : clusterPortR pl g k xs = .ok ys) (hk : k ≠ v) :
    ys.getD v 0 = xs.getD v 0 := by
  unfold clusterPortR at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · rw [← Except.ok.inj h, setAt_other _ _ _ _ _ hk]
  · cases h

private theorem reservedPortsR_other {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs out : List Int} {outP : Proper} {v : Nat}
    (h : reservedPortsR pl cg labels xs = .ok (out, outP)) (hanchor : NotAnchor pl.rm v) :
    out.getD v 0 = xs.getD v 0 ∧ outP.nodes[v]? = pl.p.nodes[v]? := by
  let step (acc : List Int × Array ProperNode) (q : RegionCluster × Nat) :
      Except LayoutError (List Int × Array ProperNode) := do
    let c := q.1
    let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      pure (x, acc.2.set! c.top { top with node := { top.node with
        h := max (RouteImpl.nodeH pl.p c.top) footprint } })
  have foldOther (entries : List (RegionCluster × Nat)) (initial fin : List Int × Array ProperNode)
      (hentries : ∀ q ∈ entries, q.1 ∈ pl.rm.clusters)
      (hf : entries.foldlM step initial = .ok fin) :
      fin.1.getD v 0 = initial.1.getD v 0 ∧ fin.2[v]? = initial.2[v]? := by
    induction entries generalizing initial with
    | nil =>
      change Except.ok initial = Except.ok fin at hf
      cases hf
      exact ⟨rfl, rfl⟩
    | cons q qs ih =>
      rw [List.foldlM_cons] at hf
      obtain ⟨mid, hmid, htail⟩ := bind_ok hf
      have hrest := ih mid (fun e he => hentries e (List.mem_cons_of_mem _ he)) htail
      obtain ⟨ht, hb⟩ := hanchor q.1 (hentries q List.mem_cons_self)
      dsimp only [step] at hmid
      split at hmid
      · cases hmid
      · obtain ⟨x1, hx1, hmid⟩ := bind_ok hmid
        obtain ⟨x2, hx2, hmid⟩ := bind_ok hmid
        rw [← Except.ok.inj hmid] at hrest
        refine ⟨hrest.1.trans ((clusterPortR_other hx2 hb).trans (clusterPortR_other hx1 ht)), ?_⟩
        exact hrest.2.trans (by rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne ht])
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = .ok (out, outP) at h
  obtain ⟨fin, hf, h⟩ := bind_ok h
  have hother := foldOther _ _ _ (fun _ he =>
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)) hf
  have hout := Except.ok.inj h
  have hx : out = fin.1 := (congrArg Prod.fst hout).symm
  have hp : outP.nodes = fin.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) hout).symm
  rw [hx, hp, Array.getElem?_toList, ← List.getElem?_toArray]
  exact hother

private theorem anchor_marked_in_graph {P : Params} {s : RegionSpec} {inp : Input}
    {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∀ c ∈ rm.clusters, (∃ n, cg.nodes[c.top]? = some n ∧ n.border ≠ 0) ∧
      (∃ n, cg.nodes[c.bottom]? = some n ∧ n.border ≠ 0) := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bind_ok h
    split at h
    · cases h
    · have hclusters : rm.clusters = clusterRows inp s cg :=
        (congrArg ComponentRegions.clusters (Option.some.inj (Except.ok.inj h))).symm
      intro c hc
      rw [hclusters] at hc
      unfold clusterRows at hc
      obtain ⟨q, hq, hc⟩ := List.mem_filterMap.mp hc
      dsimp only at hc
      split at hc
      · cases hc
      · rename_i hb
        have htop : ∃ n, cg.nodes[q.2]? = some n ∧ n.border ≠ 0 := by
          refine ⟨q.1, List.mem_zipIdx_iff_getElem?.mp hq, ?_⟩
          intro he
          simp [he] at hb
        rw [← Option.some.inj hc]
        refine ⟨htop, ?_⟩
        dsimp only
        split
        · rename_i bottom hbottom
          refine ⟨bottom.1, List.mem_zipIdx_iff_getElem?.mp
            (List.mem_of_find?_eq_some hbottom), ?_⟩
          have htest := List.find?_some hbottom
          intro he
          simp [he] at htest
        · exact htop

/-- The selected crossing's source and the router's final rectangle read the same
plain node; only that node's allocation visit changes its final cross coordinate. -/
theorem actualPlainNode_record {P : Params} {exact : List Nat} {s : RegionSpec}
    {inp : Input} {candidate cg : Graph} {labels : List MeasuredLabel} {order : OrderOptions}
    {rm : ComponentRegions} {run : Run} {p p₀ labeled : Proper} {ranks : List Int} {budget : Bool}
    {minimum : RegionConstraints} {layers : List (List Nat)} {reserved : List (Option Int)}
    (hrun : componentRunR P exact (some s) inp candidate labels order = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hrank : rankEquivalentR rm candidate = .ok (ranks, cg, budget))
    (hnormal : normalize cg ranks = .ok p₀)
    (hlabels : Labels.addLabelNodes cg p₀ (componentLabels cg labels) = .ok labeled)
    (hcoord : coordinateGraphR P exact (some s) labeled = p)
    (st : RegionCrossAllocationStages P rm cg labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    {v : Nat} {source : Node} (hv : cg.nodes[v]? = some source) (hb : source.border = 0) :
    ∃ n, p.nodes[v]? = some n ∧ n.node.border = 0 ∧ run.proper.nodes[v]? = some n ∧
      run.xs.getD v 0 = st.shifted.getD v 0 := by
  obtain ⟨n, hn, hplain, _, _⟩ := regionCoordinatePlainDims P exact (some s)
    (addLabelNodes_untouched_node hlabels (normalize_node_record hnormal hv) rfl) hb
  rw [hcoord] at hn
  have haway : NotAnchor st.placement.rm v := by
    rw [st.hPlacement]
    intro c hc
    obtain ⟨ht, hb'⟩ := anchor_marked_in_graph hactive c hc
    have marked {k : Nat} (hm : ∃ nd, candidate.nodes[k]? = some nd ∧ nd.border ≠ 0) : k ≠ v := by
      obtain ⟨nd, hnd, hmark⟩ := hm
      intro hk
      subst k
      rw [← rankEquivalentR_nodes_eq hrank, hv] at hnd
      exact hmark ((congrArg Node.border (Option.some.inj hnd)).symm.trans hb)
    exact ⟨marked ht, marked hb'⟩
  have hp : st.placement.p.nodes[v]? = some n := by rw [st.hPlacement]; exact hn
  obtain ⟨hx, hr⟩ := reservedPortsR_other st.hFramesAndPorts haway
  have hc := hr.trans hp
  have hxs := hx.trans (frames_read_plain hp hplain haway)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, _, _, _, trace⟩ := componentRunR_stages hrun
  have hnot : ¬ (n.node.border = -2 ∨ n.node.border = 2) := by simp [hplain]
  have hl : placed.nodes[v]? = some n := by rwa [← trace.hCoordProper]
  have hproper : run.proper.nodes[v]? = some n := by
    rw [← trace.hDrop, OrderImpl.dropSynthetic_nodes]
    exact ((proxyWidths_rel trace.hProxy).2.2.2.2.2 v n hl hnot).1
  exact ⟨n, hn, hplain, hproper, (componentRunR_placement_xsR hrun hc hnot).trans hxs⟩

end Elegant.Layered.PipelineImpl.RegionOrdinaryC6

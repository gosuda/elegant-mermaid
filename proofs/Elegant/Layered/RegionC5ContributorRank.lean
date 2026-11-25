import Elegant.Layered.RegionC5TerminalOrigRank

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem c5ReservedPathAt {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper}
    (hr : reservedPortsR pl cg labels xs = .ok (ys, placed)) (v : Nat) :
    (placed.nodes[v]?).map (fun n => n.node.clusterPath) =
      (pl.p.nodes[v]?).map (fun n => n.node.clusterPath) := by
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
  let key := fun (n : ProperNode) => n.node.clusterPath
  have preserve (entries : List (RegionCluster × Nat)) (start finish : List Int × Array ProperNode)
      (hfold : entries.foldlM step start = .ok finish) :
      (finish.2[v]?).map key = (start.2[v]?).map key := by
    induction entries generalizing start with
    | nil => rw [show start = finish from Except.ok.inj hfold]
    | cons q rest ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨mid, hmid, hrest⟩ := bind_ok hfold
      rw [ih mid hrest]
      dsimp only [step] at hmid
      split at hmid
      · cases hmid
      obtain ⟨_, _, hmid⟩ := bind_ok hmid
      obtain ⟨_, _, hmid⟩ := bind_ok hmid
      rw [← Except.ok.inj hmid]
      dsimp only
      rw [Array.set!_eq_setIfInBounds]
      by_cases he : q.1.top = v
      · rw [he]
        by_cases hv : v < start.2.size
        · rw [Array.getElem?_setIfInBounds_self_of_lt hv, Array.getElem?_eq_getElem hv]
          have hget : start.2.getD v default = start.2[v]'hv := by
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hv, Option.getD_some]
          simp only [hget, Option.map_some, key]
        · have hn : start.2[v]? = none := Array.getElem?_eq_none (Nat.le_of_not_gt hv)
          rw [Array.getElem?_setIfInBounds_self, hn] <;> simp [hv]
      · rw [Array.getElem?_setIfInBounds_ne he]
  unfold reservedPortsR at hr
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = _ at hr
  obtain ⟨out, hfold, hresult⟩ := bind_ok hr
  have harray : placed.nodes = out.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hresult)).symm
  rw [harray, Array.getElem?_toList]
  simpa only [List.getElem?_toArray, key] using preserve _ _ _ hfold

private theorem c5TitledSource {P : Params} {exact : List Nat} {s : RegionSpec}
    {labeled : Proper} (hAlign : labeled.nodes.length = labeled.rank.length)
    {v : Nat} {n : ProperNode}
    (hn : (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled)).nodes[v]? = some n) :
    (∃ old, labeled.nodes[v]? = some old ∧ n.dummy = old.dummy ∧
      n.node.border = old.node.border ∧ n.node.clusterPath = old.node.clusterPath) ∨
    (∃ j old, labeled.nodes[j]? = some old ∧ old.node.border = -2 ∧
      n.dummy = old.dummy ∧ n.node.border = 3 ∧ n.node.clusterPath = old.node.clusterPath ∧
      rk (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled)).rank v =
        rk labeled.rank j) := by
  let sized := sizeProperPortsX P exact labeled
  let copy (q : ProperNode × Nat) : ProperNode :=
    { q.1 with
      node := { q.1.node with
        border := 3
        loopExtent := 0
        h := (s.titles.getD q.1.node.decl (0, 0)).2 + P.clusterPad } }
  change (sized.nodes.map titleF ++ (titleNodes sized).map copy)[v]? = some n at hn
  have hlen : sized.nodes.length = labeled.rank.length :=
    (sizeProperPortsX_length P exact labeled).trans hAlign
  by_cases hv : v < sized.nodes.length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using hv),
      List.getElem?_map] at hn
    obtain ⟨src, hsrc, rfl⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨old, hold, hd, hb, hp⟩ := X_sizeProperPorts_node_origin P exact labeled hsrc
    obtain ⟨hd', hb', hp', _⟩ := titleF_keys src
    exact Or.inl ⟨old, hold, hd'.trans hd, hb'.trans hb, hp'.trans hp⟩
  · have hge : (sized.nodes.map titleF).length ≤ v := by simpa only [List.length_map] using Nat.le_of_not_gt hv
    rw [List.getElem?_append_right hge, List.length_map, List.getElem?_map] at hn
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨hsrc, htop⟩ := titleNodes_spec hq
    obtain ⟨old, hold, hd, hb, hp⟩ := X_sizeProperPorts_node_origin P exact labeled hsrc
    refine Or.inr ⟨q.2, old, hold, hb.symm.trans htop, hd, rfl, hp, ?_⟩
    change rk (labeled.rank ++ (titleNodes sized).map (fun q => rk labeled.rank q.2)) v = _
    rw [NormalizeImpl.rk_append_right (show labeled.rank.length ≤ v by omega)]
    rw [← hlen]
    simp only [rk, List.getD_eq_getElem?_getD, List.getElem?_map, hq,
      Option.map_some, Option.getD_some]

private theorem c5NormalizedRankPosition {cg : Graph} {ranks : List Int} {p : Proper}
    (hn : normalize cg ranks = .ok p) {edge : Edge} {chain : List Nat}
    (hhead : chain.head? = some edge.tail)
    (hstep : ∀ (j : Nat) (hj : j < chain.length) (hk : j + 1 < chain.length),
      ∃ pe ∈ p.edges, pe.tail = chain[j] ∧ pe.head = chain[j + 1]) :
    ∀ (j v : Nat), chain[j]? = some v → rk p.rank v = rk p.rank edge.tail + (j : Int) := by
  intro j
  induction j with
  | zero =>
    intro v hv
    rw [← List.head?_eq_getElem?, hhead] at hv
    have he := Option.some.inj hv
    subst v
    simp
  | succ j ih =>
    intro v hv
    obtain ⟨hbound, hvalue⟩ := List.getElem?_eq_some_iff.mp hv
    have hj : j < chain.length := by omega
    have hr := ih chain[j] (List.getElem?_eq_getElem hj)
    obtain ⟨pe, he, htail, hnext⟩ := hstep j hj hbound
    have hspan := normalize_proper cg ranks p hn pe he
    unfold Proper.span at hspan
    rw [htail, hnext] at hspan
    have hv' : chain[j + 1] = v := hvalue
    rw [hv'] at hspan
    rw [Int.natCast_succ]
    omega

private theorem c5SelectedNormalizedChain {cg : Graph} {ranks : List Int} {p : Proper}
    (hn : normalize cg ranks = .ok p) {chain : List Nat} (hchain : chain ∈ p.chains)
    {v : Nat} (hv : v ∈ chain) :
    ∃ edge ∈ cg.edges, chain.headD v = edge.tail ∧ chain.getLastD v = edge.head ∧
      rk p.rank edge.tail ≤ rk p.rank v ∧ rk p.rank v ≤ rk p.rank edge.head := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hchain
  obtain ⟨hiBound, _⟩ := List.getElem?_eq_some_iff.mp hi
  have hiEdge : i < cg.edges.length := by rwa [← normalize_chains_length hn]
  let edge := cg.edges[i]'hiEdge
  have he : cg.edges[i]? = some edge := List.getElem?_eq_getElem hiEdge
  obtain ⟨_, hfact⟩ := (normalize_ok hn).2.2 i hiEdge edge he
  have hne : edge.tail ≠ edge.head := by
    intro hself
    rw [ite_eq_left hself] at hfact
    have hnil : chain = [] := Option.some.inj (hi.symm.trans hfact)
    rw [hnil] at hv
    exact List.not_mem_nil hv
  rw [ite_eq_right hne] at hfact
  obtain ⟨members, hmembers, _, hhead, hlast, hsteps⟩ := hfact
  have heq : members = chain := Option.some.inj (hmembers.symm.trans hi)
  subst members
  have rankAt := c5NormalizedRankPosition hn (edge := edge) (chain := chain) hhead (fun j hj hk => by
    obtain ⟨pe, hpe, _, _, ht, hh⟩ := hsteps j hj hk
    exact ⟨pe, hpe, ht, hh⟩)
  obtain ⟨position, hposition⟩ := List.mem_iff_getElem?.mp hv
  obtain ⟨hpositionBound, _⟩ := List.getElem?_eq_some_iff.mp hposition
  have hlastGet : chain[chain.length - 1]? = some edge.head := by
    rwa [← List.getLast?_eq_getElem?]
  have hvRank := rankAt position v hposition
  have hheadRank := rankAt (chain.length - 1) edge.head hlastGet
  refine ⟨edge, List.mem_of_getElem? he, ?_, ?_, ?_, ?_⟩
  · rw [List.headD_eq_head?_getD, hhead, Option.getD_some]
  · rw [List.getLastD_eq_getLast?, hlast, Option.getD_some]
  · calc
      rk p.rank edge.tail ≤ rk p.rank edge.tail + (position : Int) :=
        Int.le_add_of_nonneg_right (Int.natCast_nonneg position)
      _ = rk p.rank v := hvRank.symm
  · have hcast : (position : Int) ≤ ((chain.length - 1 : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.le_sub_one_of_lt hpositionBound)
    calc
      rk p.rank v = rk p.rank edge.tail + (position : Int) := hvRank
      _ ≤ rk p.rank edge.tail + ((chain.length - 1 : Nat) : Int) :=
        Int.add_le_add_left hcast _
      _ = rk p.rank edge.head := hheadRank.symm

/-- Every emitted frame contributor is bracketed by actual candidate records carrying its owner.
For a dummy these are the endpoints of its own normalized semantic chain. -/
theorem activeFrameContributorRankSources
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {s : RegionSpec} {index : Nat} {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) execution.graph comp index) execution.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) execution.params inp
      (componentCandidateR (some s) execution.graph comp index) = .ok (some rm))
    {v owner : Nat} {n : ProperNode} (hn : run.proper.nodes[v]? = some n)
    (howner : n.node.clusterPath.contains owner = true) :
    ∃ a b na nb, cg.nodes[a]? = some na ∧ cg.nodes[b]? = some nb ∧
      na.clusterPath.contains owner = true ∧ nb.clusterPath.contains owner = true ∧
      rk run.proper.rank a ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ rk run.proper.rank b := by
  let P := execution.params
  let exact := exactDecls exactIds inp
  obtain ⟨ranks, p0, labeled, p, _, _, _, _, hre, hnorm, hlabels, hcoord, _, _, ⟨alloc⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, q0, _, _, hs⟩ := componentRunR_stages hrun
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  let cleared := clearProxyExtents bordered
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes]
  have hv := (List.getElem?_eq_some_iff.mp hn).1
  have hvPlaced : v < placed.nodes.length := by rwa [hnodes, (proxyWidths_rel hs.hProxy).2.2.1] at hv
  obtain ⟨out, hout⟩ : ∃ out, placed.nodes[v]? = some out := ⟨_, List.getElem?_eq_getElem hvPlaced⟩
  obtain ⟨n', hn', _, _, hnPath⟩ := proxyWidths_decl_path hs.hProxy hout
  rw [hnodes] at hn
  have hsame := Option.some.inj (hn'.symm.trans hn)
  subst n'
  have hout' : run.coordinateProper.nodes[v]? = some out := by rwa [hs.hCoordProper]
  have hpath := c5ReservedPathAt alloc.hFramesAndPorts v
  rw [hout', alloc.hPlacement] at hpath
  change some out.node.clusterPath = (p.nodes[v]?).map (fun n => n.node.clusterPath) at hpath
  obtain ⟨current, hcur, he⟩ := Option.map_eq_some_iff.mp hpath.symm
  have hcur' : (materializeDummyPaths cleared).nodes[v]? = some current := by
    change (coordinateGraphR P exact (some s) labeled).nodes[v]? = some current
    rwa [hcoord]
  have hfinRank : run.proper.rank = run.coordinateProper.rank := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_rank, hs.hCoordProper]
    exact (proxyWidths_rel hs.hProxy).2.1
  have hplaceRank : run.coordinateProper.rank = p.rank := by
    have hh := alloc.hFramesAndPorts
    unfold reservedPortsR at hh
    obtain ⟨_, _, hh⟩ := bind_ok hh
    have hh := congrArg (fun q : List Int × Proper => q.2.rank) (Except.ok.inj hh)
    change alloc.placement.p.rank = run.coordinateProper.rank at hh
    rw [alloc.hPlacement] at hh
    exact hh.symm
  have hfr : run.proper.rank = bordered.rank := hfinRank.trans (hplaceRank.trans (by rw [← hcoord]; rfl))
  have halign : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hlabels, (Labels.addLabelNodes_metadata hlabels).2.1]
    exact (normalize_node_rank_alignment hnorm).1
  have hSizedLength : sized.nodes.length = labeled.nodes.length :=
    sizeProperPortsX_length P exact labeled
  have hTitleLength : titled.nodes.length = titled.rank.length := by
    change (sized.nodes.map titleF ++ (titleNodes sized).map _).length =
      (labeled.rank ++ (titleNodes sized).map _).length
    simp only [List.length_append, List.length_map]
    rw [hSizedLength, halign]
  obtain ⟨extraR, hBorderRank⟩ := addClusterBorders_rank_prefix titled P.clusterBorderW
  have htitleRank (j : Nat) (hj : j < titled.nodes.length) :
      rk run.proper.rank j = rk titled.rank j := by
    rw [hfr, hBorderRank, NormalizeImpl.rk_append_left (by rwa [← hTitleLength])]
  have hlabRank (j : Nat) (hj : j < labeled.nodes.length) :
      rk run.proper.rank j = rk labeled.rank j := by
    have hjr : j < labeled.rank.length := by rwa [← halign]
    have ht : j < titled.nodes.length := by
      change j < (sized.nodes.map titleF ++ (titleNodes sized).map _).length
      simp only [List.length_append, List.length_map]
      rw [hSizedLength]
      exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
    rw [htitleRank j ht]
    exact NormalizeImpl.rk_append_left hjr
  have hcnodes : (componentCandidate execution.graph comp index).nodes = cg.nodes := by
    rw [componentCandidate_nodes, rankEquivalentR_nodes_eq hre] <;> rfl
  have hmarkers (j : Nat) (node : Node) (hj : cg.nodes[j]? = some node) :=
    X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq
      (show (componentCandidate execution.graph comp index).nodes[j]? = some node by rwa [hcnodes])
  have hKeys := addLabelNodes_keys _ _ _ (normalize_keys hnorm) hlabels
  have realOrigin {j : Nat} {m : ProperNode} (hm : labeled.nodes[j]? = some m) (hd : m.dummy = false) :
      ∃ old, cg.nodes[j]? = some old ∧ m.node.border = old.border ∧ m.node.clusterPath = old.clusterPath := by
    rcases hKeys j m hm with ⟨old, hOld, _, hb, hp⟩ | ⟨htrue, _, _⟩
    · exact ⟨old, hOld, hb, hp⟩
    · simp [hd] at htrue
  have titledOrig {j : Nat} {m : ProperNode} (hm : titled.nodes[j]? = some m)
      (hborder : m.node.border = -2 ∨ m.node.border = 2) :
      ∃ old, cg.nodes[j]? = some old ∧ m.node.border = old.border ∧ m.node.clusterPath = old.clusterPath := by
    rcases c5TitledSource (P := P) (exact := exact) (s := s) halign hm with
      ⟨src, hsrc, _, hb, hp⟩ | ⟨_, _, _, _, _, hb, _, _⟩
    · rcases hKeys j src hsrc with ⟨old, hOld, _, hbo, hpo⟩ | ⟨_, hz, _⟩
      · exact ⟨old, hOld, hb.trans hbo, hp.trans hpo⟩
      · rw [hz] at hb
        rcases hborder with h | h <;> omega
    · rcases hborder with h | h <;> omega
  have hready : OrderImpl.BorderConstructionReady titled := by
    refine ⟨?_, ?_, ?_, hTitleLength, ?_⟩
    · intro m hm
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
      rcases c5TitledSource (P := P) (exact := exact) (s := s) halign hj with
        ⟨src, hsrc, _, hb, _⟩ | ⟨_, _, _, _, _, hb, _, _⟩
      · rcases hKeys j src hsrc with ⟨old, hOld, _, hbo, _⟩ | ⟨_, hz, _⟩
        · rw [hb, hbo]
          rcases (hmarkers j old hOld).1 with h | h | h <;> omega
        · rw [hb, hz]
          decide
      · rw [hb]
        decide
    · intro m hm ht
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
      obtain ⟨old, hOld, hb, hp⟩ := titledOrig hj (Or.inl ht)
      rw [hp]
      exact (hmarkers j old hOld).2 (hb.symm.trans ht)
    · intro a b na nb ha hb hba hbb hp
      obtain ⟨oa, hoa, hboa, hpa⟩ := titledOrig ha (Or.inl hba)
      obtain ⟨ob, hob, hbob, hpb⟩ := titledOrig hb (Or.inl hbb)
      exact X_cg_top_unique execution.graph0_eq execution.graph_eq hcomp
        (by rwa [hcnodes]) (by rwa [hcnodes]) (hboa.symm.trans hba) (hbob.symm.trans hbb)
        (hpa.symm.trans (hp.trans hpb))
    · intro m hm hd
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
      rcases c5TitledSource (P := P) (exact := exact) (s := s) halign hj with
        ⟨src, hsrc, hd', hb, _⟩ | ⟨k, src, hsrc, _, hd', _, _, _⟩
      · rcases hKeys j src hsrc with ⟨_, _, hfalse, _, _⟩ | ⟨_, hz, _⟩
        · simp [hd', hfalse] at hd
        · exact hb.trans hz
      · rcases hKeys k src hsrc with ⟨_, _, hfalse, _, _⟩ | ⟨_, hz, _⟩
        · simp [hd', hfalse] at hd
        · omega
  obtain ⟨before, hbefore, _, _, _, hreal⟩ := materialize_lookup cleared hcur'
  have hCurrentOwner : current.node.clusterPath.contains owner = true := by
    rw [he, ← hnPath.2]
    exact howner
  rw [clearProxyExtents_nodes, List.getElem?_map] at hbefore
  obtain ⟨origin, horigin, horiginEq⟩ := Option.map_eq_some_iff.mp hbefore
  have hbeforeGet : cleared.nodes[v]? = some before := by
    rw [clearProxyExtents_nodes, List.getElem?_map, horigin, Option.map_some, horiginEq]
  have hdummy : before.dummy = origin.dummy := by rw [← horiginEq]; exact (clearF_keys _).1
  have hsingle {j : Nat} {old : Node} (hj : cg.nodes[j]? = some old)
      (hown : old.clusterPath.contains owner = true) (hr : rk run.proper.rank v = rk run.proper.rank j) :
      ∃ a b na nb, cg.nodes[a]? = some na ∧ cg.nodes[b]? = some nb ∧
        na.clusterPath.contains owner = true ∧ nb.clusterPath.contains owner = true ∧
        rk run.proper.rank a ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ rk run.proper.rank b :=
    ⟨j, j, old, old, hj, hj, hown, hown, Int.le_of_eq hr.symm, Int.le_of_eq hr⟩
  obtain ⟨extra, hborderNodes, hextra⟩ := addClusterBorders_extra titled P.clusterBorderW
  by_cases hvt : v < titled.nodes.length
  · have htorigin := horigin
    rw [show bordered.nodes = titled.nodes ++ extra from hborderNodes,
      List.getElem?_append_left hvt] at htorigin
    rcases c5TitledSource (P := P) (exact := exact) (s := s) halign htorigin with
      ⟨src, hsrc, hdSrc, _, hpSrc⟩ | ⟨j, src, hsrc, htop, hdSrc, _, hpSrc, hr⟩
    · by_cases hsrcReal : src.dummy = false
      · obtain ⟨old, hOld, _, hp⟩ := realOrigin hsrc hsrcReal
        have hc := hreal (hdummy.trans (hdSrc.trans hsrcReal))
        rw [hc, ← horiginEq, (clearF_keys _).2.2.1, hpSrc, hp] at hCurrentOwner
        exact hsingle hOld hCurrentOwner rfl
      · have htrue : before.dummy = true :=
          hdummy.trans (hdSrc.trans (Bool.eq_true_of_ne_false hsrcReal))
        have hpp : current.node.clusterPath = OrderImpl.nodePath cleared v := by
          unfold materializeDummyPaths at hcur'
          simp only [List.getElem?_map, List.getElem?_zipIdx, hbeforeGet, Option.map_some,
            Nat.zero_add, htrue, ↓reduceIte, Option.some.injEq] at hcur'
          rw [← hcur']
        have hchains : cleared.chains = p0.chains :=
          (OrderImpl.addClusterBorders_metadata titled P.clusterBorderW).2.1.trans
            (Labels.addLabelNodes_metadata hlabels).2.2.1
        have hmember : owner ∈ OrderImpl.nodePath cleared v := by
          rw [← hpp]
          exact List.contains_iff_mem.mp hCurrentOwner
        have hbeforeD : cleared.nodes.getD v default = before := by
          rw [List.getD_eq_getElem?_getD, hbeforeGet, Option.getD_some]
        unfold OrderImpl.nodePath at hmember
        simp only [hbeforeD, htrue, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmember
        generalize hfind : cleared.chains.find? (fun chain : List Nat => chain.contains v) = selected at hmember
        cases selected with
        | none => exact (List.not_mem_nil hmember).elim
        | some chain =>
          have hchain : chain ∈ p0.chains := by
            rw [← hchains]
            exact List.mem_of_find?_eq_some hfind
          have hvChain : v ∈ chain := List.contains_iff_mem.mp
            (List.find?_some (p := fun members : List Nat => members.contains v) hfind)
          obtain ⟨e, he, hh, hl, hlo, hhi⟩ := c5SelectedNormalizedChain hnorm hchain hvChain
          obtain ⟨htail, hhead, _⟩ :=
            RankImpl.wellformed_spec (normalize_node_rank_alignment hnorm).2 e he
          have endpoint {j : Nat} (hj : j < cg.nodes.length) :
              ∃ old q, cg.nodes[j]? = some old ∧ cleared.nodes[j]? = some q ∧
                q.node.clusterPath = old.clusterPath ∧ rk run.proper.rank j = rk p0.rank j := by
            let old := cg.nodes[j]
            have hOld : cg.nodes[j]? = some old := List.getElem?_eq_getElem hj
            have hL := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hOld) rfl
            have hLlt := (List.getElem?_eq_some_iff.mp hL).1
            have hSzLt : j < sized.nodes.length := by rwa [hSizedLength]
            let sz := sized.nodes[j]
            have hSz : sized.nodes[j]? = some sz := List.getElem?_eq_getElem hSzLt
            obtain ⟨oldL, hOldL, _, _, hpathL⟩ := X_sizeProperPorts_node_origin P exact labeled hSz
            have hsame := Option.some.inj (hOldL.symm.trans hL)
            have hT : titled.nodes[j]? = some (titleF sz) := by
              change (sized.nodes.map titleF ++ (titleNodes sized).map _)[j]? = _
              rw [List.getElem?_append_left (by simpa only [List.length_map] using hSzLt),
                List.getElem?_map, hSz, Option.map_some]
            have hB : bordered.nodes[j]? = some (titleF sz) := by
              rw [hborderNodes, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hT).1, hT]
            refine ⟨old, clearF (titleF sz), hOld, ?_, ?_, ?_⟩
            · rw [clearProxyExtents_nodes, List.getElem?_map, hB, Option.map_some]
            · rw [(clearF_keys _).2.2.1, (titleF_keys _).2.2.1, hpathL, hsame]
            · rw [hlabRank j hLlt, (Labels.addLabelNodes_metadata hlabels).2.1]
          obtain ⟨na, _, ha, hqa, hpa, hra⟩ := endpoint htail
          obtain ⟨nb, _, hb, hqb, hpb, hrb⟩ := endpoint hhead
          simp only [hh, hl, List.getD_eq_getElem?_getD, hqa, hqb, Option.getD_some,
            hpa, hpb] at hmember
          obtain ⟨hoa, hob⟩ := commonPath_member_both _ _ hmember
          have hvr : rk run.proper.rank v = rk p0.rank v := by
            rw [hlabRank v (List.getElem?_eq_some_iff.mp hsrc).1, (Labels.addLabelNodes_metadata hlabels).2.1]
          refine ⟨e.tail, e.head, na, nb, ha, hb, List.contains_iff_mem.mpr hoa,
            List.contains_iff_mem.mpr hob, ?_, ?_⟩
          · calc
              rk run.proper.rank e.tail = rk p0.rank e.tail := hra
              _ ≤ rk p0.rank v := hlo
              _ = rk run.proper.rank v := hvr.symm
          · calc
              rk run.proper.rank v = rk p0.rank v := hvr
              _ ≤ rk p0.rank e.head := hhi
              _ = rk run.proper.rank e.head := hrb.symm
    · have hTopReal : src.dummy = false := by
        rcases hKeys j src hsrc with ⟨_, _, h, _, _⟩ | ⟨_, hz, _⟩
        · exact h
        · omega
      obtain ⟨old, hOld, _, hp⟩ := realOrigin hsrc hTopReal
      have hc := hreal (hdummy.trans (hdSrc.trans hTopReal))
      rw [hc, ← horiginEq, (clearF_keys _).2.2.1, hpSrc, hp] at hCurrentOwner
      exact hsingle hOld hCurrentOwner ((htitleRank _ hvt).trans (hr.trans (hlabRank _ (List.getElem?_eq_some_iff.mp hsrc).1).symm))
  · have hx := horigin
    rw [show bordered.nodes = titled.nodes ++ extra from hborderNodes,
      List.getElem?_append_right (Nat.le_of_not_gt hvt)] at hx
    obtain ⟨hd', hside⟩ := hextra origin (List.mem_of_getElem? hx)
    have hc := hreal (hdummy.trans hd')
    obtain ⟨a, ha, b, hb, hp, hvNN, hlo, hhi⟩ := addClusterBorders_side_rank_bounds _ _ hready horigin hside
    obtain ⟨haMem, haTag⟩ := List.mem_filter.mp ha
    have haT : a.1.node.border = -2 := by simpa only [beq_iff_eq] using haTag
    have hbT : b.1.node.border = 2 ∧ b.1.node.clusterPath = a.1.node.clusterPath := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using
        List.find?_some (p := fun entry : ProperNode × Nat =>
          entry.1.node.border == 2 && entry.1.node.clusterPath == a.1.node.clusterPath) hb
    have haGet := List.mem_zipIdx_iff_getElem?.mp haMem
    have hbGet := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hb)
    obtain ⟨na, hna, _, hpa⟩ := titledOrig haGet (Or.inl haT)
    obtain ⟨nb, hnb, _, hpb⟩ := titledOrig hbGet (Or.inr hbT.1)
    rw [hc, ← horiginEq, (clearF_keys _).2.2.1, hp] at hCurrentOwner
    have hownA : na.clusterPath.contains owner = true := by rwa [← hpa]
    have hownB : nb.clusterPath.contains owner = true := by rwa [← hpb, hbT.2]
    have hra := htitleRank a.2 (List.getElem?_eq_some_iff.mp haGet).1
    have hrb := htitleRank b.2 (List.getElem?_eq_some_iff.mp hbGet).1
    have hlayers : RouteImpl.layersOk run.proper run.layers = true := by
      rcases hs.hLanes with ⟨_, h⟩ | ⟨_, h⟩
      · exact (RouteImpl.routeWithLanes_geometry h).1
      · exact (rcbRouteWithLanesR_geometry h).1
    obtain ⟨_, _, _, hcoverage, _⟩ := RouteImpl.layersOk_spec hlayers
    have nonneg {j : Nat} {m : Node} (hj : cg.nodes[j]? = some m) : 0 ≤ rk run.proper.rank j := by
      obtain ⟨hjBound, _⟩ := List.getElem?_eq_some_iff.mp hj
      obtain ⟨_, _, _, hnonnegative⟩ := hcoverage j
        (componentRunR_original_nodes_covered hrun j hjBound)
      exact hnonnegative
    rw [← hra, ← hfr] at hlo
    rw [← hrb, ← hfr] at hhi
    rw [← hfr] at hvNN
    have hloInt := Int.ofNat_le.mpr hlo
    have hhiInt := Int.ofNat_le.mpr hhi
    rw [Int.toNat_of_nonneg (nonneg hna), Int.toNat_of_nonneg hvNN] at hloInt
    rw [Int.toNat_of_nonneg hvNN, Int.toNat_of_nonneg (nonneg hnb)] at hhiInt
    exact ⟨a.2, b.2, na, nb, hna, hnb, hownA, hownB, hloInt, hhiInt⟩

end Elegant.Layered.PipelineImpl

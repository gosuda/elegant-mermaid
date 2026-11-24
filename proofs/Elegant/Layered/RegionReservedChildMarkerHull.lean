import Elegant.Layered.RegionReservedChildBudget

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem markerSet_length {α : Type} (xs : List α) (i : Nat) (a : α) :
    (setAt xs i a).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [setAt, ih]

private theorem markerSet_getD {α : Type} (xs : List α) (i j : Nat) (a d : α) :
    (setAt xs i a).getD j d = if j = i ∧ i < xs.length then a else xs.getD j d := by
  induction xs generalizing i j with
  | nil => simp [setAt]
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => simp [setAt]
      | succ j => simp [setAt]
    | succ i =>
      cases j with
      | zero => simp [setAt]
      | succ j => simpa [setAt, List.getD_cons_succ] using ih i j

private theorem markerFoldM_preserve {α β : Type} {step : α → β → Except LayoutError α}
    {I : α → Prop} {jobs : List β} {initial final : α}
    (hinitial : I initial)
    (hstep : ∀ a q b, q ∈ jobs → I a → step a q = .ok b → I b)
    (h : jobs.foldlM step initial = .ok final) : I final := by
  induction jobs generalizing initial with
  | nil => exact (Except.ok.inj h) ▸ hinitial
  | cons q qs ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hm, ht⟩ := bind_ok' h
    exact ih (hstep initial q mid List.mem_cons_self hinitial hm)
      (fun a j b hj ha hb => hstep a j b (List.mem_cons_of_mem _ hj) ha hb) ht

private theorem markerFold_lookup {α : Type} {jobs : List α}
    {step : List Int → α → List Int} {hit : α → Bool} {v : Nat} {value : Int}
    {initial : List Int}
    (hlen : ∀ x q, (step x q).length = x.length)
    (hstep : ∀ x q, q ∈ jobs → v < x.length →
      (step x q).getD v 0 = if hit q then value else x.getD v 0)
    (hv : v < initial.length) :
    (jobs.foldl step initial).getD v 0 = if jobs.any hit then value else initial.getD v 0 := by
  induction jobs generalizing initial with
  | nil => rfl
  | cons q qs ih =>
    rw [List.foldl_cons, ih (initial := step initial q)
      (fun x j hj => hstep x j (List.mem_cons_of_mem _ hj))
      (by rwa [hlen]), hstep initial q List.mem_cons_self hv]
    cases hq : hit q <;> cases ht : qs.any hit <;> simp [List.any_cons, hq, ht]

private def clusterEntry (inp : Input) (s : RegionSpec) (cg : Graph)
    (q : Node × Nat) : Option RegionCluster :=
  if q.1.border != -2 then none else
    let bottom := match cg.nodes.zipIdx.find? (fun b =>
        b.1.border == 2 && b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2
    let node := match cg.nodes.zipIdx.find? (fun b => b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2
    let titles := s.titles.getD q.1.decl (0, 0)
    some ({ id := boxId inp q.1.decl, decl := q.1.decl,
            node := node, top := q.2, bottom := bottom,
            titleW := q.1.w, titleH := titles.2, extent := q.1.loopExtent } : RegionCluster)

private theorem active_clusterRows {P : Params} {s : RegionSpec} {inp : Input}
    {candidate : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp candidate = .ok (some rm)) :
    rm.clusters = candidate.nodes.zipIdx.filterMap (clusterEntry inp s candidate) := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bind_ok' h
    split at h
    · cases h
    · change rm.clusters = RegionImpl.clusterRows inp s candidate
      exact (congrArg ComponentRegions.clusters (Option.some.inj (Except.ok.inj h))).symm

private theorem clusterEntry_top {inp : Input} {s : RegionSpec} {cg : Graph}
    {q : Node × Nat} {c : RegionCluster} (h : clusterEntry inp s cg q = some c) :
    q.1.border = -2 ∧ c.decl = q.1.decl ∧ c.top = q.2 := by
  unfold clusterEntry at h
  split at h
  · cases h
  · rename_i hb
    rw [← Option.some.inj h]
    exact ⟨by simpa using hb, rfl, rfl⟩

private theorem cluster_anchors_are_candidate_indices {inp : Input} {s : RegionSpec}
    {candidate : Graph} {c : RegionCluster}
    (hc : c ∈ candidate.nodes.zipIdx.filterMap (clusterEntry inp s candidate)) :
    (∃ n, candidate.nodes[c.top]? = some n) ∧
    (∃ n, candidate.nodes[c.bottom]? = some n) := by
  obtain ⟨q, hq, hentry⟩ := List.mem_filterMap.mp hc
  have htop : candidate.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  unfold clusterEntry at hentry
  split at hentry
  · cases hentry
  · rw [← Option.some.inj hentry]
    refine ⟨⟨q.1, htop⟩, ?_⟩
    change ∃ n : Node, candidate.nodes[(match candidate.nodes.zipIdx.find? (fun b =>
      b.1.border == 2 && b.1.decl == q.1.decl) with
      | some b => b.2
      | none => q.2)]? = some n
    split
    · rename_i b hb
      exact ⟨b.1, List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hb)⟩
    · exact ⟨q.1, htop⟩

private theorem cluster_decl_nodup {inp : Input} {s : RegionSpec} {candidate : Graph}
    (huniq : ∀ {i j : Nat} {a b : Node}, candidate.nodes[i]? = some a →
      candidate.nodes[j]? = some b → a.border = -2 → b.border = -2 →
      a.decl = b.decl → i = j) :
    ((candidate.nodes.zipIdx.filterMap (clusterEntry inp s candidate)).map (·.decl)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map, List.pairwise_filterMap,
    List.pairwise_iff_getElem]
  intro i j hi hj hij a ha b hb he
  obtain ⟨hab, had, _⟩ := clusterEntry_top ha
  obtain ⟨hbb, hbd, _⟩ := clusterEntry_top hb
  have hiNode := List.mem_zipIdx_iff_getElem?.mp
    (List.getElem_mem (l := candidate.nodes.zipIdx) (n := i) (h := hi))
  have hjNode := List.mem_zipIdx_iff_getElem?.mp
    (List.getElem_mem (l := candidate.nodes.zipIdx) (n := j) (h := hj))
  have hpos := huniq hiNode hjNode hab hbb (had.symm.trans (he.trans hbd))
  simp only [List.getElem_zipIdx, Nat.zero_add] at hpos
  omega

private theorem regionRun_admitted_candidate_keys {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel} (h0 : measuredGraph P inp o lines = .ok graph0)
    (hg : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {s : RegionSpec} {comp : List Nat} {index : Nat} (hc : comp ∈ components graph) :
    let candidate := componentCandidateR (some s) graph comp index
    (∀ {i : Nat} {n : Node}, candidate.nodes[i]? = some n →
      n.border ≠ -1 ∧ n.border ≠ 1) ∧
    (∀ {i j : Nat} {a b : Node}, candidate.nodes[i]? = some a → candidate.nodes[j]? = some b →
      a.border = -2 → b.border = -2 → a.decl = b.decl → i = j) := by
  dsimp only
  have hnodes : (componentCandidateR (some s) graph comp index).nodes =
      (componentCandidate graph comp index).nodes := (componentCandidate_nodes graph comp index).symm
  simp only [hnodes]
  refine ⟨?_, ?_⟩
  · intro i n hn
    rcases (X_componentCandidate_marker_shape h0 hg hn).1 with h | h | h <;> omega
  · intro i j a b ha hb hba hbb he
    obtain ⟨ia, hia, hga⟩ := componentCandidate_nonplain_source ha (by omega)
    obtain ⟨ib, hib, hgb⟩ := componentCandidate_nonplain_source hb (by omega)
    obtain ⟨_, ha0, hda, hba0, _⟩ := xdb_exactGraph_key hg hga
    obtain ⟨_, hb0, hdb, hbb0, _⟩ := xdb_exactGraph_key hg hgb
    have hdA := (measuredGraph_group_origin h0 ha0 (hba0.symm.trans hba)).1
    have hdB := (measuredGraph_group_origin h0 hb0 (hbb0.symm.trans hbb)).1
    exact nodup_map_inj_aux (fun x => x)
      (by simpa using components_nodup graph comp hc) hia hib (by omega)

private theorem markerTitled_no_sides {P : Params} {exact : List Nat} {s : RegionSpec}
    {g : Graph} {labeled : Proper} (hkeys : NodeKeys g labeled)
    (hsource : ∀ {i : Nat} {n : Node}, g.nodes[i]? = some n → n.border ≠ -1 ∧ n.border ≠ 1) :
    ∀ v ∈ (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled)).nodes,
      v.node.border ≠ -1 ∧ v.node.border ≠ 1 := by
  intro v hv
  unfold titleReservationsR at hv
  dsimp only at hv
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨sz, hsz, rfl⟩ := List.mem_map.mp hv
    have hb : sz.node.border ≠ -1 ∧ sz.node.border ≠ 1 := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hsz
      have h := sizeProperPortsX_key P exact labeled i
      rw [hi] at h
      cases hn : labeled.nodes[i]? with
      | none => simp [hn] at h
      | some n =>
        simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [h.2.1]
        rcases hkeys i n hn with ⟨before, hh, _, hb, _⟩ | ⟨_, hb, _⟩
        · rw [hb]
          exact hsource hh
        · rw [hb]
          decide
    split <;> exact hb
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
    change (3 : Int) ≠ -1 ∧ (3 : Int) ≠ 1
    decide

private theorem bordered_side_record {titled : Proper} {w : Int}
    {side : ProperNode} (hm : side ∈ (OrderImpl.addClusterBorders titled w).nodes)
    (hb : side.node.border = -1 ∨ side.node.border = 1) :
    side ∈ titled.nodes ∨ (side.dummy = false ∧ side.node.w = w) := by
  rw [OrderImpl.addClusterBorders_eq] at hm
  let inv (p : Proper) := ∀ n ∈ p.nodes, (n.node.border = -1 ∨ n.node.border = 1) →
    n ∈ titled.nodes ∨ (n.dummy = false ∧ n.node.w = w)
  have hall : inv ((titled.nodes.zipIdx.filter fun q => q.1.node.border == -2).foldl
      (OrderImpl.borderStep titled w) titled) := by
    apply OrderImpl.foldl_inv inv _ _ _ (fun _ h _ => Or.inl h)
    intro p hp q _
    unfold OrderImpl.borderStep
    split
    · exact hp
    · apply OrderImpl.foldl_inv inv _ _ _ hp
      intro p hp k _ n hn hnSide
      change n ∈ p.nodes ++ [OrderImpl.borderLeft q w, OrderImpl.borderRight q w] at hn
      rcases List.mem_append.mp hn with h | h
      · exact hp n h hnSide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> exact Or.inr ⟨rfl, rfl⟩
  exact hall side hm hb

private theorem activeCoordinate_side_width_and_index {P : Params} {exact : List Nat}
    {s : RegionSpec} {labeled : Proper} {i : Nat} {side : ProperNode}
    (hsource : ∀ v ∈ (titleReservationsR s.titles P.clusterPad
      (sizeProperPortsX P exact labeled)).nodes, v.node.border ≠ -1 ∧ v.node.border ≠ 1)
    (hside : (coordinateGraphR P exact (some s) labeled).nodes[i]? = some side)
    (hb : side.node.border = -1 ∨ side.node.border = 1) :
    side.node.w = P.clusterBorderW ∧ labeled.nodes.length ≤ i := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  change (materializeDummyPaths (clearProxyExtents bordered)).nodes[i]? = some side at hside
  obtain ⟨before, hbefore, _, hborder, _, heq⟩ := materialize_lookup _ hside
  rw [clearProxyExtents_nodes, List.getElem?_map] at hbefore
  obtain ⟨marker, hmarker, hclear⟩ := Option.map_eq_some_iff.mp hbefore
  have hb' : marker.node.border = -1 ∨ marker.node.border = 1 := by
    rw [← (clearF_keys marker).2.1, hclear, ← hborder]
    exact hb
  have hnot : marker ∉ titled.nodes := by
    intro hm
    obtain ⟨hl, hr⟩ := hsource marker hm
    exact hb'.elim hl hr
  obtain ⟨hd, hw⟩ := (bordered_side_record (List.mem_of_getElem? hmarker) hb').resolve_left hnot
  have hclearId : clearF marker = marker := by
    have hh : (marker.node.border == -2 || marker.node.border == 2) = false := by
      rcases hb' with h | h <;> simp [h]
    simp only [clearF, hh, Bool.false_eq_true, ite_false]
  have hdummy : before.dummy = false := by rw [← hclear, hclearId]; exact hd
  have hsideId : side = marker := (heq hdummy).trans (hclear.symm.trans hclearId)
  refine ⟨by rwa [hsideId], ?_⟩
  obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  have ht : titled.nodes.length ≤ i := by
    apply Classical.byContradiction
    intro h
    rw [show bordered.nodes = titled.nodes ++ extra from hnodes,
      List.getElem?_append_left (by omega)] at hmarker
    exact hnot (List.mem_of_getElem? hmarker)
  have hz : sized.nodes.length = labeled.nodes.length := by simp [sized, sizeProperPortsX]
  have htlen : sized.nodes.length ≤ titled.nodes.length := by
    simp [titled, titleReservationsR]
  omega

private theorem regionFrame_marker_set {pl : RegionPlacement} {P : Params}
    {a : RegionAllocation} {xs : List Int} {child i : Nat}
    {c : RegionCluster} {n : ProperNode} (hc : pl.rm.clusters[child]? = some c)
    (hu : (pl.rm.clusters.map (·.decl)).Nodup)
    (hn : pl.p.nodes[i]? = some n) (hi : i < xs.length)
    (hb : n.node.border = -1 ∨ n.node.border = 1 ∨ n.node.border = 3)
    (hp : n.node.clusterPath.getLast? = some c.decl)
    (ha : ∀ d ∈ pl.rm.clusters, d.top ≠ i ∧ d.bottom ≠ i) :
    let left := a.lefts.getD child 0
    let right := left + a.widths.getD child 0 - pl.buckets.loopWidth.getD child 0
    (regionFrames pl P a xs).getD i 0 = match n.node.border with
      | -1 => left + Int.tdiv P.clusterBorderW 2
      | 1 => right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2
      | _ => left + Int.tdiv (right - left) 2 := by
  let nodeStep (d : RegionCluster × Nat) (x : List Int) (q : ProperNode × Nat) : List Int :=
    let left := a.lefts.getD d.2 0
    let right := left + a.widths.getD d.2 0 - pl.buckets.loopWidth.getD d.2 0
    if q.1.node.clusterPath.getLast? != some d.1.decl then x else
      match q.1.node.border with
      | -1 => setAt x q.2 (left + Int.tdiv P.clusterBorderW 2)
      | 1 => setAt x q.2 (right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2)
      | 3 => setAt x q.2 (left + Int.tdiv (right - left) 2)
      | _ => x
  let step (x : List Int) (d : RegionCluster × Nat) : List Int :=
    let left := a.lefts.getD d.2 0
    let right := left + a.widths.getD d.2 0 - pl.buckets.loopWidth.getD d.2 0
    let center := left + Int.tdiv (right - left) 2
    setAt (setAt (pl.p.nodes.zipIdx.foldl (nodeStep d) x) d.1.top center) d.1.bottom center
  let centerOf (k : Nat) : Int :=
    let left := a.lefts.getD k 0
    let right := left + a.widths.getD k 0 - pl.buckets.loopWidth.getD k 0
    match n.node.border with
    | -1 => left + Int.tdiv P.clusterBorderW 2
    | 1 => right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2
    | _ => left + Int.tdiv (right - left) 2
  have hlen (d : RegionCluster × Nat) (x : List Int) (q : ProperNode × Nat) :
      (nodeStep d x q).length = x.length := by
    unfold nodeStep
    dsimp only
    split
    · rfl
    · split <;> simp only [markerSet_length]
  have houterLen (x : List Int) (d : RegionCluster × Nat) : (step x d).length = x.length := by
    simp only [step, markerSet_length]
    exact OrderImpl.foldl_inv (fun y : List Int => y.length = x.length) _ _ _ rfl
      (fun y hy q _ => (hlen d y q).trans hy)
  have houter (x : List Int) (d : RegionCluster × Nat) (hd : d ∈ pl.rm.clusters.zipIdx)
      (hx : i < x.length) : (step x d).getD i 0 =
        if (d.2 == child) then centerOf child else x.getD i 0 := by
    have hlookup : pl.rm.clusters[d.2]? = some d.1 := List.mem_zipIdx_iff_getElem?.mp hd
    obtain ⟨ht, hbot⟩ := ha d.1 (List.mem_of_getElem? hlookup)
    simp only [step]
    rw [markerSet_getD, ite_eq_right (fun h => hbot h.1.symm),
      markerSet_getD, ite_eq_right (fun h => ht h.1.symm)]
    have hkeys : d.1.decl = c.decl ↔ d.2 = child := by
      constructor
      · intro h
        exact nodup_map_inj_aux (·.decl) hu hlookup hc h
      · intro h
        rw [h, hc] at hlookup
        rw [Option.some.inj hlookup]
    let hit (q : ProperNode × Nat) := (q.2 == i) && (d.2 == child)
    have hinner (y : List Int) (q : ProperNode × Nat) (hq : q ∈ pl.p.nodes.zipIdx)
        (hy : i < y.length) : (nodeStep d y q).getD i 0 =
          if hit q then centerOf child else y.getD i 0 := by
      by_cases hqIdx : q.2 = i
      · have hqNode : pl.p.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
        rw [hqIdx, hn] at hqNode
        have hqRec := Option.some.inj hqNode
        by_cases hdIdx : d.2 = child
        · have hdDecl := hkeys.mpr hdIdx
          have hguard : ¬ ((q.1.node.clusterPath.getLast? != some d.1.decl) = true) := by
            intro hne
            apply bne_iff_ne.mp hne
            rw [← hqRec, hp, hdDecl]
          have hhit : hit q = true := by simp [hit, hqIdx, hdIdx]
          have hwrite (z : Int) : (setAt y q.2 z).getD i 0 = z := by
            rw [markerSet_getD, ite_eq_left ⟨hqIdx.symm, by omega⟩]
          rw [ite_eq_left hhit]
          unfold nodeStep centerOf
          dsimp only
          rw [ite_eq_right hguard, ← hqRec, hdIdx]
          rcases hb with hl | hr | ht
          · rw [hl]
            exact hwrite _
          · rw [hr]
            exact hwrite _
          · rw [ht]
            exact hwrite _
        · have hguard : (q.1.node.clusterPath.getLast? != some d.1.decl) = true := by
            apply bne_iff_ne.mpr
            intro he
            rw [← hqRec, hp] at he
            exact hdIdx (hkeys.mp (Option.some.inj he).symm)
          have hhit : ¬ (hit q = true) := by simp [hit, hdIdx]
          unfold nodeStep
          dsimp only
          rw [ite_eq_left hguard, ite_eq_right hhit]
      · have hs (z : Int) : (setAt y q.2 z).getD i 0 = y.getD i 0 := by
          rw [markerSet_getD, ite_eq_right (fun h => hqIdx h.1.symm)]
        simp only [hit, beq_eq_false_iff_ne.mpr hqIdx, Bool.false_and, Bool.false_eq_true,
          ite_false, nodeStep]
        split
        · rfl
        · split <;> first | rfl | exact hs _
    rw [markerFold_lookup (hlen d) hinner hx]
    have hany : pl.p.nodes.zipIdx.any hit = (d.2 == child) := by
      by_cases hdIdx : d.2 = child
      · rw [beq_iff_eq.mpr hdIdx]
        exact List.any_eq_true.mpr ⟨(n, i), List.mem_zipIdx_iff_getElem?.mpr hn, by simp [hit, hdIdx]⟩
      · rw [beq_eq_false_iff_ne.mpr hdIdx]
        apply List.any_eq_false.mpr
        intro q _
        simp [hit, hdIdx]
    rw [hany]
  change (pl.rm.clusters.zipIdx.foldl step xs).getD i 0 = centerOf child
  rw [markerFold_lookup houterLen houter hi]
  have hany : pl.rm.clusters.zipIdx.any (fun d => d.2 == child) = true :=
    List.any_eq_true.mpr ⟨(c, child), List.mem_zipIdx_iff_getElem?.mpr hc, by simp⟩
  simp only [hany, ite_true]

private theorem clusterPort_marker_other {pl : RegionPlacement} {g k i : Nat}
    {xs ys : List Int} (h : clusterPortR pl g k xs = .ok ys) (hk : k ≠ i) :
    ys.getD i 0 = xs.getD i 0 := by
  unfold clusterPortR at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · rw [← Except.ok.inj h, markerSet_getD, ite_eq_right (fun he => hk he.1.symm)]
  · cases h

private theorem reservedPorts_marker_lookup {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper}
    (h : reservedPortsR pl cg labels xs = .ok (ys, placed)) :
    placed.nodes.length = pl.p.nodes.length ∧
    ∀ {i : Nat} {n : ProperNode}, pl.p.nodes[i]? = some n →
      ∃ m, placed.nodes[i]? = some m ∧ m.node.border = n.node.border ∧
        m.node.clusterPath = n.node.clusterPath ∧
        ((∀ c ∈ pl.rm.clusters, c.top ≠ i ∧ c.bottom ≠ i) →
          m = n ∧ ys.getD i 0 = xs.getD i 0) := by
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
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = _ at h
  obtain ⟨out, hfold, hresult⟩ := bind_ok' h
  have hp : placed.nodes = out.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hresult)).symm
  have hy : ys = out.1 := (congrArg Prod.fst (Except.ok.inj hresult)).symm
  rw [hp, hy]
  refine ⟨?_, ?_⟩
  · rw [Array.length_toList, ← List.size_toArray]
    refine markerFoldM_preserve (I := fun acc => acc.2.size = pl.p.nodes.toArray.size)
      rfl ?_ hfold
    intro a q b _ ha hab
    dsimp only [step] at hab
    split at hab
    · cases hab
    · obtain ⟨_, _, hab⟩ := bind_ok' hab
      obtain ⟨_, _, hab⟩ := bind_ok' hab
      rw [← Except.ok.inj hab]
      simpa only [size_set!_eq] using ha
  · intro i n hn
    have keep (jobs : List (RegionCluster × Nat)) (start finish : List Int × Array ProperNode)
        (src : ProperNode) (hsrc : start.2[i]? = some src)
        (hjobs : jobs.foldlM step start = .ok finish) :
        ∃ dst, finish.2[i]? = some dst ∧ dst.node.border = src.node.border ∧
          dst.node.clusterPath = src.node.clusterPath ∧
          ((∀ q ∈ jobs, q.1.top ≠ i ∧ q.1.bottom ≠ i) →
            dst = src ∧ finish.1.getD i 0 = start.1.getD i 0) := by
      induction jobs generalizing start src with
      | nil =>
        rw [← Except.ok.inj hjobs]
        exact ⟨src, hsrc, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
      | cons q qs ih =>
        rw [List.foldlM_cons] at hjobs
        obtain ⟨mid, hm, ht⟩ := bind_ok' hjobs
        dsimp only [step] at hm
        split at hm
        · cases hm
        · obtain ⟨x, hx, hm⟩ := bind_ok' hm
          obtain ⟨y, hy, hm⟩ := bind_ok' hm
          have hrec : ∃ m, mid.2[i]? = some m ∧ m.node.border = src.node.border ∧
              m.node.clusterPath = src.node.clusterPath := by
            rw [← Except.ok.inj hm]
            dsimp only
            rw [Array.set!_eq_setIfInBounds]
            by_cases htop : q.1.top = i
            · have hi := (Array.getElem?_eq_some_iff.mp hsrc).1
              have hget : start.2.getD i default = src := by
                simp only [Array.getD_eq_getD_getElem?, hsrc, Option.getD_some]
              rw [htop, Array.getElem?_setIfInBounds_self_of_lt hi, hget]
              exact ⟨_, rfl, rfl, rfl⟩
            · rw [Array.getElem?_setIfInBounds_ne htop]
              exact ⟨src, hsrc, rfl, rfl⟩
          obtain ⟨m, hmid, hb, hp⟩ := hrec
          obtain ⟨dst, hd, hborder, hpath, hkeep⟩ := ih mid m hmid ht
          refine ⟨dst, hd, hborder.trans hb, hpath.trans hp, ?_⟩
          intro ha
          obtain ⟨hTop, hBottom⟩ := ha q List.mem_cons_self
          obtain ⟨he, hxs⟩ := hkeep (fun r hr => ha r (List.mem_cons_of_mem _ hr))
          have hcurrent : mid.2[i]? = some src := by
            rw [← Except.ok.inj hm]
            dsimp only
            rwa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hTop]
          have hmidX : mid.1 = y := (congrArg Prod.fst (Except.ok.inj hm)).symm
          rw [hmidX] at hxs
          exact ⟨he.trans (Option.some.inj (hmid.symm.trans hcurrent)),
            hxs.trans ((clusterPort_marker_other hy hBottom).trans (clusterPort_marker_other hx hTop))⟩
    obtain ⟨m, hm, hb, hp, hs⟩ := keep _ _ _ n (by rwa [List.getElem?_toArray]) hfold
    exact ⟨m, by simpa only [Array.getElem?_toList] using hm, hb, hp,
      fun ha => hs (fun q hq => ha q.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq)))⟩

private theorem allocate_marker_left_nonneg {pl : RegionPlacement} {P : Params}
    {before shifted : List Int} {a : RegionAllocation}
    (h : allocatePl pl P before = .ok (a, shifted))
    (horig : ∀ g, 0 ≤ pl.minimum.origins.getD g 0)
    (hown : ∀ g, 0 ≤ pl.buckets.widths.getD g 0)
    (hwidth : ∀ g, 0 ≤ (reserveWidths pl P).getD g 0) :
    a.widths = reserveWidths pl P ∧ ∀ g, 0 ≤ a.lefts.getD g 0 := by
  unfold allocatePl at h
  obtain ⟨out, hfold, hreturn⟩ := bind_ok' h
  have ha : a = ⟨reserveWidths pl P, out.2.1, out.2.2⟩ :=
    (congrArg (fun result : RegionAllocation × List Int => result.1) (Except.ok.inj hreturn)).symm
  subst a
  refine ⟨rfl, ?_⟩
  change ∀ g, 0 ≤ out.2.1.getD g 0
  refine markerFoldM_preserve (I := fun acc => ∀ g, 0 ≤ acc.2.1.getD g 0) ?_ ?_ hfold
  · intro g
    change 0 ≤ (List.replicate (pl.rm.clusters.length + 1) (0 : Int)).getD g 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> decide
  · intro acc job out _ ha hout
    rcases acc with ⟨xs, lefts, lanes⟩
    unfold allocateGroup at hout
    dsimp only at hout
    obtain ⟨placed, hp, hout⟩ := bind_ok' hout
    obtain ⟨_, _, hout⟩ := bind_ok' hout
    rw [← Except.ok.inj hout]
    change ∀ g, 0 ≤ placed.2.getD g 0
    have hstart : 0 ≤ lefts.getD job 0 +
        (if job != pl.rm.clusters.length then pl.minimum.origins.getD job 0 else 0) +
        pl.buckets.widths.getD job 0 := by
      change ∀ g, 0 ≤ lefts.getD g 0 at ha
      have hbase := ha job
      have ho := horig job
      have hw := hown job
      split <;> omega
    exact (markerFoldM_preserve (I := fun st => 0 ≤ st.1 ∧ ∀ g, 0 ≤ st.2.getD g 0)
      ⟨hstart, ha⟩ (by
        intro st c next _ hs hnext
        rw [← Except.ok.inj hnext]
        refine ⟨Int.add_nonneg hs.1 (hwidth c), ?_⟩
        intro g
        change 0 ≤ (setAt st.2 c st.1).getD g 0
        rw [markerSet_getD]
        split
        · exact hs.1
        · exact hs.2 g) hp).2

/-- The actual allocation supplies the final side-marker centers. The right border
stops before the group's loop allowance, not at the end of that allowance. -/
theorem RegionCrossAllocationStages.activeChild_side_centers
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
    {child : Nat} {c : RegionCluster} (hchild : rm.clusters[child]? = some c)
    {i : Nat} {side : ProperNode} (hside : run.proper.nodes[i]? = some side)
    (hkind : side.node.border = -1 ∨ side.node.border = 1)
    (hpath : side.node.clusterPath.getLast? = some c.decl) :
    let left := stages.allocation.lefts.getD child 0
    let right := left + (reserveWidths stages.placement P).getD child 0 -
      stages.placement.buckets.loopWidth.getD child 0
    side.node.w = P.clusterBorderW ∧
      run.xs.getD i 0 = if side.node.border = -1 then left + Int.tdiv P.clusterBorderW 2
        else right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2 := by
  have hnodes := rankEquivalentR_nodes_eq hrank
  have hclusters := active_clusterRows hactive
  obtain ⟨hsource, huniq⟩ := regionRun_admitted_candidate_keys
    (s := s) (index := candidate) hgraph0 hgraph hcomp
  have hnoSide : ∀ {i : Nat} {n : Node}, cg.nodes[i]? = some n → n.border ≠ -1 ∧ n.border ≠ 1 := by
    intro i n hn
    exact hsource (by rwa [← hnodes])
  have htitled := markerTitled_no_sides (P := P) (exact := exact) (s := s)
    (addLabelNodes_keys _ _ _ (normalize_keys hnorm) hlabels) hnoSide
  have hpl := stages.hPlacement
  have hpp : stages.placement.p = p := by rw [hpl]
  have hpr : stages.placement.rm = rm := by rw [hpl]
  obtain ⟨hplacedLen, hports⟩ := reservedPorts_marker_lookup stages.hFramesAndPorts
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, proxied, _, _, actual⟩ := componentRunR_stages hrun
  have hproxy : proxyWidths run.coordinateProper run.coordinateXs = .ok (proxied, run.xs) := by
    rw [actual.hCoordProper]
    exact actual.hProxy
  obtain ⟨_, _, hproxyLen, _, hmetadata, hnonproxy⟩ := proxyWidths_rel hproxy
  rw [← actual.hDrop, OrderImpl.dropSynthetic_nodes] at hside
  have hiFinal := (List.getElem?_eq_some_iff.mp hside).1
  have hiP : i < p.nodes.length := by rw [hproxyLen, hplacedLen, hpp] at hiFinal; exact hiFinal
  let n := p.nodes[i]
  have hn : p.nodes[i]? = some n := List.getElem?_eq_getElem hiP
  have hnP : stages.placement.p.nodes[i]? = some n := by rwa [hpp]
  obtain ⟨m, hm, hbPort, _, hrestore⟩ := hports hnP
  obtain ⟨q, hq, _, hbProxy, _⟩ := hmetadata i m hm
  have hqSide : q = side := Option.some.inj (hq.symm.trans hside)
  subst q
  have hb : n.node.border = -1 ∨ n.node.border = 1 := by
    simpa only [← hbPort, ← hbProxy] using hkind
  have hnC : (coordinateGraphR P exact (some s) labeled).nodes[i]? = some n := by
    rwa [hcoord]
  obtain ⟨hwidth, hiSide⟩ := activeCoordinate_side_width_and_index htitled hnC hb
  have haway : ∀ d ∈ stages.placement.rm.clusters, d.top ≠ i ∧ d.bottom ≠ i := by
    rw [hpr, hclusters]
    intro d hd
    obtain ⟨ht, hb⟩ := cluster_anchors_are_candidate_indices hd
    have away {k : Nat} (hk : ∃ b, (componentCandidateR (some s) graph comp candidate).nodes[k]? = some b) :
        k ≠ i := by
      obtain ⟨b, hnb⟩ := hk
      rw [← hnodes] at hnb
      have hlabel := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hnb) rfl
      have hlt := (List.getElem?_eq_some_iff.mp hlabel).1
      omega
    exact ⟨away ht, away hb⟩
  obtain ⟨hmn, hxPort⟩ := hrestore haway
  have hm' : run.coordinateProper.nodes[i]? = some n := by rwa [hmn] at hm
  have hnp : ¬ (n.node.border = -2 ∨ n.node.border = 2) := by rcases hb with h | h <;> omega
  obtain ⟨hwrite, hx⟩ := hnonproxy i n hm' hnp
  have heq : n = side := Option.some.inj (hwrite.symm.trans hside)
  subst side
  obtain ⟨_, _, _, hlen, _⟩ := allocatePl_translation_trace stages.hAllocation
  have hbound : i < stages.shifted.length := by
    rw [hlen, CoordsImpl.crossCoordsClusterWith_length stages.hCross]
    exact hiP
  have hchild' : stages.placement.rm.clusters[child]? = some c := by rwa [hpr]
  have huniq' : (stages.placement.rm.clusters.map (·.decl)).Nodup := by
    rw [hpr, hclusters]
    exact cluster_decl_nodup huniq
  have hwidths : stages.allocation.widths = reserveWidths stages.placement P := by
    have ha := stages.hAllocation
    unfold allocatePl at ha
    obtain ⟨_, _, hret⟩ := bind_ok' ha
    exact (congrArg (fun q : RegionAllocation × List Int => q.1.widths) (Except.ok.inj hret)).symm
  refine ⟨hwidth, ?_⟩
  rw [List.getD_eq_getElem?_getD, hx, Option.getD_some, hxPort]
  have h := regionFrame_marker_set (P := P) (a := stages.allocation) hchild' huniq' hnP hbound
    (hb.elim Or.inl (fun h => Or.inr (Or.inl h))) hpath haway
  rcases hb with hleft | hright
  · simpa [hwidths, hleft] using h
  · simpa [hwidths, hright] using h

private theorem activeCoordinate_title_copy {P : Params} {exact : List Nat}
    {s : RegionSpec} {cg : Graph} {normalized labeled : Proper} {ranks : List Int}
    {labels : List MeasuredLabel}
    (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    (hshape : ∀ {i : Nat} {n : Node}, cg.nodes[i]? = some n → n.border ≠ 3)
    {i : Nat} {n : ProperNode}
    (hn : (coordinateGraphR P exact (some s) labeled).nodes[i]? = some n)
    (hb : n.node.border = 3) :
    labeled.nodes.length ≤ i ∧
      ∃ (j : Nat) (old : Node), cg.nodes[j]? = some old ∧ old.border = -2 ∧
        n.node.clusterPath = old.clusterPath ∧ n.node.w = old.w := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  let copy (q : ProperNode × Nat) : ProperNode :=
    let top := q.1
    let title : Node := { top.node with
      border := 3
      loopExtent := 0
      h := (s.titles.getD top.node.decl (0, 0)).2 + P.clusterPad }
    { top with node := title }
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
    have hclear' : before = copy q := by
      simpa [clearF, copy] using hclear.symm
    have hcopyReal : (copy q).dummy = false := congrArg ProperNode.dummy hqEq
    have hnEq : n = copy q :=
      (hreal ((congrArg ProperNode.dummy hclear').trans hcopyReal)).trans hclear'
    refine ⟨by simpa only [hsizedLen] using hi, q.2, old, hold, htopOld, ?_, ?_⟩
    · rw [hnEq, show (copy q).node.clusterPath = q.1.node.clusterPath from rfl, hqEq]
    · rw [hnEq, show (copy q).node.w = q.1.node.w from rfl, hqEq]
  · omega

private theorem activeCoordinate_anchor_keys {P : Params} {exact : List Nat}
    {s : RegionSpec} {labeled : Proper} {i : Nat} {n : ProperNode}
    (hn : labeled.nodes[i]? = some n) (hreal : n.dummy = false) :
    ∃ m, (coordinateGraphR P exact (some s) labeled).nodes[i]? = some m ∧
      m.node.border = n.node.border ∧ m.node.clusterPath = n.node.clusterPath := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  have hk := sizeProperPortsX_key P exact labeled i
  change (sized.nodes[i]?).map _ = _ at hk
  cases hs : sized.nodes[i]? with
  | none => simp [hs, hn] at hk
  | some sz =>
    simp only [hs, hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
    have ht : titled.nodes[i]? = some (titleF sz) := by
      unfold titled titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by
        simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hs).1)]
      simp only [List.getElem?_map, hs, Option.map_some] <;> rfl
    obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    have hget : (clearProxyExtents bordered).nodes[i]? = some (clearF (titleF sz)) := by
      rw [clearProxyExtents_nodes, List.getElem?_map, show bordered.nodes = _ ++ extra from hnodes,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1, ht] <;> rfl
    obtain ⟨nd, hnd, _⟩ := materialize_exists _ hget
    obtain ⟨orig, ho, _, _, _, he⟩ := materialize_lookup _ hnd
    have heq : orig = clearF (titleF sz) := Option.some.inj (ho.symm.trans hget)
    subst orig
    have hnd' : nd = clearF (titleF sz) := he (by
      rw [(clearF_keys _).1, (titleF_keys _).1, hk.1, hreal])
    refine ⟨nd, hnd, ?_, ?_⟩
    · rw [hnd', (clearF_keys _).2.1, (titleF_keys _).2.1, hk.2.1]
    · rw [hnd', (clearF_keys _).2.2.1, (titleF_keys _).2.2.1, hk.2.2]

private theorem activeFrame_borders_nonempty {P : Params} {exact : List Nat} {s : RegionSpec}
    {inp : Input} {candidate cg : Graph} {labels : List MeasuredLabel} {run : Run}
    {orderOptions : OrderOptions} {rm : ComponentRegions} {ranks : List Int}
    {normalized labeled p : Proper} {minimum : RegionConstraints} {layers : List (List Nat)}
    {reserved : List (Option Int)}
    (hrun : componentRunR P exact (some s) inp candidate labels orderOptions = .ok (cg, run))
    (hnorm : normalize cg ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled)
    (hcoord : coordinateGraphR P exact (some s) labeled = p)
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    {pos : Nat} {frame : Node} (hnode : cg.nodes[pos]? = some frame) (hgroup : frame.border = -2)
    (hframePath : frame.clusterPath.getLast? = some frame.decl) :
    groupBorderRects cg run frame.decl ≠ [] := by
  have hl := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hnode) rfl
  obtain ⟨n, hn, hb, hp⟩ := activeCoordinate_anchor_keys (P := P)
    (exact := exact) (s := s) hl rfl
  rw [hcoord] at hn
  have hpp : stages.placement.p = p := by rw [stages.hPlacement]
  have hget : stages.placement.p.nodes[pos]? = some n := by rwa [hpp]
  obtain ⟨_, hports⟩ := reservedPorts_marker_lookup stages.hFramesAndPorts
  obtain ⟨proxy, hproxy, hproxyBorder, hproxyPath, _⟩ := hports hget
  have hgb : proxy.node.border = -2 := hproxyBorder.trans (hb.trans hgroup)
  have hpath : proxy.node.clusterPath.getLast? = some frame.decl := by
    rw [hproxyPath, hp]
    exact hframePath
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, proxied, _, _, actual⟩ := componentRunR_stages hrun
  have hw : proxyWidths run.coordinateProper run.coordinateXs = .ok (proxied, run.xs) := by
    rw [actual.hCoordProper]
    exact actual.hProxy
  obtain ⟨owner, _, howner, hs⟩ := proxyWidths_proxy_span_source hw hproxy (Or.inl hgb)
  obtain ⟨i, side, hi, hkind, hsidePath, _⟩ := proxySpan_side_source hs
  have hbSide : ¬ (side.node.border = -2 ∨ side.node.border = 2) :=
    by rcases hkind with h | h <;> omega
  have hfinal := ((proxyWidths_rel hw).2.2.2.2.2 i side hi hbSide).1
  have hfinal' : run.proper.nodes[i]? = some side := by
    rwa [← actual.hDrop, OrderImpl.dropSynthetic_nodes]
  have hsame : owner = frame.decl := Option.some.inj (howner.symm.trans hpath)
  have hm := groupBorderRects_mem_of_record (cg := cg) hfinal' hkind
    (hsidePath.trans (congrArg some hsame))
  intro he
  exact List.not_mem_nil (he ▸ hm)

/-- The selected child's emitted group frame lies in the horizontal reservation.
No assertion about neighboring lanes or frame clearance is a premise. -/
theorem RegionCrossAllocationStages.activeChild_frame_within_reservation
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
    (hmin : constrainR rm P p = .ok minimum)
    {child pos : Nat} {c : RegionCluster} {frame : Node}
    (hchild : rm.clusters[child]? = some c) (hnode : cg.nodes[pos]? = some frame)
    (hgroup : frame.border = -2) (hdecl : frame.decl = c.decl) :
    stages.allocation.lefts.getD child 0 ≤ (frameRect P cg run pos).x ∧
      (frameRect P cg run pos).x + (frameRect P cg run pos).w ≤
        stages.allocation.lefts.getD child 0 + (reserveWidths stages.placement P).getD child 0 := by
  have hpad := (checkedParams_sizing_nonneg hparams).2.1
  have hb := checkedParams_clusterBorderW_ge_one hparams
  have hinset : 0 ≤ regionInsetOf P := by unfold regionInsetOf; omega
  have hslot : 0 ≤ P.slot := by have := componentRunR_slot_pos hrun; omega
  obtain ⟨hown, hlane, hloop⟩ := stages.bucket_signs hslot
  have hwidth := reserveWidths_nonnegative hinset hown hlane hloop
  have horig (g : Nat) : 0 ≤ stages.placement.minimum.origins.getD g 0 := by
    rw [stages.hPlacement]
    change 0 ≤ minimum.origins.getD g 0
    rw [constrainR_origins hmin, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split
    · exact hinset
    · exact Int.le_refl 0
  obtain ⟨_, hleft⟩ := allocate_marker_left_nonneg stages.hAllocation horig hown hwidth
  have hchildBound := (List.getElem?_eq_some_iff.mp hchild).1
  obtain ⟨pre, post, hsplit, hlast, hchildren⟩ :=
    (stages.reservation_order (activeRegion_parent_count hactive) hmin).2 child (Nat.le_of_lt hchildBound)
  have hreal : child < stages.placement.rm.clusters.length := by
    simpa only [stages.hPlacement] using hchildBound
  have hchildRoom := reserveWidths_room_from_last_writes
    (pl := stages.placement) (P := P) hsplit hreal hlast hchildren
  dsimp only at hchildRoom
  have hsum : 0 ≤ ((stages.placement.children.getD child []).map fun k =>
      (reserveWidths stages.placement P).getD k 0).sum := by
    generalize stages.placement.children.getD child [] = row
    induction row with
    | nil => exact Int.le_refl 0
    | cons k ks ih => rw [List.map_cons, List.sum_cons]; exact Int.add_nonneg (hwidth k) ih
  let left := stages.allocation.lefts.getD child 0
  let right := left + (reserveWidths stages.placement P).getD child 0 -
    stages.placement.buckets.loopWidth.getD child 0
  have hroom : left + P.clusterBorderW ≤ right := by
    have hInset : P.clusterBorderW ≤ 2 * regionInsetOf P := by unfold regionInsetOf; omega
    have := hown child
    have := hlane child
    dsimp only [right]
    omega
  have hleft0 : 0 ≤ left := hleft child
  have hright : 0 ≤ right := by omega
  have hcenters {i : Nat} {side : ProperNode} (hi : run.proper.nodes[i]? = some side)
      (hk : side.node.border = -1 ∨ side.node.border = 1)
      (hp : side.node.clusterPath.getLast? = some frame.decl) :
      side.node.w = P.clusterBorderW ∧
        run.xs.getD i 0 = if side.node.border = -1 then left + Int.tdiv P.clusterBorderW 2
          else right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2 :=
    stages.activeChild_side_centers hgraph0 hgraph hcomp hrun hactive
      hrank hnorm hlabels hcoord hchild hi hk (hp.trans (congrArg some hdecl))
  have hframe := activeFrame_right_of_side_centers (P := P) (run := run)
    (left := left) (right := right) hnode hgroup
    (by omega) hright hroom
    (fun hi hk hp => hcenters hi hk hp)
  refine ⟨?_, ?_⟩
  · have hsource : (componentCandidate graph comp candidate).nodes[pos]? = some frame := by
      rw [componentCandidate_nodes]
      have hn := hnode
      rw [rankEquivalentR_nodes_eq hrank] at hn
      exact hn
    obtain ⟨_, _, horiginal⟩ := componentCandidate_nonplain_source hsource (by omega)
    obtain ⟨n0, hn0, hd0, hb0, hp0⟩ := xdb_exactGraph_key hgraph horiginal
    obtain ⟨_, _, _, _, hp⟩ := measuredGraph_group_origin hgraph0 hn0 (hb0.symm.trans hgroup)
    have hframePath : frame.clusterPath.getLast? = some frame.decl := by
      rw [hp0, hp, hd0]
      simp
    have hne := activeFrame_borders_nonempty hrun hnorm hlabels hcoord stages hnode hgroup hframePath
    have hfloor : Int.tdiv P.clusterBorderW 2 = Int.fdiv P.clusterBorderW 2 := by
      have hb0 : 0 ≤ P.clusterBorderW := by omega
      rw [Int.tdiv_eq_ediv_of_nonneg hb0, Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    rw [frameRect_group_span hnode hgroup]
    dsimp only
    apply boundsOf_minX_ge_of_all hne
    intro rect hrect
    obtain ⟨i, side, hi, hk, hpSide, rfl⟩ := groupBorderRects_inv hrect
    obtain ⟨hw, hx⟩ := hcenters hi hk hpSide
    change left ≤ run.xs.getD i 0 - Int.fdiv (RouteImpl.nodeW run.proper i) 2
    simp only [RouteImpl.nodeW, hi, hw]
    rw [hx, hfloor]
    rcases hk with hl | hr
    · rw [hl, ite_eq_left rfl]
      omega
    · rw [hr, ite_eq_right (by decide : (1 : Int) ≠ -1)]
      omega
  · have := hloop child
    dsimp only [right, left] at hframe
    omega

theorem activeChild_frame_record {P : Params} {s : RegionSpec} {inp : Input}
    {candidate cg : Graph} {rm : ComponentRegions} {ranks : List Int} {budget : Bool}
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hrank : rankEquivalentR rm candidate = .ok (ranks, cg, budget))
    {child : Nat} {c : RegionCluster} (hc : rm.clusters[child]? = some c) :
    ∃ frame : Node, cg.nodes[c.top]? = some frame ∧ frame.border = -2 ∧ frame.decl = c.decl := by
  have hm := List.mem_of_getElem? hc
  rw [active_clusterRows hactive] at hm
  obtain ⟨q, hq, hentry⟩ := List.mem_filterMap.mp hm
  obtain ⟨hb, hd, ht⟩ := clusterEntry_top hentry
  refine ⟨q.1, ?_, hb, hd.symm⟩
  rw [ht, rankEquivalentR_nodes_eq hrank]
  exact List.mem_zipIdx_iff_getElem?.mp hq

theorem RegionCrossAllocationStages.activeChild_title_center
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
    {child : Nat} {c : RegionCluster} (hchild : rm.clusters[child]? = some c)
    {i : Nat} {title : ProperNode} (htitle : run.proper.nodes[i]? = some title)
    (hkind : title.node.border = 3) (hpath : title.node.clusterPath.getLast? = some c.decl) :
    title.node.w = c.titleW ∧
      run.xs.getD i 0 = stages.allocation.lefts.getD child 0 +
        Int.tdiv (stages.allocation.widths.getD child 0 -
          stages.placement.buckets.loopWidth.getD child 0) 2 := by
  have hnodes := rankEquivalentR_nodes_eq hrank
  have hclusters := active_clusterRows hactive
  obtain ⟨_, huniq⟩ := regionRun_admitted_candidate_keys
    (s := s) (index := candidate) hgraph0 hgraph hcomp
  have horiginal {j : Nat} {b : Node} (hb : cg.nodes[j]? = some b) :
      (componentCandidate graph comp candidate).nodes[j]? = some b := by
    rw [componentCandidate_nodes]
    rwa [hnodes] at hb
  have hshape {j : Nat} {b : Node} (hb : cg.nodes[j]? = some b) : b.border ≠ 3 := by
    rcases (X_componentCandidate_marker_shape hgraph0 hgraph (horiginal hb)).1 with h | h | h <;>
      omega
  have hpp : stages.placement.p = p := by rw [stages.hPlacement]
  have hpr : stages.placement.rm = rm := by rw [stages.hPlacement]
  obtain ⟨hplacedLen, hports⟩ := reservedPorts_marker_lookup stages.hFramesAndPorts
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, proxied, _, _, actual⟩ := componentRunR_stages hrun
  have hproxy : proxyWidths run.coordinateProper run.coordinateXs = .ok (proxied, run.xs) := by
    rw [actual.hCoordProper]
    exact actual.hProxy
  obtain ⟨_, _, hproxyLen, _, hmetadata, hnonproxy⟩ := proxyWidths_rel hproxy
  rw [← actual.hDrop, OrderImpl.dropSynthetic_nodes] at htitle
  have hiP : i < p.nodes.length := by
    have hi := (List.getElem?_eq_some_iff.mp htitle).1
    rwa [hproxyLen, hplacedLen, hpp] at hi
  let n := p.nodes[i]
  have hn : p.nodes[i]? = some n := List.getElem?_eq_getElem hiP
  have hnP : stages.placement.p.nodes[i]? = some n := by rwa [hpp]
  obtain ⟨m, hm, hbPort, _, hrestore⟩ := hports hnP
  obtain ⟨q, hq, _, hbProxy, _⟩ := hmetadata i m hm
  have heq : q = title := Option.some.inj (hq.symm.trans htitle)
  subst q
  have hb : n.node.border = 3 := hbPort.symm.trans (hbProxy.symm.trans hkind)
  have hnC : (coordinateGraphR P exact (some s) labeled).nodes[i]? = some n := by
    rwa [hcoord]
  obtain ⟨hiCopy, j, old, hold, holdB, hcopyPath, hcopyW⟩ :=
    activeCoordinate_title_copy hnorm hlabels (fun hb => hshape hb) hnC hb
  have haway : ∀ d ∈ stages.placement.rm.clusters, d.top ≠ i ∧ d.bottom ≠ i := by
    rw [hpr, hclusters]
    intro d hd
    obtain ⟨ht, hb⟩ := cluster_anchors_are_candidate_indices hd
    have away {k : Nat} (hk : ∃ b,
        (componentCandidateR (some s) graph comp candidate).nodes[k]? = some b) : k ≠ i := by
      obtain ⟨b, hnb⟩ := hk
      rw [← hnodes] at hnb
      have hlabel := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hnb) rfl
      have hlt := (List.getElem?_eq_some_iff.mp hlabel).1
      omega
    exact ⟨away ht, away hb⟩
  obtain ⟨hmn, hxPort⟩ := hrestore haway
  have hm' : run.coordinateProper.nodes[i]? = some n := by rwa [hmn] at hm
  obtain ⟨hwrite, hx⟩ := hnonproxy i n hm' (by simp [hb])
  have hnTitle : n = title := Option.some.inj (hwrite.symm.trans htitle)
  subst title
  have hmC := List.mem_of_getElem? hchild
  rw [hclusters] at hmC
  obtain ⟨entry, hent, hentry⟩ := List.mem_filterMap.mp hmC
  obtain ⟨hentryB, hentryD, _⟩ := clusterEntry_top hentry
  have hentryW : c.titleW = entry.1.w := by
    unfold clusterEntry at hentry
    split at hentry
    · cases hentry
    · rw [← Option.some.inj hentry]
  obtain ⟨_, _, holdPath⟩ := X_cg_group_box hgraph0 hgraph (horiginal hold) holdB
  have holdDecl : old.decl = c.decl := by
    rw [hcopyPath, holdPath, List.getLast?_append] at hpath
    simpa using hpath
  have holdCandidate := hold
  rw [hnodes] at holdCandidate
  have hentryLookup := List.mem_zipIdx_iff_getElem?.mp hent
  have hsame := huniq holdCandidate hentryLookup holdB hentryB (holdDecl.trans hentryD)
  rw [hsame] at holdCandidate
  have holdEq := Option.some.inj (holdCandidate.symm.trans hentryLookup)
  have hWidth : n.node.w = c.titleW :=
    hcopyW.trans ((congrArg Node.w holdEq).trans hentryW.symm)
  obtain ⟨_, _, _, hlen, _⟩ := allocatePl_translation_trace stages.hAllocation
  have hbound : i < stages.shifted.length := by
    rw [hlen, CoordsImpl.crossCoordsClusterWith_length stages.hCross]
    exact hiP
  have hchild' : stages.placement.rm.clusters[child]? = some c := by rwa [hpr]
  have huniq' : (stages.placement.rm.clusters.map (·.decl)).Nodup := by
    rw [hpr, hclusters]
    exact cluster_decl_nodup huniq
  refine ⟨hWidth, ?_⟩
  rw [List.getD_eq_getElem?_getD, hx, Option.getD_some, hxPort]
  have hcenter := regionFrame_marker_set (P := P) (a := stages.allocation) hchild' huniq' hnP
    hbound (Or.inr (Or.inr hb)) hpath haway
  simp only [hb] at hcenter
  have hdelta : stages.allocation.lefts.getD child 0 + stages.allocation.widths.getD child 0 -
      stages.placement.buckets.loopWidth.getD child 0 - stages.allocation.lefts.getD child 0 =
      stages.allocation.widths.getD child 0 - stages.placement.buckets.loopWidth.getD child 0 := by
    omega
  rw [hcenter, hdelta]

end Elegant.Layered.PipelineImpl

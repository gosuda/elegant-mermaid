import Elegant.Layered.RegionPositionsSomeProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem bindOk {α β : Type} {input : Except LayoutError α}
    {next : α → Except LayoutError β} {out : β} (h : input.bind next = .ok out) :
    ∃ a, input = .ok a ∧ next a = .ok out := by
  cases input with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

structure RegionCrossAllocationStages (P : Params) (rm : ComponentRegions)
    (cg : Graph) (labels : List MeasuredLabel) (p : Proper) (minimum : RegionConstraints)
    (layers pinned : List (List Nat)) (xs : List Int) (reserved : List (Option Int))
    (placed : Proper) where
  children : List (List Nat)
  groups : List Nat
  before : List Int
  placement : RegionPlacement
  allocation : RegionAllocation
  shifted : List Int
  hChildren : regionChildren rm = .ok children
  hGroups : nodeGroupsOf rm p = .ok groups
  hTraversal : (childPreorderGo children (children.length + 1) [rm.clusters.length] []).length =
    children.length
  hPinned : pinned = pinLayers p groups children
    (childPreorderGo children (children.length + 1) [rm.clusters.length] []) layers
  hCross : CoordsImpl.crossCoordsClusterWith P.nodeGap P.clusterPad p pinned = .ok before
  hSpans : commonSpansR rm minimum p = .ok ()
  hPlacement : placement =
    ⟨rm, p, children, childPreorderGo children (children.length + 1) [rm.clusters.length] [],
      newRegionBuckets rm cg p groups
        (cg.edges.map fun e => (stackSize cg.slot (routeLabels labels e.decl)).width) before,
      minimum⟩
  hAllocation : allocatePl placement P before = .ok (allocation, shifted)
  hFramesAndPorts : reservedPortsR placement cg labels
    (regionFrames placement P allocation shifted) = .ok (xs, placed)
  hLanes : reserved = allocation.lanes

theorem crossCoordsR_allocation_stages {P : Params} {rm : ComponentRegions} {cg : Graph}
    {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok (xs, pinned, reserved, placed)) :
    Nonempty (RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed) := by
  unfold crossCoordsR at h
  obtain ⟨children, hchildren, h⟩ := bindOk h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    cases h
  · rename_i htraverse
    obtain ⟨groups, hgroups, h⟩ := bindOk h
    obtain ⟨before, hcross, h⟩ := bindOk h
    obtain ⟨spans, hspans, h⟩ := bindOk h
    cases spans
    obtain ⟨⟨allocation, shifted⟩, halloc, h⟩ := bindOk h
    obtain ⟨⟨final, pFinal⟩, hports, h⟩ := bindOk h
    have hout := Except.ok.inj h
    simp only [Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hout
    exact ⟨⟨children, groups, before, _, allocation, shifted, hchildren, hgroups,
      by simpa using htraverse, rfl, hcross, hspans, rfl, halloc, hports, rfl⟩⟩

theorem componentRunR_active_allocation_stages {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∃ ranks p0 labeled p minimum ord reserved budget,
      rankEquivalentR rm cg = .ok (ranks, cg', budget) ∧
      normalize cg' ranks = .ok p0 ∧
      Labels.addLabelNodes cg' p0 (componentLabels cg' labels) = .ok labeled ∧
      coordinateGraphR P exact (some s) labeled = p ∧ constrainR rm P p = .ok minimum ∧
      orderWithBudget p orderOptions = .ok ord ∧
      Nonempty (RegionCrossAllocationStages P rm cg' labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper) := by
  obtain ⟨rs, ranks, budget, p0, labeled, pCoord, minimum, ord, _, reserved, placed, _, _, _,
    hRs, hRank, hNorm, hLabels, hCoord, hMin, hOrd, _, hPlaced, _, _, _, _, _, _, _, _, hProper,
    _, _, _⟩ :=
    componentRunR_specR hrun
  have hrs : rs = some rm := Except.ok.inj (hRs.symm.trans hactive)
  rcases hPlaced with ⟨hnone, _, _, _, _⟩ | ⟨rm', m, hsome, hm, hcross⟩
  · rw [hrs] at hnone
    cases hnone
  have hregion : rm' = rm := Option.some.inj (hsome.symm.trans hrs)
  subst rm'
  rcases hMin with ⟨hnone, _⟩ | ⟨rm', m', hrm', hm', hconstrain⟩
  · rw [hrs] at hnone
    cases hnone
  have hregion : rm' = rm := Option.some.inj (hrm'.symm.trans hrs)
  subst rm'
  have hminimum : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst m'
  rw [← hProper] at hcross
  rcases hRank with ⟨_, hnone, _, _, _, _⟩ | ⟨rm', hrm', hrank⟩
  · rw [hrs] at hnone
    cases hnone
  have hregion : rm' = rm := Option.some.inj (hrm'.symm.trans hrs)
  subst rm'
  exact ⟨ranks, p0, labeled, pCoord, m, ord, reserved, budget, hrank, hNorm, hLabels,
    hCoord, hconstrain, hOrd, crossCoordsR_allocation_stages hcross⟩

private theorem setAt_length {α : Type} (xs : List α) (i : Nat) (a : α) :
    (setAt xs i a).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [setAt, ih]

private theorem setAt_getD {α : Type} (xs : List α) (i j : Nat) (a fallback : α) :
    (setAt xs i a).getD j fallback =
      if j = i ∧ i < xs.length then a else xs.getD j fallback := by
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

/-- The signed translation chosen when a group is visited, using the left table
at the start of that visit, not the input to the crossing pass. -/
def regionBucketShift (pl : RegionPlacement) (lefts : List Int) (g : Nat) : Int :=
  lefts.getD g 0 + (if g != pl.rm.clusters.length then pl.minimum.origins.getD g 0 else 0) -
    pl.buckets.low.getD g 0

private abbrev AllocationState := List Int × List Int × List (Option Int)

private theorem allocateGroup_centers {pl : RegionPlacement} {P : Params} {widths : List Int}
    {g : Nat} {initial final : AllocationState}
    (h : allocateGroup pl P widths g initial = .ok final) :
    final.1 = (pl.buckets.members.getD g []).foldl
      (fun xs v => setAt xs v (xs.getD v 0 + regionBucketShift pl initial.2.1 g)) initial.1 := by
  rcases initial with ⟨xs, lefts, lanes⟩
  unfold allocateGroup at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  have hx := (congrArg Prod.fst (Except.ok.inj h)).symm
  let members := pl.buckets.members.getD g []
  let step (x : List Int) (v : Nat) := setAt x v (x.getD v 0 + regionBucketShift pl lefts g)
  change final.1 = (if members.isEmpty then xs else members.foldl step xs) at hx
  change final.1 = members.foldl step xs
  by_cases hm : members.isEmpty
  · rw [ite_eq_left hm] at hx
    rwa [List.nil_of_isEmpty hm, List.foldl_nil]
  · rwa [ite_eq_right hm] at hx

private theorem shiftMembers (members : List Nat) (xs : List Int) (shift : Int) :
    let shifted := members.foldl (fun x i => setAt x i (x.getD i 0 + shift)) xs
    shifted.length = xs.length ∧
      ∀ v, v < xs.length → shifted.getD v 0 =
        xs.getD v 0 + (members.count v : Int) * shift := by
  dsimp only
  induction members generalizing xs with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons]
    have hs := ih (setAt xs i (xs.getD i 0 + shift))
    rw [setAt_length] at hs
    refine ⟨hs.1, ?_⟩
    intro v hv
    rw [hs.2 v hv, setAt_getD]
    by_cases he : i = v
    · subst i
      rw [ite_eq_left ⟨rfl, hv⟩, List.count_cons_self, Int.natCast_add, Int.add_mul]
      simp only [Int.natCast_one, Int.one_mul]
      omega
    · rw [ite_eq_right (fun h => he h.1.symm), List.count_cons_of_ne he]

private theorem allocateGroupFold_trace (pl : RegionPlacement) (P : Params)
    (groups : List Nat) (initial final : AllocationState)
    (h : groups.foldlM (fun state g => allocateGroup pl P (reserveWidths pl P) g state)
        initial = .ok final) :
    ∃ visits : List (Nat × Int), visits.map Prod.fst = groups ∧
      (∀ k g shift, visits[k]? = some (g, shift) →
        ∃ left : AllocationState,
          (groups.take k).foldlM (fun state g => allocateGroup pl P (reserveWidths pl P) g state)
            initial = .ok left ∧ shift = regionBucketShift pl left.2.1 g) ∧
      final.1.length = initial.1.length ∧
      ∀ v, v < initial.1.length → final.1.getD v 0 = initial.1.getD v 0 +
        (visits.map fun q => ((pl.buckets.members.getD q.1 []).count v : Int) * q.2).sum := by
  induction groups generalizing initial with
  | nil =>
    change Except.ok initial = Except.ok final at h
    cases h
    exact ⟨[], rfl, by simp, rfl, by simp⟩
  | cons g gs ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hstep, htail⟩ := bindOk h
    obtain ⟨visits, hgroups, hprefix, htailLength, hsum⟩ := ih mid htail
    have hcenters := allocateGroup_centers hstep
    have hmembers := shiftMembers (pl.buckets.members.getD g []) initial.1
      (regionBucketShift pl initial.2.1 g)
    dsimp only at hmembers
    rw [← hcenters] at hmembers
    refine ⟨(g, regionBucketShift pl initial.2.1 g) :: visits, by simp [hgroups],
      ?_, htailLength.trans hmembers.1, ?_⟩
    · intro k g' shift hx
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact ⟨initial, rfl, rfl⟩
      | succ k =>
        obtain ⟨left, hleft, hshift⟩ := hprefix k g' shift
          (by simpa only [List.getElem?_cons_succ] using hx)
        refine ⟨left, ?_, hshift⟩
        simp only [List.take_succ_cons, List.foldlM_cons, hstep, bind, Except.bind, hleft]
    · intro v hv
      rw [hsum v (by rwa [hmembers.1]), hmembers.2 v hv, List.map_cons, List.sum_cons]
      exact Int.add_assoc _ _ _

/-- Allocation changes a center by the sum of its actual visits' translations.
Each listed translation is backed by the successful allocation prefix that
produces its left table. This applies to different buckets as well as one. -/
theorem allocatePl_translation_trace {pl : RegionPlacement} {P : Params} {xs shifted : List Int}
    {allocation : RegionAllocation} (h : allocatePl pl P xs = .ok (allocation, shifted)) :
    ∃ visits : List (Nat × Int), visits.map Prod.fst = pl.order ∧
      (∀ k g shift, visits[k]? = some (g, shift) →
        ∃ left : List Int × List Int × List (Option Int),
          (pl.order.take k).foldlM (fun state g => allocateGroup pl P (reserveWidths pl P) g state)
            (xs, List.replicate (pl.rm.clusters.length + 1) 0,
              List.replicate pl.p.chains.length none) = .ok left ∧
            shift = regionBucketShift pl left.2.1 g) ∧
      shifted.length = xs.length ∧
      ∀ v, v < xs.length → shifted.getD v 0 = xs.getD v 0 +
        (visits.map fun q => ((pl.buckets.members.getD q.1 []).count v : Int) * q.2).sum := by
  unfold allocatePl at h
  obtain ⟨final, hfold, h⟩ := bindOk h
  have hx : shifted = final.1 := (congrArg Prod.snd (Except.ok.inj h)).symm
  rw [hx]
  exact allocateGroupFold_trace pl P _ _ _ hfold

/-- A child's left boundary is the parent bucket's right boundary plus the
reserved widths of the preceding children. Lane allocation does not change
that boundary. -/
theorem allocateGroup_child_left {pl : RegionPlacement} {P : Params} {widths : List Int}
    {g child k : Nat} {initial final : List Int × List Int × List (Option Int)}
    (h : allocateGroup pl P widths g initial = .ok final)
    (hchildren : (pl.children.getD g []).Nodup)
    (hchild : (pl.children.getD g [])[k]? = some child)
    (hbound : child < initial.2.1.length) :
    final.2.1.getD child 0 =
      initial.2.1.getD g 0 +
        (if g != pl.rm.clusters.length then pl.minimum.origins.getD g 0 else 0) +
        pl.buckets.widths.getD g 0 +
        (((pl.children.getD g []).take k).map fun c => widths.getD c 0).sum := by
  let step (acc : Int × List Int) (c : Nat) : Except LayoutError (Int × List Int) :=
    .ok (acc.1 + widths.getD c 0, setAt acc.2 c acc.1)
  have unchanged (children : List Nat) (start finish : Int × List Int)
      (hnot : child ∉ children) (hfold : children.foldlM step start = .ok finish) :
      finish.2.getD child 0 = start.2.getD child 0 := by
    induction children generalizing start with
    | nil =>
      change Except.ok start = Except.ok finish at hfold
      rw [← Except.ok.inj hfold]
    | cons c cs ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨mid, hstep, htail⟩ := bindOk hfold
      have hresult := ih mid (fun hc => hnot (List.mem_cons_of_mem _ hc)) htail
      rw [hresult, ← Except.ok.inj hstep]
      change (setAt start.2 c start.1).getD child 0 = start.2.getD child 0
      rw [setAt_getD, ite_eq_right (fun he => hnot (List.mem_cons.mpr (Or.inl he.1)))]
  have childStart (children : List Nat) (start finish : Int × List Int) (i : Nat)
      (hunique : children.Nodup) (hslot : children[i]? = some child)
      (hin : child < start.2.length) (hfold : children.foldlM step start = .ok finish) :
      finish.2.getD child 0 = start.1 + ((children.take i).map fun c => widths.getD c 0).sum := by
    induction children generalizing start i with
    | nil => simp at hslot
    | cons c cs ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨mid, hstep, htail⟩ := bindOk hfold
      have hmid : (start.1 + widths.getD c 0, setAt start.2 c start.1) = mid :=
        Except.ok.inj hstep
      have ⟨hnot, hnodup⟩ := List.nodup_cons.mp hunique
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hslot
        subst c
        rw [unchanged cs mid finish hnot htail, ← hmid]
        change (setAt start.2 child start.1).getD child 0 = _
        rw [setAt_getD, ite_eq_left ⟨rfl, hin⟩]
        simp
      | succ i =>
        have htailBound : child < mid.2.length := by
          rw [← hmid]
          change child < (setAt start.2 c start.1).length
          rwa [setAt_length]
        have hs := ih mid i hnodup (by simpa only [List.getElem?_cons_succ] using hslot)
          htailBound htail
        rw [hs, ← hmid, List.take_succ_cons, List.map_cons, List.sum_cons]
        change start.1 + widths.getD c 0 + _ = start.1 + (widths.getD c 0 + _)
        exact Int.add_assoc _ _ _
  rcases initial with ⟨xs, lefts, lanes⟩
  unfold allocateGroup at h
  dsimp only at h
  obtain ⟨placed, hplaced, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  have hlefts : final.2.1 = placed.2 :=
    (congrArg (fun out : AllocationState => out.2.1) (Except.ok.inj h)).symm
  rw [hlefts]
  exact childStart _ _ _ k hchildren hchild hbound hplaced

private theorem coordinateGraphR_border_record (P : Params) (exact : List Nat) (s : RegionSpec)
    {labeled : Proper} {v : Nat} {n : ProperNode} (hn : labeled.nodes[v]? = some n) :
    ∃ m, (coordinateGraphR P exact (some s) labeled).nodes[v]? = some m ∧
      m.node.border = n.node.border := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  have hkeys := sizeProperPortsX_key P exact labeled v
  change (sized.nodes[v]?).map _ = _ at hkeys
  cases hs : sized.nodes[v]? with
  | none => simp [hs, hn] at hkeys
  | some sz =>
    simp only [hs, hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkeys
    let t : ProperNode := if sz.node.border == -2 || sz.node.border == 2 then
      { sz with node := { sz.node with w := 0, h := 0 } } else sz
    have ht : titled.nodes[v]? = some t := by
      unfold titled titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by
        simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hs).1)]
      simp only [List.getElem?_map, hs, Option.map_some] <;> rfl
    have htitle : t.node.border = sz.node.border := by
      dsimp only [t]
      split <;> rfl
    obtain ⟨_, hbordered, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    have hc : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[v]? =
        some (clearF t) := by
      rw [clearProxyExtents_nodes, List.getElem?_map, hbordered,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1, ht] <;> rfl
    obtain ⟨m, hm, _⟩ := materialize_exists _ hc
    obtain ⟨old, hold, _, hborder, _, _⟩ := materialize_lookup _ hm
    have heq : old = clearF t := Option.some.inj (hold.symm.trans hc)
    subst old
    exact ⟨m, hm, hborder.trans ((clearF_keys t).2.1.trans (htitle.trans hkeys.2.1))⟩

private theorem resolvedAnchors_markers {P : Params} {s : RegionSpec} {inp : Input}
    {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∀ c ∈ rm.clusters, (∃ n, cg.nodes[c.top]? = some n ∧ n.border ≠ 0) ∧
      (∃ n, cg.nodes[c.bottom]? = some n ∧ n.border ≠ 0) := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bindOk h
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

private def IsNotAnchor (rm : ComponentRegions) (v : Nat) : Prop :=
  ∀ c ∈ rm.clusters, c.top ≠ v ∧ c.bottom ≠ v

private theorem regionFrames_nonanchor {pl : RegionPlacement} {P : Params}
    {allocation : RegionAllocation} {xs : List Int} {v : Nat} {n : ProperNode}
    (hn : pl.p.nodes[v]? = some n) (hplain : n.node.border = 0)
    (haway : IsNotAnchor pl.rm v) :
    (regionFrames pl P allocation xs).getD v 0 = xs.getD v 0 := by
  unfold regionFrames
  apply OrderImpl.foldl_inv (fun x : List Int => x.getD v 0 = xs.getD v 0) _ _ _ rfl
  intro x hx job hj
  obtain ⟨ht, hb⟩ := haway job.1
    (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hj))
  dsimp only
  rw [setAt_getD, ite_eq_right (fun he => hb he.1.symm),
    setAt_getD, ite_eq_right (fun he => ht he.1.symm)]
  apply OrderImpl.foldl_inv (fun x : List Int => x.getD v 0 = xs.getD v 0) _ _ _ hx
  intro y hy q hq
  by_cases he : q.2 = v
  · have hlookup := List.mem_zipIdx_iff_getElem?.mp hq
    rw [he, hn] at hlookup
    have hz : q.1.node.border = 0 := by rw [← Option.some.inj hlookup, hplain]
    simp only [hz]
    split <;> exact hy
  · have hwrite (value : Int) : (setAt y q.2 value).getD v 0 = xs.getD v 0 := by
      rw [setAt_getD, ite_eq_right (fun hf => he hf.1.symm)]
      exact hy
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
    · rw [← Except.ok.inj h, setAt_getD, ite_eq_right (fun he => hk he.1.symm)]
  · cases h

private theorem reservedPortsR_node_law {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper} {v : Nat}
    {n : ProperNode} (h : reservedPortsR pl cg labels xs = .ok (ys, placed))
    (hn : pl.p.nodes[v]? = some n) :
    ∃ m, placed.nodes[v]? = some m ∧ m.node.border = n.node.border ∧
      (IsNotAnchor pl.rm v → m = n ∧ ys.getD v 0 = xs.getD v 0) := by
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
      ∃ dst, out.2[v]? = some dst ∧ dst.node.border = src.node.border ∧
        ((∀ q ∈ entries, q.1.top ≠ v ∧ q.1.bottom ≠ v) →
          dst = src ∧ out.1.getD v 0 = start.1.getD v 0) := by
    induction entries generalizing start src with
    | nil =>
      change Except.ok start = Except.ok out at hfold
      rw [← Except.ok.inj hfold]
      exact ⟨src, hsrc, rfl, fun _ => ⟨rfl, rfl⟩⟩
    | cons q rest ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨mid, hmid, hrest⟩ := bindOk hfold
      dsimp only [step] at hmid
      split at hmid
      · cases hmid
      · obtain ⟨x1, hx1, hmid⟩ := bindOk hmid
        obtain ⟨x2, hx2, hmid⟩ := bindOk hmid
        have hx : mid.1 = x2 := (congrArg Prod.fst (Except.ok.inj hmid)).symm
        have hrecord : ∃ dst, mid.2[v]? = some dst ∧ dst.node.border = src.node.border := by
          rw [← Except.ok.inj hmid]
          dsimp only
          rw [Array.set!_eq_setIfInBounds]
          by_cases he : q.1.top = v
          · have hlt := (Array.getElem?_eq_some_iff.mp hsrc).1
            have hget : start.2.getD v default = src := by
              simp only [Array.getD_eq_getD_getElem?, hsrc, Option.getD_some]
            rw [he, Array.getElem?_setIfInBounds_self_of_lt hlt, hget]
            exact ⟨_, rfl, rfl⟩
          · rw [Array.getElem?_setIfInBounds_ne he]
            exact ⟨src, hsrc, rfl⟩
        obtain ⟨midNode, hlookup, hborder⟩ := hrecord
        obtain ⟨dst, hdst, hb, hother⟩ := ih mid midNode hlookup hrest
        refine ⟨dst, hdst, hb.trans hborder, ?_⟩
        intro haway
        obtain ⟨ht, hb⟩ := haway q List.mem_cons_self
        obtain ⟨heq, hxs⟩ := hother (fun r hr => haway r (List.mem_cons_of_mem _ hr))
        have hnode : mid.2[v]? = some src := by
          rw [← Except.ok.inj hmid]
          dsimp only
          rwa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne ht]
        have hcurrent : mid.1.getD v 0 = start.1.getD v 0 := by
          rw [hx]
          exact (clusterPortR_other hx2 hb).trans (clusterPortR_other hx1 ht)
        exact ⟨heq.trans (Option.some.inj (hlookup.symm.trans hnode)), hxs.trans hcurrent⟩
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = _ at h
  obtain ⟨out, hfold, hresult⟩ := bindOk h
  have harray : placed.nodes = out.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) (Except.ok.inj hresult)).symm
  have hxs : ys = out.1 := (congrArg Prod.fst (Except.ok.inj hresult)).symm
  rw [harray, Array.getElem?_toList, hxs]
  obtain ⟨m, hm, hborder, hother⟩ := preserve _ _ _ n
    (by rwa [List.getElem?_toArray]) hfold
  exact ⟨m, hm, hborder, fun haway => hother (fun q hq => haway q.1
    (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq)))⟩

theorem reservedPortsR_preserves_border {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs ys : List Int} {placed : Proper} {v : Nat}
    {n : ProperNode} (h : reservedPortsR pl cg labels xs = .ok (ys, placed))
    (hn : pl.p.nodes[v]? = some n) :
    ∃ m, placed.nodes[v]? = some m ∧ m.node.border = n.node.border := by
  obtain ⟨m, hm, hb, _⟩ := reservedPortsR_node_law h hn
  exact ⟨m, hm, hb⟩

/-- On any pinned layer in a successful active run, a final plain node is the
same record as before allocation. Frames, reserved ports and proxy widths
leave its allocated center unchanged. -/
theorem componentRunR_active_plain_centers_with_minimum {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult) (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages P rm cg' labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper,
      constrainR rm P p = .ok minimum ∧
      ∀ {layer : List Nat} {i v : Nat} {n : ProperNode}, layer ∈ run.layers →
        layer[i]? = some v → run.coordinateProper.nodes[v]? = some n → n.node.border = 0 →
        p.nodes[v]? = some n ∧ run.coordinateXs.getD v 0 = stages.shifted.getD v 0 ∧
          run.xs.getD v 0 = stages.shifted.getD v 0 := by
  obtain ⟨_, _, labeled, p, minimum, ord, reserved, _, hrank, hnorm, hlabels, hcoord, hmin, _,
    ⟨stages⟩⟩ := componentRunR_active_allocation_stages hrun hactive
  refine ⟨p, minimum, ord, reserved, stages, hmin, ?_⟩
  intro layer i v n hl hv hnode hplain
  obtain ⟨_, _, hrange, _, _⟩ := CoordsImpl.crossCoordsClusterWith_spec stages.hCross
  have hbound := CoordsImpl.layers_mem_lt hrange hl hv
  obtain ⟨src, hsrc⟩ : ∃ src, p.nodes[v]? = some src := by
    cases he : p.nodes[v]? with
    | none => have := List.getElem?_eq_none_iff.mp he; omega
    | some src => exact ⟨src, rfl⟩
  have hpp : stages.placement.p = p := by rw [stages.hPlacement]
  have hrm : stages.placement.rm = rm := by rw [stages.hPlacement]
  have hlookup : stages.placement.p.nodes[v]? = some src := by rwa [hpp]
  obtain ⟨m, hm, hb, hother⟩ := reservedPortsR_node_law stages.hFramesAndPorts hlookup
  have he : m = n := Option.some.inj (hm.symm.trans hnode)
  subst m
  have hsrcPlain : src.node.border = 0 := hb.symm.trans hplain
  have hmarked {k : Nat} (hk : ∃ orig, cg.nodes[k]? = some orig ∧ orig.border ≠ 0) :
      k ≠ v := by
    obtain ⟨orig, horig, hnonzero⟩ := hk
    intro he
    subst k
    rw [← rankEquivalentR_nodes_eq hrank] at horig
    obtain ⟨mark, hmark, hbmark⟩ := coordinateGraphR_border_record P exact s
      (addLabelNodes_untouched_node hlabels (normalize_node_record hnorm horig) rfl)
    rw [hcoord, hsrc] at hmark
    rw [← Option.some.inj hmark, hsrcPlain] at hbmark
    exact hnonzero hbmark.symm
  have haway : IsNotAnchor stages.placement.rm v := by
    rw [hrm]
    intro c hc
    obtain ⟨ht, hb⟩ := resolvedAnchors_markers hactive c hc
    exact ⟨hmarked ht, hmarked hb⟩
  obtain ⟨hsame, hxports⟩ := hother haway
  have hx := hxports.trans (regionFrames_nonanchor hlookup hsrcPlain haway)
  have hnonproxy : ¬ (n.node.border = -2 ∨ n.node.border = 2) := by simp [hplain]
  exact ⟨hsame.symm ▸ hsrc, hx, (componentRunR_placement_xsR hrun hnode hnonproxy).trans hx⟩

theorem componentRunR_active_plain_centers {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult) (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages P rm cg' labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper,
      ∀ {layer : List Nat} {i v : Nat} {n : ProperNode}, layer ∈ run.layers →
        layer[i]? = some v → run.coordinateProper.nodes[v]? = some n → n.node.border = 0 →
        p.nodes[v]? = some n ∧ run.coordinateXs.getD v 0 = stages.shifted.getD v 0 ∧
          run.xs.getD v 0 = stages.shifted.getD v 0 := by
  obtain ⟨p, minimum, ord, reserved, stages, _, hcenters⟩ :=
    componentRunR_active_plain_centers_with_minimum hrun hactive
  exact ⟨p, minimum, ord, reserved, stages, hcenters⟩

/-- In the active branch, the crossing pass pays the full plain-node gap.
The published gap differs from that gap by exactly the signed difference
between the two endpoints' accumulated bucket translations. -/
theorem componentRunR_active_plain_gap_stages {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult) (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages P rm cg' labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper,
      ∃ visits : List (Nat × Int), visits.map Prod.fst = stages.placement.order ∧
      (∀ k g shift, visits[k]? = some (g, shift) →
        ∃ left : List Int × List Int × List (Option Int),
          (stages.placement.order.take k).foldlM
            (fun state g => allocateGroup stages.placement P (reserveWidths stages.placement P) g state)
            (stages.before, List.replicate (stages.placement.rm.clusters.length + 1) 0,
              List.replicate stages.placement.p.chains.length none) = .ok left ∧
            shift = regionBucketShift stages.placement left.2.1 g) ∧
      ∀ {layer : List Nat} {i j a b : Nat} {na nb : ProperNode}, layer ∈ run.layers →
        i < j → layer[i]? = some a → layer[j]? = some b →
        run.coordinateProper.nodes[a]? = some na → run.coordinateProper.nodes[b]? = some nb →
        na.node.border = 0 → nb.node.border = 0 →
        CoordsImpl.coordSep (min P.nodeGap P.clusterPad) run.coordinateProper a b ≤
            stages.before.getD b 0 - stages.before.getD a 0 ∧
          let displacement (v : Nat) :=
            (visits.map fun q => ((stages.placement.buckets.members.getD q.1 []).count v : Int) *
              q.2).sum
          run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 =
            stages.before.getD b 0 - stages.before.getD a 0 + (displacement b - displacement a) ∧
          run.xs.getD b 0 - run.xs.getD a 0 =
            run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  obtain ⟨p, minimum, ord, reserved, stages, hcenters⟩ :=
    componentRunR_active_plain_centers hrun hactive
  obtain ⟨visits, horder, hvisit, _, hmove⟩ := allocatePl_translation_trace stages.hAllocation
  refine ⟨p, minimum, ord, reserved, stages, visits, horder, hvisit, ?_⟩
  intro layer i j a b na nb hl hij ha hb hna hnb hpa hpb
  obtain ⟨hsa, hca, hxa⟩ := hcenters hl ha hna hpa
  obtain ⟨hsb, hcb, hxb⟩ := hcenters hl hb hnb hpb
  have hcross := crossCoordsClusterWith_plain_order stages.hCross hl hij ha hb hsa hpa
  refine ⟨?_, ?_, by rw [hxa, hxb, hca, hcb]⟩
  · simpa only [CoordsImpl.coordSep, CoordsImpl.nodeW, hsa, hsb, hna, hnb] using hcross
  · have hlen := CoordsImpl.crossCoordsClusterWith_length stages.hCross
    have haLen : a < stages.before.length := by
      rw [hlen]
      exact (List.getElem?_eq_some_iff.mp hsa).1
    have hbLen : b < stages.before.length := by
      rw [hlen]
      exact (List.getElem?_eq_some_iff.mp hsb).1
    rw [hca, hcb, hmove a haLen, hmove b hbLen]
    have signedGap (x y dx dy : Int) : (y + dy) - (x + dx) = y - x + (dy - dx) := by omega
    exact signedGap _ _ _ _

end Elegant.Layered.PipelineImpl

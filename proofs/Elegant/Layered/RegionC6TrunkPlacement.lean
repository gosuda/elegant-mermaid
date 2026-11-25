import Elegant.Layered.RegionSharedAllocation
import Elegant.Layered.RegionFixedBoxDominance

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Elegant.Layered.PipelineImpl.RegionOrdinaryC6

open RegionImpl

abbrev TrunkAllocationState := List Int × List Int × List (Option Int)

private theorem setAt_length {α : Type} (xs : List α) (i : Nat) (a : α) :
    (setAt xs i a).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [setAt, ih]

private theorem setAt_getD {α : Type} (xs : List α) (i j : Nat) (a d : α) :
    (setAt xs i a).getD j d = if j = i ∧ i < xs.length then a else xs.getD j d := by
  induction xs generalizing i j with
  | nil => simp [setAt]
  | cons x xs ih =>
    cases i with
    | zero => cases j <;> simp [setAt]
    | succ i =>
      cases j with
      | zero => simp [setAt]
      | succ j => simpa [setAt, List.getD_cons_succ] using ih i j

private theorem foldOkInv {α β : Type} {f : α → β → Except LayoutError α}
    {I : α → Prop} {xs : List β} {a b : α}
    (hi : I a) (hs : ∀ a x b, I a → x ∈ xs → f a x = .ok b → I b)
    (h : xs.foldlM f a = .ok b) : I b := by
  induction xs generalizing a with
  | nil =>
    change Except.ok a = .ok b at h
    exact (Except.ok.inj h) ▸ hi
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hm, ht⟩ := bind_ok h
    exact ih (hs a x mid hi (List.Mem.head _) hm)
      (fun a y b ha hy hb => hs a y b ha (List.Mem.tail _ hy) hb) ht

private def setMemberStep (parents : List Int) (s : LocalRegionSet) (i : Nat)
    (owner : List Int) (r : Nat) : Except LayoutError (List Int) :=
  if parents.length ≤ r ∨ parents.getD r 0 != s.parent ∨ 0 ≤ owner.getD r (-1)
  then .error .domain else .ok (setAt owner r (i : Int))

private def setIndexStep (parents : List Int) (acc : List Int × List Int × Nat)
    (q : LocalRegionSet × Nat) : Except LayoutError (List Int × List Int × Nat) := do
  let s := q.1
  if parents.length ≤ s.parent ∨ s.regions.isEmpty ∨ 0 ≤ acc.1.getD s.parent (-1) then
    throw .domain
  else
    let owner ← s.regions.foldlM (setMemberStep parents s q.2) acc.2.1
    pure (setAt acc.1 s.parent (q.2 : Int), owner, acc.2.2 + s.regions.length)

private theorem setMembers_valid {parents : List Int} {sets : List LocalRegionSet}
    {out : List Int × Nat} (h : indexRegionSets parents sets = .ok out) :
    ∀ q ∈ sets.zipIdx, ∀ r ∈ q.1.regions,
      r < parents.length ∧ parents.getD r 0 = (q.1.parent : Int) := by
  have memberFold (s : LocalRegionSet) (i : Nat) (regions : List Nat) {before after : List Int}
      (hr : regions.foldlM (setMemberStep parents s i) before = .ok after) :
      ∀ r ∈ regions, r < parents.length ∧ parents.getD r 0 = (s.parent : Int) := by
    induction regions generalizing before with
    | nil => simp
    | cons r rest ih =>
      rw [List.foldlM_cons] at hr
      obtain ⟨mid, hm, ht⟩ := bind_ok hr
      unfold setMemberStep at hm
      split at hm
      · cases hm
      · rename_i hguard
        intro node hn
        rcases List.mem_cons.mp hn with rfl | hn
        · refine ⟨Nat.lt_of_not_ge fun hh => hguard (Or.inl hh), ?_⟩
          apply Classical.byContradiction
          intro hh
          exact hguard (Or.inr (Or.inl (bne_iff_ne.mpr hh)))
        · exact ih ht node hn
  have indexFold (jobs : List (LocalRegionSet × Nat)) {before after : List Int × List Int × Nat}
      (hi : jobs.foldlM (setIndexStep parents) before = .ok after) :
      ∀ q ∈ jobs, ∀ r ∈ q.1.regions,
        r < parents.length ∧ parents.getD r 0 = (q.1.parent : Int) := by
    induction jobs generalizing before with
    | nil => simp
    | cons q jobs ih =>
      rw [List.foldlM_cons] at hi
      obtain ⟨mid, hm, ht⟩ := bind_ok hi
      unfold setIndexStep at hm
      dsimp only at hm
      split at hm
      · cases hm
      · obtain ⟨_, hfold, _⟩ := bind_ok hm
        intro t ht'
        rcases List.mem_cons.mp ht' with rfl | ht'
        · exact memberFold _ _ _ hfold
        · exact ih ht t ht'
  unfold indexRegionSets at h
  obtain ⟨_, hfold, _⟩ := bind_ok h
  exact indexFold _ hfold

private theorem constrainR_valid_setMembers {P : Params} {rm : ComponentRegions} {p : Proper}
    {minimum : RegionConstraints} (h : constrainR rm P p = .ok minimum) :
    ∀ q ∈ rm.sets.zipIdx, ∀ r ∈ q.1.regions,
      r < rm.parents.length ∧ rm.parents.getD r 0 = (q.1.parent : Int) := by
  unfold constrainR at h
  obtain ⟨_, _, h⟩ := bind_ok h
  unfold solveRegions at h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, hi, _⟩ := bind_ok h
  exact setMembers_valid hi

private def ChildParents (rm : ComponentRegions) (rows : List (List Nat)) : Prop :=
  ∀ g c, c ∈ rows.getD g [] → c < rm.clusters.length ∧ parentGroup rm c = g

private theorem regionChildren_parents {P : Params} {rm : ComponentRegions} {p : Proper}
    {minimum : RegionConstraints} {children : List (List Nat)}
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) (h : regionChildren rm = .ok children) :
    ChildParents rm children := by
  let init : List (List Nat) := List.replicate (rm.clusters.length + 1) []
  let insert (rows : List (List Nat)) (c : Nat) :=
    setAt rows (parentGroup rm c) (rows.getD (parentGroup rm c) [] ++ [c])
  have hbase : ChildParents rm ((List.range rm.clusters.length).foldl insert init) := by
    apply OrderImpl.foldl_inv (ChildParents rm)
    · intro g c hc
      rw [show init.getD g [] = [] from by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl] at hc
      exact (List.not_mem_nil hc).elim
    · intro rows hh key hk g c hc
      change c ∈ (insert rows key).getD g [] at hc
      dsimp only [insert] at hc
      rw [setAt_getD] at hc
      split at hc
      · rename_i hwrite
        rcases List.mem_append.mp hc with hc | hc
        · rw [hwrite.1]
          exact hh _ _ hc
        · rw [List.mem_singleton.mp hc, hwrite.1]
          exact ⟨List.mem_range.mp hk, rfl⟩
      · exact hh _ _ hc
  unfold regionChildren at h
  refine foldOkInv hbase ?_ h
  intro rows q out hrows hq hstep
  dsimp only at hstep
  split at hstep
  · cases hstep
  · rename_i first _
    let owner : List Nat :=
      q.1.regions.foldl (fun ow r => setAt ow r q.2)
        (List.replicate rm.clusters.length rm.clusters.length)
    let kept := (rows.getD q.1.parent []).filter fun g => !(owner.getD g rm.clusters.length == q.2)
    have hout : out = setAt rows q.1.parent (kept.take first ++ q.1.regions ++ kept.drop first) :=
      (Except.ok.inj hstep).symm
    intro g c hc
    rw [hout, setAt_getD] at hc
    split at hc
    · rename_i hwrite
      rw [hwrite.1]
      have hkeep : ∀ n ∈ kept, n < rm.clusters.length ∧ parentGroup rm n = q.1.parent :=
        fun n hn => hrows _ _ (List.mem_filter.mp hn).1
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · exact hkeep c (List.mem_of_mem_take hc)
        · obtain ⟨hle, hp⟩ := constrainR_valid_setMembers hmin q hq c hc
          refine ⟨by rwa [hparents] at hle, ?_⟩
          have hget : rm.parents.getD c (-1) = rm.parents.getD c 0 := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hle, Option.getD_some]
          rw [parentGroup, hget, hp, ite_eq_left (Int.natCast_nonneg _), Int.toNat_natCast]
      · exact hkeep c (List.mem_of_mem_drop hc)
    · exact hrows _ _ hc

/-- A path along the actual allocation child rows, including the empty path. -/
inductive TrunkBranch (rows : List (List Nat)) : Nat → Nat → Prop where
  | here (g : Nat) : TrunkBranch rows g g
  | step {g c d : Nat} (hc : c ∈ rows.getD g []) (rest : TrunkBranch rows c d) :
      TrunkBranch rows g d

private structure PreorderFrontier (rm : ComponentRegions) (rows : List (List Nat))
    (visited pending : List Nat) : Prop where
  unique : (visited ++ pending).Nodup
  introduced : ∀ c ∈ visited ++ pending, c = rm.clusters.length ∨
    (c < rm.clusters.length ∧ ∃ g ∈ visited, c ∈ rows.getD g [])
  ordered : visited.Pairwise (fun a b => a ∉ rows.getD b [])
  noSelf : ∀ g ∈ visited, g ∉ rows.getD g []
  reachable : ∀ c ∈ visited ++ pending, TrunkBranch rows rm.clusters.length c

private theorem preorder_frontier {rm : ComponentRegions} {rows : List (List Nat)}
    (hparents : ChildParents rm rows) (hnodup : ∀ g, (rows.getD g []).Nodup)
    (fuel : Nat) {visited pending : List Nat}
    (h : PreorderFrontier rm rows visited pending) :
    PreorderFrontier rm rows (childPreorderGo rows fuel pending visited) [] := by
  induction fuel generalizing visited pending with
  | zero =>
    change PreorderFrontier rm rows visited []
    exact ⟨by simpa using (List.nodup_append.mp h.unique).1,
      fun c hc => h.introduced c (List.mem_append_left _ (by simpa using hc)),
      h.ordered, h.noSelf, fun c hc => h.reachable c (List.mem_append_left _ (by simpa using hc))⟩
  | succ fuel ih =>
    cases hv : pending.getLast? with
    | none =>
      have he := List.getLast?_eq_none_iff.mp hv
      subst pending
      exact h
    | some g =>
      obtain ⟨pending, rfl⟩ := List.getLast?_eq_some_iff.mp hv
      rw [childPreorderGo, hv, List.dropLast_concat]
      have hgPending : g ∈ pending ++ [g] := List.mem_append_right _ (by simp)
      have hgNew : g ∉ visited := by
        intro hg
        exact (List.nodup_append.mp h.unique).2.2 g hg g hgPending rfl
      have hFresh : ∀ c ∈ rows.getD g [], c ∉ visited ++ (pending ++ [g]) := by
        intro c hc hold
        obtain ⟨hb, hp⟩ := hparents g c hc
        rcases h.introduced c hold with hroot | ⟨_, par, hpar, hchild⟩
        · omega
        · exact hgNew (((hparents par c hchild).2.symm.trans hp) ▸ hpar)
      have hprev : ∀ c ∈ (visited ++ [g]) ++ pending, c ∈ visited ++ (pending ++ [g]) := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · rcases List.mem_append.mp hc with hc | hc
          · exact List.mem_append_left _ hc
          · exact List.mem_append_right _ (List.mem_append_right _ hc)
        · exact List.mem_append_right _ (List.mem_append_left _ hc)
      have hpre : ((visited ++ [g]) ++ pending).Nodup := by
        apply List.Perm.nodup _ h.unique
        simpa only [List.append_assoc] using
          (List.Perm.append_left visited (List.perm_append_comm (l₁ := pending) (l₂ := [g])))
      have hrev : (rows.getD g []).reverse.Nodup := by
        apply List.pairwise_reverse.mpr
        exact List.Pairwise.imp (fun hn => Ne.symm hn) (hnodup g)
      refine ih ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [← List.append_assoc]
        refine List.nodup_append.mpr ⟨hpre, hrev, ?_⟩
        intro a ha b hb hab
        exact hFresh b (List.mem_reverse.mp hb) (hab ▸ hprev a ha)
      · intro c hc
        simp only [← List.append_assoc] at hc
        rcases List.mem_append.mp hc with hc | hc
        · rcases h.introduced c (hprev c hc) with hh | ⟨hb, par, hpar, hcp⟩
          · exact Or.inl hh
          · exact Or.inr ⟨hb, par, List.mem_append_left _ hpar, hcp⟩
        · have hmem := List.mem_reverse.mp hc
          exact Or.inr ⟨(hparents g c hmem).1, g, List.mem_append_right _ (by simp), hmem⟩
      · refine List.pairwise_append.mpr ⟨h.ordered, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton.mp hb]
        exact fun hm => hFresh a hm (List.mem_append_left _ ha)
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact h.noSelf i hi
        · rw [List.mem_singleton.mp hi]
          exact fun hself => hFresh g hself (List.mem_append_right _ hgPending)
      · intro c hc
        simp only [← List.append_assoc] at hc
        rcases List.mem_append.mp hc with hc | hc
        · exact h.reachable c (hprev c hc)
        · have hg := h.reachable g (List.mem_append_right _ hgPending)
          have appendChild {parent g : Nat} (path : TrunkBranch rows parent g)
              {child : Nat} (hchild : child ∈ rows.getD g []) : TrunkBranch rows parent child := by
            induction path with
            | here k => exact .step hchild (.here child)
            | step hstep _ ih => exact .step hstep (ih hchild)
          exact appendChild hg (List.mem_reverse.mp hc)

private theorem preorder_keeps_prefix (rows : List (List Nat)) (fuel : Nat)
    (pending visited : List Nat) : ∃ rest, childPreorderGo rows fuel pending visited = visited ++ rest := by
  induction fuel generalizing pending visited with
  | zero => exact ⟨[], by simp [childPreorderGo]⟩
  | succ fuel ih =>
    cases hp : pending.getLast? with
    | none => exact ⟨[], by simp [childPreorderGo, hp]⟩
    | some g =>
      rw [childPreorderGo, hp]
      obtain ⟨rest, hrest⟩ := ih (pending.dropLast ++ (rows.getD g []).reverse) (visited ++ [g])
      exact ⟨g :: rest, by simpa only [List.append_assoc, List.singleton_append] using hrest⟩

private theorem allocationWidths {pl : RegionPlacement} {P : Params} {xs shifted : List Int}
    {a : RegionAllocation} (h : allocatePl pl P xs = .ok (a, shifted)) :
    a.widths = reserveWidths pl P := by
  unfold allocatePl at h
  obtain ⟨_, _, hf⟩ := bind_ok h
  exact (congrArg (fun q : RegionAllocation × List Int => q.1.widths) (Except.ok.inj hf)).symm

private theorem group_lefts_inv {pl : RegionPlacement} {P : Params} {widths : List Int}
    {g : Nat} {before after : TrunkAllocationState}
    {I : List Int → Prop} (h : allocateGroup pl P widths g before = .ok after)
    (hi : I before.2.1)
    (hs : ∀ lefts c x, I lefts → c ∈ pl.children.getD g [] → I (setAt lefts c x)) :
    I after.2.1 := by
  rcases before with ⟨xs, lefts, lanes⟩
  unfold allocateGroup at h
  dsimp only at h
  obtain ⟨placed, hplaced, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have hlefts : after.2.1 = placed.2 :=
    (congrArg (fun out : TrunkAllocationState => out.2.1) (Except.ok.inj h)).symm
  rw [hlefts]
  refine foldOkInv (I := fun a : Int × List Int => I a.2) hi ?_ hplaced
  intro a c b ha hc hb
  have he : (a.1 + widths.getD c 0, setAt a.2 c a.1) = b := Except.ok.inj hb
  rw [← he]
  exact hs a.2 c a.1 ha hc

private theorem group_fold_keep_left {pl : RegionPlacement} {P : Params} {widths : List Int}
    {groups : List Nat} {before after : TrunkAllocationState} {target : Nat}
    (h : groups.foldlM (fun a g => allocateGroup pl P widths g a) before = .ok after)
    (haway : ∀ g ∈ groups, target ∉ pl.children.getD g []) :
    after.2.1.getD target 0 = before.2.1.getD target 0 := by
  refine foldOkInv (I := fun q : TrunkAllocationState =>
    q.2.1.getD target 0 = before.2.1.getD target 0) rfl ?_ h
  intro a g b ha hg hb
  refine group_lefts_inv (I := fun lefts => lefts.getD target 0 = before.2.1.getD target 0) hb ha ?_
  intro lefts c x hi hc
  have hno : ¬ (target = c ∧ c < lefts.length) := by
    intro he
    exact haway g hg (he.1.symm ▸ hc)
  rw [setAt_getD, ite_eq_right hno, hi]

private def bucketMember (groups : List Nat) (g : Nat) (q : ProperNode × Nat) : Bool :=
  q.1.node.border == 0 && groups.getD q.2 0 == g

private theorem bucketMember_iff {groups : List Nat} {g : Nat} {q : ProperNode × Nat} :
    bucketMember groups g q ↔ q.1.node.border = 0 ∧ groups.getD q.2 0 = g := by
  simp only [bucketMember, Bool.and_eq_true_iff, beq_iff_eq]

private def gatherMembers (groups : List Nat) (members : List (List Nat))
    (q : ProperNode × Nat) : List (List Nat) :=
  if q.1.node.border != 0 then members else
    let owner := groups.getD q.2 0
    setAt members owner (members.getD owner [] ++ [q.2])

private theorem gatherMembers_lookup (groups : List Nat) (entries : List (ProperNode × Nat))
    (members : List (List Nat)) (g : Nat) :
    (entries.foldl (gatherMembers groups) members).getD g [] = members.getD g [] ++
      (if g < members.length then (entries.filter (bucketMember groups g)).map Prod.snd else []) := by
  induction entries generalizing members with
  | nil => simp
  | cons q rest ih =>
    rw [List.foldl_cons, ih]
    by_cases hp : q.1.node.border = 0
    · have hstep : gatherMembers groups members q =
          setAt members (groups.getD q.2 0) (members.getD (groups.getD q.2 0) [] ++ [q.2]) := by
        unfold gatherMembers
        exact ite_eq_right (fun h => (bne_iff_ne.mp h) hp)
      rw [hstep, setAt_length, setAt_getD]
      by_cases ho : groups.getD q.2 0 = g
      · have hm : bucketMember groups g q := bucketMember_iff.mpr ⟨hp, ho⟩
        rw [ho, List.filter_cons_of_pos hm]
        by_cases hin : g < members.length
        · rw [ite_eq_left ⟨rfl, hin⟩, ite_eq_left hin]
          simp only [ite_eq_left hin, List.map_cons, List.append_assoc, List.singleton_append]
        · rw [ite_eq_right (fun h => hin h.2)]
          simp only [ite_eq_right hin, List.append_nil]
      · have hm : ¬ bucketMember groups g q := fun h => ho (bucketMember_iff.mp h).2
        rw [ite_eq_right (fun he => ho he.1.symm), List.filter_cons_of_neg hm]
    · have hstep : gatherMembers groups members q = members := by
        unfold gatherMembers
        exact ite_eq_left (bne_iff_ne.mpr hp)
      have hm : ¬ bucketMember groups g q := fun h => hp (bucketMember_iff.mp h).1
      rw [hstep, List.filter_cons_of_neg hm]

private theorem bucketMembers (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (groups : List Nat) (labelWidths x : List Int) (g : Nat) :
    (newRegionBuckets rm cg p groups labelWidths x).members.getD g [] =
      if g < rm.clusters.length + 1 then
        (p.nodes.zipIdx.filter (bucketMember groups g)).map Prod.snd else [] := by
  let n := rm.clusters.length + 1
  let empty : RegionBuckets :=
    ⟨List.replicate n [], List.replicate n 0, List.replicate n 2147483647,
      List.replicate n (-2147483648), List.replicate n [], List.replicate n 0,
      List.replicate n 0⟩
  let gather (acc : RegionBuckets) (q : ProperNode × Nat) : RegionBuckets :=
    if q.1.node.border != 0 then acc else
      let owner := groups.getD q.2 0
      let width := q.1.node.w + 2 * (q.1.node.loopExtent : Int)
      let left := RouteImpl.xAt x q.2 - Int.tdiv width 2
      let right := left + width
      { acc with
        low := setAt acc.low owner (min (acc.low.getD owner 2147483647) left)
        high := setAt acc.high owner (max (acc.high.getD owner (-2147483648)) right)
        members := setAt acc.members owner (acc.members.getD owner [] ++ [q.2]) }
  let addLane (acc : RegionBuckets) (q : Edge × Nat) : RegionBuckets :=
    if !q.1.reversed || q.1.tail == q.1.head then acc else
      let root := rm.clusters.length
      let owner := edgeOwnerOf rm groups root q.1.tail q.1.head
      if owner == root then acc else
        { acc with
          lanes := setAt acc.lanes owner (acc.lanes.getD owner [] ++ [q.2])
          laneWidth := setAt acc.laneWidth owner
            (max (acc.laneWidth.getD owner 0) (labelWidths.getD q.2 0)) }
  change ((cg.edges.zipIdx.foldl addLane (p.nodes.zipIdx.foldl gather empty)).members).getD g [] = _
  have laneMembers (entries : List (Edge × Nat)) (acc : RegionBuckets) :
      (entries.foldl addLane acc).members = acc.members := by
    induction entries generalizing acc with
    | nil => rfl
    | cons q rest ih =>
      rw [List.foldl_cons, ih]
      dsimp only [addLane]
      split
      · rfl
      · split <;> rfl
  have gatheredMembers (entries : List (ProperNode × Nat)) (acc : RegionBuckets) :
      (entries.foldl gather acc).members = entries.foldl (gatherMembers groups) acc.members := by
    induction entries generalizing acc with
    | nil => rfl
    | cons q rest ih =>
      rw [List.foldl_cons, List.foldl_cons, ih]
      have he : (gather acc q).members = gatherMembers groups acc.members q := by
        dsimp only [gather, gatherMembers]
        split <;> rfl
      rw [he]
  rw [laneMembers, gatheredMembers, gatherMembers_lookup]
  have hnil : (List.replicate n ([] : List Nat)).getD g [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  simp only [empty, hnil, List.length_replicate, List.nil_append, n]

private theorem bucketCount (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (groups : List Nat) (labelWidths x : List Int) (g v : Nat) {n : ProperNode}
    (hn : p.nodes[v]? = some n) (hplain : n.node.border = 0) :
    ((newRegionBuckets rm cg p groups labelWidths x).members.getD g []).count v =
      if g < rm.clusters.length + 1 ∧ groups.getD v 0 = g then 1 else 0 := by
  rw [bucketMembers]
  by_cases hg : g < rm.clusters.length + 1
  · rw [ite_eq_left hg]
    have hmem : v ∈ (p.nodes.zipIdx.filter (bucketMember groups g)).map Prod.snd ↔
        groups.getD v 0 = g := by
      constructor
      · intro h
        obtain ⟨⟨m, k⟩, hq, rfl⟩ := List.mem_map.mp h
        exact (bucketMember_iff.mp (List.mem_filter.mp hq).2).2
      · intro h
        exact List.mem_map.mpr ⟨(n, v), List.mem_filter.mpr
          ⟨List.mem_zipIdx_iff_getElem?.mpr hn, bucketMember_iff.mpr ⟨hplain, h⟩⟩, rfl⟩
    by_cases ho : groups.getD v 0 = g
    · rw [ite_eq_left ⟨hg, ho⟩]
      have hnd : (p.nodes.zipIdx.map Prod.snd).Nodup := by
        rw [List.zipIdx_map_snd]
        exact List.nodup_range'
      have hsub := (List.filter_sublist (p := bucketMember groups g) (l := p.nodes.zipIdx)).map
        Prod.snd
      exact (hsub.nodup hnd).count_of_mem (hmem.mpr ho)
    · rw [ite_eq_right (fun h => ho h.2)]
      exact List.count_eq_zero_of_not_mem (fun h => ho (hmem.mp h))
  · simp [hg]

private theorem group_centers {pl : RegionPlacement} {P : Params} {widths : List Int}
    {g : Nat} {before after : TrunkAllocationState}
    (h : allocateGroup pl P widths g before = .ok after) :
    after.1 = (pl.buckets.members.getD g []).foldl
      (fun xs v => setAt xs v (xs.getD v 0 + regionBucketShift pl before.2.1 g)) before.1 := by
  rcases before with ⟨xs, lefts, lanes⟩
  unfold allocateGroup at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have hx := (congrArg Prod.fst (Except.ok.inj h)).symm
  let members := pl.buckets.members.getD g []
  let step (x : List Int) (v : Nat) := setAt x v (x.getD v 0 + regionBucketShift pl lefts g)
  change after.1 = (if members.isEmpty then xs else members.foldl step xs) at hx
  change after.1 = members.foldl step xs
  by_cases hm : members.isEmpty
  · rw [ite_eq_left hm] at hx
    rwa [List.nil_of_isEmpty hm, List.foldl_nil]
  · rwa [ite_eq_right hm] at hx

private theorem shiftMembers (members : List Nat) (xs : List Int) (shift : Int)
    (v : Nat) :
    let placed := members.foldl (fun x i => setAt x i (x.getD i 0 + shift)) xs
    placed.length = xs.length ∧ (v < xs.length → placed.getD v 0 =
      xs.getD v 0 + (members.count v : Int) * shift) := by
  dsimp only
  induction members generalizing xs with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons]
    have hh := ih (setAt xs i (xs.getD i 0 + shift))
    rw [setAt_length] at hh
    refine ⟨hh.1, ?_⟩
    intro hv
    rw [hh.2 hv, setAt_getD]
    by_cases he : i = v
    · subst i
      rw [ite_eq_left ⟨rfl, hv⟩, List.count_cons_self, Int.natCast_add, Int.add_mul]
      simp only [Int.natCast_one, Int.one_mul]
      omega
    · rw [ite_eq_right (fun h => he h.1.symm), List.count_cons_of_ne he]

private theorem fold_keep_center {pl : RegionPlacement} {P : Params} {widths : List Int}
    {groups : List Nat} {before after : TrunkAllocationState} {v : Nat}
    (h : groups.foldlM (fun a g => allocateGroup pl P widths g a) before = .ok after)
    (hv : v < before.1.length)
    (haway : ∀ g ∈ groups, (pl.buckets.members.getD g []).count v = 0) :
    after.1.length = before.1.length ∧ after.1.getD v 0 = before.1.getD v 0 := by
  refine foldOkInv (I := fun q : TrunkAllocationState =>
    q.1.length = before.1.length ∧ q.1.getD v 0 = before.1.getD v 0) ⟨rfl, rfl⟩ ?_ h
  intro a g out ha hg ht
  rw [group_centers ht]
  have hs := shiftMembers (pl.buckets.members.getD g []) a.1 (regionBucketShift pl a.2.1 g) v
  exact ⟨hs.1.trans ha.1, by
    rw [hs.2 (ha.1.symm ▸ hv), haway g hg, Int.natCast_zero, Int.zero_mul, Int.add_zero, ha.2]⟩

section Stages

variable {P : Params} {rm : ComponentRegions} {cg : Graph} {labels : List MeasuredLabel}
  {p placed : Proper} {minimum : RegionConstraints} {layers pinned : List (List Nat)}
  {xs : List Int} {reserved : List (Option Int)}
  (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)

private theorem actualChildParents (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) : ChildParents rm stages.placement.children := by
  rw [stages.hPlacement]
  exact regionChildren_parents hparents hmin stages.hChildren

private theorem actualPreorder (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) :
    PreorderFrontier rm stages.placement.children stages.placement.order [] := by
  have hi : PreorderFrontier rm stages.children [] [rm.clusters.length] :=
    ⟨by simp, fun c hc => Or.inl (by simpa using hc), by simp,
      fun c hc => (List.not_mem_nil hc).elim, fun c hc => by
        have he : c = rm.clusters.length := by simpa using hc
        rw [he]
        exact .here _⟩
  have hc := actualChildParents stages hparents hmin
  have hn := (stages.reservation_order hparents hmin).1
  rw [stages.hPlacement] at hc hn ⊢
  exact preorder_frontier hc hn _ hi

private theorem actualOrder_mem (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) {g : Nat} (hg : g ≤ rm.clusters.length) :
    g ∈ stages.placement.order := by
  rcases Nat.lt_or_eq_of_le hg with hg | rfl
  · obtain ⟨pre, post, hsplit, _, _⟩ := (stages.reservation_order hparents hmin).2 g (Nat.le_of_lt hg)
    exact List.mem_reverse.mp (List.mem_iff_append.mpr ⟨pre, post, hsplit⟩)
  · rw [stages.hPlacement]
    change rm.clusters.length ∈ childPreorderGo stages.children (stages.children.length + 1)
      [rm.clusters.length] []
    simp only [childPreorderGo, List.getLast?_singleton, List.dropLast_singleton, List.nil_append]
    obtain ⟨post, hp⟩ := preorder_keeps_prefix stages.children stages.children.length
      (stages.children.getD rm.clusters.length []).reverse [rm.clusters.length]
    rw [hp]
    exact List.mem_append_left _ List.mem_cons_self

/-- The actual preorder visits each bounded group once and its left coordinate is already final
when visited. The synthetic root is included, although it never allocates a reserved lane. -/
theorem actualGroupVisit (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) {g : Nat} (hg : g ≤ rm.clusters.length) :
    ∃ pre post : List Nat, ∃ before after final : TrunkAllocationState,
      stages.placement.order = pre ++ g :: post ∧ g ∉ pre ∧ g ∉ post ∧
      pre.foldlM (fun a k => allocateGroup stages.placement P (reserveWidths stages.placement P) k a)
        (stages.before, List.replicate (stages.placement.rm.clusters.length + 1) 0,
          List.replicate stages.placement.p.chains.length none) = .ok before ∧
      allocateGroup stages.placement P (reserveWidths stages.placement P) g before = .ok after ∧
      post.foldlM (fun a k => allocateGroup stages.placement P (reserveWidths stages.placement P) k a)
        after = .ok final ∧
      final.1 = stages.shifted ∧ final.2.1 = stages.allocation.lefts ∧
      before.2.1.length = rm.clusters.length + 1 ∧
      before.2.1.getD g 0 = stages.allocation.lefts.getD g 0 := by
  have hmem := actualOrder_mem stages hparents hmin hg
  have hwalk := actualPreorder stages hparents hmin
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hmem
  have huni : (pre ++ g :: post).Nodup := by
    rw [← hsplit]
    simpa only [List.append_nil] using hwalk.unique
  have hnpre : g ∉ pre := fun hm => (List.nodup_append.mp huni).2.2 g hm g List.mem_cons_self rfl
  have hnpost := (List.nodup_cons.mp (List.nodup_append.mp huni).2.1).1
  have haway : ∀ k ∈ g :: post, g ∉ stages.placement.children.getD k [] := by
    have ho := hwalk.ordered
    rw [hsplit] at ho
    intro k hk
    rcases List.mem_cons.mp hk with hk | hk
    · rw [hk]
      exact hwalk.noSelf g hmem
    · exact (List.pairwise_cons.mp (List.pairwise_append.mp ho).2.1).1 k hk
  let init : TrunkAllocationState := (stages.before,
    List.replicate (stages.placement.rm.clusters.length + 1) 0,
    List.replicate stages.placement.p.chains.length none)
  let step (a : TrunkAllocationState) (k : Nat) :=
    allocateGroup stages.placement P (reserveWidths stages.placement P) k a
  have h := stages.hAllocation
  unfold allocatePl at h
  obtain ⟨final, hfold, hf⟩ := bind_ok h
  change stages.placement.order.foldlM step init = .ok final at hfold
  have hx : final.1 = stages.shifted := congrArg Prod.snd (Except.ok.inj hf)
  have hl : final.2.1 = stages.allocation.lefts :=
    congrArg (fun q : RegionAllocation × List Int => q.1.lefts) (Except.ok.inj hf)
  rw [hsplit, List.foldlM_append] at hfold
  obtain ⟨before, hpre, htail⟩ := bind_ok hfold
  have htail' := htail
  rw [List.foldlM_cons] at htail'
  obtain ⟨after, hvisit, hpost⟩ := bind_ok htail'
  have hlen : before.2.1.length = rm.clusters.length + 1 := by
    refine foldOkInv (I := fun q : TrunkAllocationState => q.2.1.length = rm.clusters.length + 1)
      ?_ ?_ hpre
    · dsimp only [init]
      rw [List.length_replicate, stages.hPlacement]
    · intro a k b ha _ hb
      exact group_lefts_inv (I := fun lefts => lefts.length = rm.clusters.length + 1)
        hb ha (fun l c x hh _ => (setAt_length l c x).trans hh)
  have hstable := group_fold_keep_left htail haway
  exact ⟨pre, post, before, after, final, hsplit, hnpre, hnpost, hpre, hvisit, hpost, hx, hl,
    hlen, (by rw [← hl]; exact hstable.symm)⟩

/-- The actual direct-child origin, also at the synthetic root. -/
theorem actualChildLeft (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum)
    {g c i : Nat} (hg : g ≤ rm.clusters.length)
    (hc : (stages.placement.children.getD g [])[i]? = some c) :
    stages.allocation.lefts.getD c 0 = stages.allocation.lefts.getD g 0 +
      (if g = rm.clusters.length then 0 else regionInsetOf P) +
      stages.placement.buckets.widths.getD g 0 +
      (((stages.placement.children.getD g []).take i).map fun k =>
        stages.allocation.widths.getD k 0).sum := by
  obtain ⟨_, post, before, after, _, _, _, hnpost, _, hv, hpost, _, hf, hlen, hstable⟩ :=
    actualGroupVisit stages hparents hmin hg
  have hrows := actualChildParents stages hparents hmin
  obtain ⟨hcb, hcp⟩ := hrows g c (List.mem_of_getElem? hc)
  have haway : ∀ k ∈ post, c ∉ stages.placement.children.getD k [] := by
    intro k hk hc'
    have hkg := (hrows k c hc').2.symm.trans hcp
    exact hnpost (hkg ▸ hk)
  have hkeep := group_fold_keep_left hpost haway
  have hout := allocateGroup_child_left hv ((stages.reservation_order hparents hmin).1 g)
    hc (by rw [hlen]; omega)
  rw [hf] at hkeep
  have hroot : stages.placement.rm.clusters.length = rm.clusters.length := by rw [stages.hPlacement]
  have hw := allocationWidths stages.hAllocation
  rw [hkeep, hout, hstable, hroot, hw]
  by_cases h : g = rm.clusters.length
  · simp [h]
  · have ht : g < rm.clusters.length := by omega
    have hinset : stages.placement.minimum.origins.getD g 0 = regionInsetOf P := by
      rw [stages.hPlacement]
      change minimum.origins.getD g 0 = regionInsetOf P
      rw [constrainR_origins hmin, hparents, List.getD_eq_getElem?_getD,
        List.getElem?_replicate_of_lt ht, Option.getD_some]
    have hcond : (g != rm.clusters.length) = true := bne_iff_ne.mpr h
    rw [ite_eq_left hcond, ite_eq_right h, hinset]

theorem allocationWidths_exact : stages.allocation.widths = reserveWidths stages.placement P :=
  allocationWidths stages.hAllocation

theorem actualChild_bound (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) {g c : Nat}
    (hc : c ∈ stages.placement.children.getD g []) : c < rm.clusters.length :=
  (actualChildParents stages hparents hmin g c hc).1

theorem actualBranch_from_root (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) {g : Nat} (hg : g ≤ rm.clusters.length) :
    TrunkBranch stages.placement.children rm.clusters.length g := by
  exact (actualPreorder stages hparents hmin).reachable g
    (List.mem_append_left _ (actualOrder_mem stages hparents hmin hg))

theorem actualMember_group_bound {v : Nat} {n : ProperNode}
    (hn : p.nodes[v]? = some n) : stages.groups.getD v 0 ≤ rm.clusters.length := by
  let owner (q : ProperNode × Nat) : Except LayoutError Nat :=
    match q.1.node.clusterPath.getLast? with
    | none => pure rm.clusters.length
    | some decl =>
      match clusterOfDecl rm decl with
      | some k => pure k
      | none => throw .domain
  have hm : p.nodes.zipIdx.mapM owner = .ok stages.groups := stages.hGroups
  have hz : p.nodes.zipIdx[v]? = some (n, v) := by
    simp only [List.getElem?_zipIdx, hn, Option.map_some, Nat.zero_add]
  obtain ⟨g, hg, hlookup⟩ := (mapM_getElem? owner _ _ hm).2 _ _ hz
  rw [List.getD_eq_getElem?_getD, hlookup, Option.getD_some]
  unfold owner at hg
  dsimp only at hg
  split at hg
  · exact Nat.le_of_eq (Except.ok.inj hg).symm
  · split at hg
    · rename_i k hk
      have he : k = g := Except.ok.inj hg
      subst g
      unfold clusterOfDecl at hk
      exact Nat.le_of_lt (List.findIdx?_eq_some_iff_getElem.mp hk).1
    · cases hg

/-- A plain node gets exactly its bucket's translation based on the final left table.
All other allocation visits leave the index alone. -/
theorem actualMember_shift (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum)
    {v g : Nat} {n : ProperNode} (hn : p.nodes[v]? = some n) (hplain : n.node.border = 0)
    (hg : stages.groups.getD v 0 = g) :
    v ∈ stages.placement.buckets.members.getD g [] ∧
    stages.shifted.getD v 0 = stages.before.getD v 0 +
      regionBucketShift stages.placement stages.allocation.lefts g := by
  have hgb : g ≤ rm.clusters.length := by rw [← hg]; exact actualMember_group_bound stages hn
  have hv : v < stages.before.length := by
    rw [CoordsImpl.crossCoordsClusterWith_length stages.hCross]
    exact (List.getElem?_eq_some_iff.mp hn).1
  have hcounts (k : Nat) : (stages.placement.buckets.members.getD k []).count v =
      if k = g then 1 else 0 := by
    rw [stages.hPlacement]
    have h := bucketCount rm cg p stages.groups
      (cg.edges.map fun e => (stackSize cg.slot (routeLabels labels e.decl)).width)
      stages.before k v hn hplain
    rw [hg] at h
    by_cases hkg : k = g
    · subst k
      rw [ite_eq_left ⟨Nat.lt_succ_of_le hgb, rfl⟩] at h
      rwa [ite_eq_left (show g = g from rfl)]
    · rw [ite_eq_right hkg]
      exact h.trans (ite_eq_right (fun he => hkg he.2.symm))
  have hcount : (stages.placement.buckets.members.getD g []).count v = 1 := by
    exact (hcounts g).trans (ite_eq_left (show g = g from rfl))
  have hmember : v ∈ stages.placement.buckets.members.getD g [] := by
    apply List.count_pos_iff.mp
    exact hcount.symm ▸ Nat.zero_lt_one
  obtain ⟨pre, post, before, after, final, _, hpreNot, hpostNot, hpre, hgStep, hpost,
    hfinal, _, _, hleft⟩ := actualGroupVisit stages hparents hmin hgb
  have hstable (ks : List Nat) (hnot : g ∉ ks) :
      ∀ k ∈ ks, (stages.placement.buckets.members.getD k []).count v = 0 := by
    intro k hk
    have hne : k ≠ g := by
      intro he
      exact hnot (he ▸ hk)
    rw [hcounts, ite_eq_right hne]
  have hprefix := fold_keep_center hpre hv (hstable pre hpreNot)
  have hvBefore : v < before.1.length := by
    rw [hprefix.1]
    exact hv
  have hstep := shiftMembers (stages.placement.buckets.members.getD g []) before.1
    (regionBucketShift stages.placement before.2.1 g) v
  dsimp only at hstep
  rw [← group_centers hgStep] at hstep
  have hvAfter : v < after.1.length := by rw [hstep.1]; exact hvBefore
  have hsuffix := fold_keep_center hpost hvAfter (hstable post hpostNot)
  refine ⟨hmember, ?_⟩
  rw [← hfinal, hsuffix.2, hstep.2 hvBefore, hcount, Int.natCast_one, Int.one_mul, hprefix.2]
  simp only [regionBucketShift, hleft]

theorem actualGroup_inset (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) {g : Nat} (hg : g < rm.clusters.length) :
    stages.placement.minimum.origins.getD g 0 = regionInsetOf P := by
  rw [stages.hPlacement]
  change minimum.origins.getD g 0 = regionInsetOf P
  rw [constrainR_origins hmin, hparents, List.getD_eq_getElem?_getD,
    List.getElem?_replicate_of_lt hg, Option.getD_some]

end Stages

end Elegant.Layered.PipelineImpl.RegionOrdinaryC6

import Elegant.Layered.RegionSharedAllocation

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem laneBindOk {α β : Type} {a : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : a.bind f = .ok b) :
    ∃ x, a = .ok x ∧ f x = .ok b := by
  cases a with
  | error e => cases h
  | ok x => exact ⟨x, rfl, h⟩

private theorem laneSetAt_length {α : Type} (xs : List α) (i : Nat) (x : α) :
    (setAt xs i x).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons a as ih => cases i <;> simp [setAt, ih]

private theorem laneSetAt_getD {α : Type} (xs : List α) (i j : Nat) (x d : α) :
    (setAt xs i x).getD j d = if j = i ∧ i < xs.length then x else xs.getD j d := by
  induction xs generalizing i j with
  | nil => simp [setAt]
  | cons a as ih =>
    cases i with
    | zero => cases j <;> simp [setAt]
    | succ i =>
      cases j with
      | zero => simp [setAt]
      | succ j => simpa [setAt, List.getD_cons_succ] using ih i j

private def addLaneEntry (rm : ComponentRegions) (groups : List Nat) (labelWidths : List Int)
    (b : RegionBuckets) (q : Edge × Nat) : RegionBuckets :=
  if !q.1.reversed || q.1.tail == q.1.head then b else
    let root := rm.clusters.length
    let owner := edgeOwnerOf rm groups root q.1.tail q.1.head
    if owner == root then b else
      { b with
        lanes := setAt b.lanes owner (b.lanes.getD owner [] ++ [q.2])
        laneWidth := setAt b.laneWidth owner
          (max (b.laneWidth.getD owner 0) (labelWidths.getD q.2 0)) }

private def selectsLane (rm : ComponentRegions) (groups : List Nat) (group : Nat)
    (q : Edge × Nat) : Bool :=
  let owner := edgeOwnerOf rm groups rm.clusters.length q.1.tail q.1.head
  if !q.1.reversed || q.1.tail == q.1.head then false else
    if owner == rm.clusters.length then false else
      decide (group = owner ∧ owner < rm.clusters.length + 1)

private theorem addLaneEntries_exact (rm : ComponentRegions) (groups : List Nat)
    (labelWidths : List Int) (group : Nat) (entries : List (Edge × Nat))
    (b : RegionBuckets) (hlen : b.lanes.length = rm.clusters.length + 1) :
    ((entries.foldl (addLaneEntry rm groups labelWidths) b).lanes.getD group []) =
      b.lanes.getD group [] ++ ((entries.filter (selectsLane rm groups group)).map Prod.snd) := by
  induction entries generalizing b with
  | nil => simp
  | cons q qs ih =>
    let owner := edgeOwnerOf rm groups rm.clusters.length q.1.tail q.1.head
    cases hskip : (!q.1.reversed || q.1.tail == q.1.head) with
    | true =>
      have hstep : addLaneEntry rm groups labelWidths b q = b := by
        unfold addLaneEntry
        rw [ite_eq_left hskip]
      have hsel : ¬ selectsLane rm groups group q := by
        unfold selectsLane
        rw [ite_eq_left hskip]
        exact Bool.false_ne_true
      rw [List.foldl_cons, hstep, List.filter_cons_of_neg hsel]
      exact ih b hlen
    | false =>
      have hnoskip : ¬ ((!q.1.reversed || q.1.tail == q.1.head) = true) :=
        fun h => Bool.false_ne_true (hskip.symm.trans h)
      by_cases hroot : owner = rm.clusters.length
      · have he : (owner == rm.clusters.length) = true := beq_iff_eq.mpr hroot
        have hstep : addLaneEntry rm groups labelWidths b q = b := by
          dsimp only [addLaneEntry]
          rw [ite_eq_right hnoskip, ite_eq_left he]
        have hsel : ¬ selectsLane rm groups group q := by
          dsimp only [selectsLane]
          rw [ite_eq_right hnoskip, ite_eq_left he]
          exact Bool.false_ne_true
        rw [List.foldl_cons, hstep, List.filter_cons_of_neg hsel]
        exact ih b hlen
      · let next : RegionBuckets := { b with
          lanes := setAt b.lanes owner (b.lanes.getD owner [] ++ [q.2])
          laneWidth := setAt b.laneWidth owner
            (max (b.laneWidth.getD owner 0) (labelWidths.getD q.2 0)) }
        have hnroot : ¬ ((owner == rm.clusters.length) = true) :=
          fun h => hroot (beq_iff_eq.mp h)
        have hstep : addLaneEntry rm groups labelWidths b q = next := by
          dsimp only [addLaneEntry]
          rw [ite_eq_right hnoskip, ite_eq_right hnroot]
        have hsel : selectsLane rm groups group q =
            decide (group = owner ∧ owner < rm.clusters.length + 1) := by
          dsimp only [selectsLane]
          rw [ite_eq_right hnoskip, ite_eq_right hnroot]
        have hn : next.lanes.length = rm.clusters.length + 1 :=
          (laneSetAt_length _ _ _).trans hlen
        rw [List.foldl_cons, hstep, ih next hn]
        change (setAt b.lanes owner (b.lanes.getD owner [] ++ [q.2])).getD group [] ++ _ = _
        rw [laneSetAt_getD, hlen]
        by_cases hw : group = owner ∧ owner < rm.clusters.length + 1
        · have hs : selectsLane rm groups group q := hsel.trans (decide_eq_true hw)
          rw [ite_eq_left hw, List.filter_cons_of_pos hs, hw.1,
            List.append_assoc, List.singleton_append, List.map_cons]
        · have hs : ¬ selectsLane rm groups group q := fun h =>
            hw (of_decide_eq_true (hsel.symm.trans h))
          rw [ite_eq_right hw, List.filter_cons_of_neg hs]

private theorem regionBuckets_lanes_exact (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (groups : List Nat) (labelWidths x : List Int) (group : Nat) :
    (newRegionBuckets rm cg p groups labelWidths x).lanes.getD group [] =
      ((cg.edges.zipIdx.filter (selectsLane rm groups group)).map Prod.snd) := by
  let n := rm.clusters.length + 1
  let empty : RegionBuckets :=
    { members := List.replicate n [], widths := List.replicate n 0,
      low := List.replicate n 2147483647, high := List.replicate n (-2147483648),
      lanes := List.replicate n [], laneWidth := List.replicate n 0,
      loopWidth := List.replicate n 0 }
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
  let b := p.nodes.zipIdx.foldl gather empty
  have hg : b.lanes = List.replicate n ([] : List Nat) := by
    apply OrderImpl.foldl_inv (fun acc : RegionBuckets => acc.lanes = List.replicate n [])
    · rfl
    · intro acc ha q _
      dsimp only [gather]
      split <;> exact ha
  have hlen : b.lanes.length = n := by rw [hg, List.length_replicate]
  unfold newRegionBuckets
  change (cg.edges.zipIdx.foldl (addLaneEntry rm groups labelWidths) b).lanes.getD group [] = _
  rw [addLaneEntries_exact _ _ _ _ _ _ hlen, hg, List.getD_eq_getElem?_getD,
    List.getElem?_replicate]
  split <;> rfl

private theorem selectedBucket_mem {rm : ComponentRegions} {cg : Graph} {groups : List Nat}
    {group edge : Nat} {e : Edge} (hedge : cg.edges[edge]? = some e) :
    edge ∈ ((cg.edges.zipIdx.filter (selectsLane rm groups group)).map Prod.snd) ↔
      selectsLane rm groups group (e, edge) = true := by
  constructor
  · intro hm
    obtain ⟨⟨e', i⟩, hq, hi⟩ := List.mem_map.mp hm
    change i = edge at hi
    subst i
    obtain ⟨hzip, hsel⟩ := List.mem_filter.mp hq
    have he' : e' = e := Option.some.inj ((List.mem_zipIdx_iff_getElem?.mp hzip).symm.trans hedge)
    subst e'
    exact hsel
  · intro hsel
    exact List.mem_map.mpr ⟨(e, edge),
      List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr hedge, hsel⟩, rfl⟩

private abbrev LaneCursor := List (Option Int) × Int
private abbrev LaneAllocationState := List Int × List Int × List (Option Int)

private def laneWrite (slot laneWidth : Int) (state : LaneCursor) (edge : Nat) :
    Except LayoutError LaneCursor :=
  let atX := state.2 + slot
  if I32_MAX < atX then .error .overflow else
    .ok (setAt state.1 edge (some atX), atX + slot + laneWidth)

private theorem laneWrites_preserve (slot laneWidth : Int) (edges : List Nat) {edge : Nat}
    {start finish : LaneCursor} (h : edges.foldlM (laneWrite slot laneWidth) start = .ok finish) :
    finish.1.length = start.1.length ∧
      (edge ∉ edges → finish.1.getD edge none = start.1.getD edge none) := by
  induction edges generalizing start with
  | nil =>
    change Except.ok start = Except.ok finish at h
    cases h
    exact ⟨rfl, fun _ => rfl⟩
  | cons i is ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hstep, htail⟩ := laneBindOk h
    dsimp only [laneWrite] at hstep
    split at hstep
    · cases hstep
    · rw [← Except.ok.inj hstep] at htail
      obtain ⟨hlen, hkeep⟩ := ih htail
      refine ⟨hlen.trans (laneSetAt_length _ _ _), ?_⟩
      intro hn
      rw [hkeep (fun hm => hn (List.mem_cons_of_mem _ hm))]
      change (setAt start.1 i (some (start.2 + slot))).getD edge none = _
      rw [laneSetAt_getD, ite_eq_right (fun he => hn (List.mem_cons.mpr (Or.inl he.1)))]

private theorem laneWrites_at (slot laneWidth : Int) (edges : List Nat) {edge j : Nat}
    {start finish : LaneCursor} (h : edges.foldlM (laneWrite slot laneWidth) start = .ok finish)
    (hnodup : edges.Nodup) (hedge : edges[j]? = some edge) (hbound : edge < start.1.length) :
    finish.1.getD edge none = some (start.2 + slot + (j : Int) * (2 * slot + laneWidth)) := by
  induction edges generalizing start j with
  | nil => simp at hedge
  | cons i is ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hstep, htail⟩ := laneBindOk h
    dsimp only [laneWrite] at hstep
    split at hstep
    · cases hstep
    · have hmid : (setAt start.1 i (some (start.2 + slot)), start.2 + slot + slot + laneWidth) = mid :=
        Except.ok.inj hstep
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hnodup
      cases j with
      | zero =>
        have he : i = edge := Option.some.inj hedge
        subst i
        rw [(laneWrites_preserve slot laneWidth is (edge := edge) htail).2 hnot, ← hmid]
        change (setAt start.1 edge (some (start.2 + slot))).getD edge none = _
        rewrite [laneSetAt_getD, ite_eq_left ⟨rfl, hbound⟩]
        simp
      | succ j =>
        have hb : edge < mid.1.length := by
          rw [← hmid]
          change edge < (setAt start.1 i (some (start.2 + slot))).length
          rwa [laneSetAt_length]
        have hj : is[j]? = some edge := hedge
        rw [ih (j := j) htail hnodup hj hb]
        apply congrArg some
        rw [← hmid]
        change start.2 + slot + slot + laneWidth + slot + (j : Int) * (2 * slot + laneWidth) = _
        rw [Int.natCast_succ, Int.add_mul, Int.one_mul]
        omega

private def laneChildWrite (widths : List Int) (state : Int × List Int) (child : Nat) :
    Except LayoutError (Int × List Int) :=
  .ok (state.1 + widths.getD child 0, setAt state.2 child state.1)

private def laneStart (pl : RegionPlacement) (P : Params) (widths : List Int) (g : Nat)
    (placed : Int × List Int) : Int :=
  if g != pl.rm.clusters.length && !(pl.buckets.lanes.getD g []).isEmpty then
    placed.2.getD g 0 + widths.getD g 0 - pl.buckets.loopWidth.getD g 0 -
      regionInsetOf P - laneExtentOf pl.buckets P.slot g
  else placed.1

private theorem allocationLanePhase {pl : RegionPlacement} {P : Params} {widths : List Int}
    {g : Nat} {initial final : LaneAllocationState}
    (h : allocateGroup pl P widths g initial = .ok final) :
    ∃ (placed : Int × List Int) (finish : LaneCursor),
      (pl.children.getD g []).foldlM (laneChildWrite widths)
        (initial.2.1.getD g 0 +
          (if g != pl.rm.clusters.length then pl.minimum.origins.getD g 0 else 0) +
          pl.buckets.widths.getD g 0, initial.2.1) = .ok placed ∧
      (pl.buckets.lanes.getD g []).foldlM (laneWrite P.slot (pl.buckets.laneWidth.getD g 0))
        (initial.2.2, laneStart pl P widths g placed) = .ok finish ∧
      final.2.1 = placed.2 ∧ final.2.2 = finish.1 := by
  rcases initial with ⟨xs, lefts, lanes⟩
  unfold allocateGroup at h
  dsimp only at h
  obtain ⟨placed, hp, h⟩ := laneBindOk h
  obtain ⟨finish, hf, h⟩ := laneBindOk h
  have hout := Except.ok.inj h
  exact ⟨placed, finish, hp, hf, (congrArg (fun s : LaneAllocationState => s.2.1) hout).symm,
    (congrArg (fun s : LaneAllocationState => s.2.2) hout).symm⟩

private theorem childWrites_keep (widths : List Int) (children : List Nat) {owner : Nat}
    {initial final : Int × List Int}
    (h : children.foldlM (laneChildWrite widths) initial = .ok final) (hnot : owner ∉ children) :
    final.2.getD owner 0 = initial.2.getD owner 0 := by
  induction children generalizing initial with
  | nil =>
    change Except.ok initial = Except.ok final at h
    rw [← Except.ok.inj h]
  | cons child rest ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hstep, htail⟩ := laneBindOk h
    rw [ih htail (fun hm => hnot (List.mem_cons_of_mem _ hm))]
    have hmid : (initial.1 + widths.getD child 0, setAt initial.2 child initial.1) = mid :=
      Except.ok.inj hstep
    rw [← hmid]
    change (setAt initial.2 child initial.1).getD owner 0 = _
    rw [laneSetAt_getD, ite_eq_right (fun he => hnot (List.mem_cons.mpr (Or.inl he.1)))]

private theorem allocationVisits_preserve {pl : RegionPlacement} {P : Params} {widths : List Int}
    (visits : List Nat) {owner edge : Nat} {initial final : LaneAllocationState}
    (h : visits.foldlM (fun state g => allocateGroup pl P widths g state) initial = .ok final) :
    final.2.2.length = initial.2.2.length ∧
      ((∀ g ∈ visits, owner ∉ pl.children.getD g []) →
        final.2.1.getD owner 0 = initial.2.1.getD owner 0) ∧
      ((∀ g ∈ visits, edge ∉ pl.buckets.lanes.getD g []) →
        final.2.2.getD edge none = initial.2.2.getD edge none) := by
  induction visits generalizing initial with
  | nil =>
    change Except.ok initial = Except.ok final at h
    cases h
    exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  | cons g gs ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hstep, htail⟩ := laneBindOk h
    obtain ⟨placed, finish, hp, hf, hleft, hlanes⟩ := allocationLanePhase hstep
    obtain ⟨hlen, hleftKeep, hlaneKeep⟩ := ih htail
    have hwrite := laneWrites_preserve _ _ _ (edge := edge) hf
    have hstepLen : mid.2.2.length = initial.2.2.length := by
      rw [hlanes]
      exact hwrite.1
    refine ⟨hlen.trans hstepLen, ?_, ?_⟩
    · intro hn
      rw [hleftKeep (fun a ha => hn a (List.mem_cons_of_mem _ ha)), hleft]
      exact childWrites_keep widths _ hp (hn g (by simp))
    · intro hn
      rw [hlaneKeep (fun a ha => hn a (List.mem_cons_of_mem _ ha)), hlanes]
      exact hwrite.2 (hn g (by simp))

private theorem allocation_lane_at {pl : RegionPlacement} {P : Params}
    {xs shifted : List Int} {a : RegionAllocation} (h : allocatePl pl P xs = .ok (a, shifted))
    {owner edge j : Nat} {pre post : List Nat} (horder : pl.order = pre ++ owner :: post)
    (howner : owner < pl.rm.clusters.length) (hbound : edge < pl.p.chains.length)
    (hrow : (pl.buckets.lanes.getD owner []).Nodup)
    (hentry : (pl.buckets.lanes.getD owner [])[j]? = some edge)
    (hlefts : ∀ g ∈ post, owner ∉ pl.children.getD g [])
    (hlanes : ∀ g ∈ post, edge ∉ pl.buckets.lanes.getD g []) :
    a.lanes.getD edge none = some (a.lefts.getD owner 0 +
      (reserveWidths pl P).getD owner 0 - pl.buckets.loopWidth.getD owner 0 -
      regionInsetOf P - laneExtentOf pl.buckets P.slot owner + P.slot +
      (j : Int) * (2 * P.slot + pl.buckets.laneWidth.getD owner 0)) := by
  let start : LaneAllocationState := (xs, List.replicate (pl.rm.clusters.length + 1) 0,
    List.replicate pl.p.chains.length none)
  unfold allocatePl at h
  obtain ⟨finish, hall, h⟩ := laneBindOk h
  have htable : a.lanes = finish.2.2 :=
    (congrArg (fun q : RegionAllocation × List Int => q.1.lanes) (Except.ok.inj h)).symm
  have hfleft : a.lefts = finish.2.1 :=
    (congrArg (fun q : RegionAllocation × List Int => q.1.lefts) (Except.ok.inj h)).symm
  change pl.order.foldlM (fun state g => allocateGroup pl P (reserveWidths pl P) g state)
    start = .ok finish at hall
  rw [horder, List.foldlM_append] at hall
  obtain ⟨beforeVisit, hprefix, hrest⟩ := laneBindOk hall
  rw [List.foldlM_cons] at hrest
  obtain ⟨afterVisit, hvisit, hsuffix⟩ := laneBindOk hrest
  have hlen := (allocationVisits_preserve pre (owner := owner) (edge := edge) hprefix).1
  have he : edge < beforeVisit.2.2.length := by
    rw [hlen]
    simpa only [start, List.length_replicate] using hbound
  obtain ⟨placed, written, _, hwrite, hvisitLeft, hvisitLane⟩ := allocationLanePhase hvisit
  obtain ⟨_, hfinalLeft, hfinalLane⟩ := allocationVisits_preserve post hsuffix (owner := owner) (edge := edge)
  have hmem : edge ∈ pl.buckets.lanes.getD owner [] := List.mem_of_getElem? hentry
  have hnonempty : (pl.buckets.lanes.getD owner []).isEmpty = false :=
    List.isEmpty_eq_false_iff_exists_mem.mpr ⟨edge, hmem⟩
  have hnonroot : (owner != pl.rm.clusters.length) = true := bne_iff_ne.mpr (Nat.ne_of_lt howner)
  have hreserve : ((owner != pl.rm.clusters.length) &&
      !(pl.buckets.lanes.getD owner []).isEmpty) = true := by
    simp only [hnonroot, hnonempty, Bool.not_false, Bool.true_and]
  rw [htable, hfleft, hfinalLane hlanes, hvisitLane, laneWrites_at _ _ _ hwrite hrow hentry he,
    hfinalLeft hlefts, hvisitLeft]
  unfold laneStart
  rw [ite_eq_left hreserve]

/-- The selected graph edge has one in-bucket occurrence, and its actual write survives
both the remainder of the lane fold and later group visits. -/
theorem RegionCrossAllocationStages.reserved_lane_of_edge {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) (hchains : p.chains.length = cg.edges.length)
    (hslot : 0 ≤ P.slot) {owner edge : Nat} {e : Edge} (howner : owner < rm.clusters.length)
    (hedge : cg.edges[edge]? = some e) (htail : e.tail ≠ e.head) (hrev : e.reversed = true)
    (hownerOf : edgeOwnerOf rm stages.groups rm.clusters.length e.tail e.head = owner) :
    ∃ (j : Nat) (laneX : Int), (stages.placement.buckets.lanes.getD owner [])[j]? = some edge ∧
      stages.allocation.lanes.getD edge none = some laneX ∧
      stages.allocation.lefts.getD owner 0 + (reserveWidths stages.placement P).getD owner 0 -
        stages.placement.buckets.loopWidth.getD owner 0 - regionInsetOf P -
        laneExtentOf stages.placement.buckets P.slot owner + P.slot ≤ laneX := by
  let pl := stages.placement
  let selected := pl.buckets.lanes.getD owner []
  have hbuck (g : Nat) : pl.buckets.lanes.getD g [] =
      ((cg.edges.zipIdx.filter (selectsLane rm stages.groups g)).map Prod.snd) := by
    rw [show pl = stages.placement from rfl, stages.hPlacement]
    exact regionBuckets_lanes_exact _ _ _ _ _ _ _
  have hmem (g : Nat) : edge ∈ pl.buckets.lanes.getD g [] ↔ g = owner := by
    rw [hbuck, selectedBucket_mem hedge]
    have hlt : owner < rm.clusters.length + 1 := Nat.lt_succ_of_lt howner
    have hnoskip : ¬ ((!e.reversed || e.tail == e.head) = true) := by
      rw [hrev, beq_eq_false_iff_ne.mpr htail]
      exact Bool.false_ne_true
    have hnroot : ¬ ((owner == rm.clusters.length) = true) :=
      fun h => Nat.ne_of_lt howner (beq_iff_eq.mp h)
    dsimp only [selectsLane]
    rw [ite_eq_right hnoskip, hownerOf, ite_eq_right hnroot, decide_eq_true_iff]
    exact ⟨And.left, fun hg => ⟨hg, hlt⟩⟩
  have hown : edge ∈ selected := (hmem owner).mpr rfl
  have hnodup : selected.Nodup := by
    change (pl.buckets.lanes.getD owner []).Nodup
    rw [hbuck]
    have hsub := (List.filter_sublist (p := selectsLane rm stages.groups owner)
      (l := cg.edges.zipIdx)).map Prod.snd
    apply hsub.nodup
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hown
  obtain ⟨hnodupOrder, hordered, _, hmember⟩ := stages.allocation_topology hparents hmin
  obtain ⟨pre, post, horder⟩ := List.mem_iff_append.mp (hmember owner (Nat.le_of_lt howner))
  rw [horder] at hnodupOrder hordered
  have hnot := (List.nodup_cons.mp (List.nodup_append.mp hnodupOrder).2.1).1
  have hleft := (List.pairwise_cons.mp (List.pairwise_append.mp hordered).2.1).1
  have hownerPl : owner < pl.rm.clusters.length := by simpa only [pl, stages.hPlacement] using howner
  have hbound : edge < pl.p.chains.length := by
    simpa only [pl, stages.hPlacement, hchains] using (List.getElem?_eq_some_iff.mp hedge).1
  have hnone (g : Nat) (hg : g ∈ post) : edge ∉ pl.buckets.lanes.getD g [] := by
    intro he
    exact hnot ((hmem g).mp he ▸ hg)
  have hwrite := allocation_lane_at stages.hAllocation horder hownerPl hbound hnodup hj hleft hnone
  have hext := (stages.bucket_signs hslot).2.1 owner
  change 0 ≤ (2 * P.slot + pl.buckets.laneWidth.getD owner 0) * (selected.length : Int) at hext
  have hpositive : 0 < (selected.length : Int) := Int.natCast_pos.mpr (List.length_pos_of_mem hown)
  have hstride : 0 ≤ 2 * P.slot + pl.buckets.laneWidth.getD owner 0 :=
    (Int.mul_nonneg_iff_of_pos_right hpositive).mp hext
  have hp := Int.mul_nonneg (Int.natCast_nonneg j) hstride
  exact ⟨j, _, hj, hwrite, Int.le_add_of_nonneg_right hp⟩

/-- The selected graph edge has one in-bucket occurrence, and its actual write survives
both the remainder of the lane fold and later group visits. -/
theorem RegionCrossAllocationStages.reserved_trunk_lane_band {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length)
    (hmin : constrainR rm P p = .ok minimum) (hchains : p.chains.length = cg.edges.length)
    (hslot : 0 ≤ P.slot) {owner edge : Nat} {e : Edge} (howner : owner < rm.clusters.length)
    (hedge : cg.edges[edge]? = some e) (htail : e.tail ≠ e.head) (hrev : e.reversed = true)
    (hownerOf : edgeOwnerOf rm stages.groups rm.clusters.length e.tail e.head = owner) :
    ∃ (j : Nat) (laneX : Int), (stages.placement.buckets.lanes.getD owner [])[j]? = some edge ∧
      stages.allocation.lanes.getD edge none = some laneX ∧
      (stages.allocation.lefts.getD owner 0 + (reserveWidths stages.placement P).getD owner 0 -
          stages.placement.buckets.loopWidth.getD owner 0 - regionInsetOf P -
          laneExtentOf stages.placement.buckets P.slot owner + P.slot ≤ laneX ∧
        laneX + (P.slot + (stackSize cg.slot (routeLabels labels e.decl)).width) ≤
          stages.allocation.lefts.getD owner 0 + (reserveWidths stages.placement P).getD owner 0 -
            stages.placement.buckets.loopWidth.getD owner 0 - regionInsetOf P) := by
  let pl := stages.placement
  let selected := pl.buckets.lanes.getD owner []
  have hbuck (g : Nat) : pl.buckets.lanes.getD g [] =
      ((cg.edges.zipIdx.filter (selectsLane rm stages.groups g)).map Prod.snd) := by
    rw [show pl = stages.placement from rfl, stages.hPlacement]
    exact regionBuckets_lanes_exact _ _ _ _ _ _ _
  have hmem (g : Nat) : edge ∈ pl.buckets.lanes.getD g [] ↔ g = owner := by
    rw [hbuck, selectedBucket_mem hedge]
    have hlt : owner < rm.clusters.length + 1 := Nat.lt_succ_of_lt howner
    have hnoskip : ¬ ((!e.reversed || e.tail == e.head) = true) := by
      rw [hrev, beq_eq_false_iff_ne.mpr htail]
      exact Bool.false_ne_true
    have hnroot : ¬ ((owner == rm.clusters.length) = true) :=
      fun h => Nat.ne_of_lt howner (beq_iff_eq.mp h)
    dsimp only [selectsLane]
    rw [ite_eq_right hnoskip, hownerOf, ite_eq_right hnroot, decide_eq_true_iff]
    exact ⟨And.left, fun hg => ⟨hg, hlt⟩⟩
  have hown : edge ∈ selected := (hmem owner).mpr rfl
  have hnodup : selected.Nodup := by
    change (pl.buckets.lanes.getD owner []).Nodup
    rw [hbuck]
    have hsub := (List.filter_sublist (p := selectsLane rm stages.groups owner)
      (l := cg.edges.zipIdx)).map Prod.snd
    apply hsub.nodup
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hown
  obtain ⟨pre, post, horder, hnot, hleft⟩ := stages.allocation_preorder hparents hmin owner howner
  have hownerPl : owner < pl.rm.clusters.length := by simpa only [pl, stages.hPlacement] using howner
  have hbound : edge < pl.p.chains.length := by
    simpa only [pl, stages.hPlacement, hchains] using (List.getElem?_eq_some_iff.mp hedge).1
  have hnone (g : Nat) (hg : g ∈ post) : edge ∉ pl.buckets.lanes.getD g [] := by
    intro he
    exact hnot ((hmem g).mp he ▸ hg)
  have hwrite := allocation_lane_at stages.hAllocation horder hownerPl hbound hnodup hj hleft hnone
  have hext := (stages.bucket_signs hslot).2.1 owner
  change 0 ≤ (2 * P.slot + pl.buckets.laneWidth.getD owner 0) * (selected.length : Int) at hext
  have hpositive : 0 < (selected.length : Int) := Int.natCast_pos.mpr (List.length_pos_of_mem hown)
  have hstride : 0 ≤ 2 * P.slot + pl.buckets.laneWidth.getD owner 0 :=
    (Int.mul_nonneg_iff_of_pos_right hpositive).mp hext
  have hp := Int.mul_nonneg (Int.natCast_nonneg j) hstride
  let lw := cg.edges.map fun e => (stackSize cg.slot (routeLabels labels e.decl)).width
  have hwidth : (stackSize cg.slot (routeLabels labels e.decl)).width ≤
      pl.buckets.laneWidth.getD owner 0 := by
    have hedgeMem : (e, edge) ∈ cg.edges.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hedge
    obtain ⟨preEdges, _, hentries⟩ := List.mem_iff_append.mp hedgeMem
    have hnoskip : ¬ ((!e.reversed || e.tail == e.head) = true) := by
      rw [hrev, beq_eq_false_iff_ne.mpr htail]
      exact Bool.false_ne_true
    have hnroot : ¬ ((owner == rm.clusters.length) = true) :=
      fun h => Nat.ne_of_lt howner (beq_iff_eq.mp h)
    have hentry (b : RegionBuckets) (hsize : b.laneWidth.length = rm.clusters.length + 1) :
        (stackSize cg.slot (routeLabels labels e.decl)).width ≤
          (addLaneEntry rm stages.groups lw b (e, edge)).laneWidth.getD owner 0 := by
      dsimp only [addLaneEntry]
      rw [ite_eq_right hnoskip, hownerOf, ite_eq_right hnroot, laneSetAt_getD]
      rw [ite_eq_left (show owner = owner ∧ owner < b.laneWidth.length from ⟨rfl, by omega⟩)]
      have hitem : lw.getD edge 0 = (stackSize cg.slot (routeLabels labels e.decl)).width := by
        simp only [lw, List.getD_eq_getElem?_getD, List.getElem?_map, hedge,
          Option.map_some, Option.getD_some]
      rw [hitem]
      exact Int.le_max_right _ _
    have hkeep (b : RegionBuckets) (q : Edge × Nat) :
        b.laneWidth.getD owner 0 ≤
          (addLaneEntry rm stages.groups lw b q).laneWidth.getD owner 0 := by
      dsimp only [addLaneEntry]
      split
      · exact Int.le_refl _
      · split
        · exact Int.le_refl _
        · rw [laneSetAt_getD]
          split
          · rename_i he
            simpa only [he.1] using
              (Int.le_max_left (b.laneWidth.getD (edgeOwnerOf rm stages.groups
                rm.clusters.length q.1.tail q.1.head) 0) (lw.getD q.2 0))
          · exact Int.le_refl _
    change _ ≤ stages.placement.buckets.laneWidth.getD owner 0
    rw [show stages.placement.buckets =
      newRegionBuckets rm cg p stages.groups lw stages.before by rw [stages.hPlacement]]
    let n := rm.clusters.length + 1
    let empty : RegionBuckets :=
      { members := List.replicate n [], widths := List.replicate n 0,
        low := List.replicate n 2147483647, high := List.replicate n (-2147483648),
        lanes := List.replicate n [], laneWidth := List.replicate n 0,
        loopWidth := List.replicate n 0 }
    let gather (acc : RegionBuckets) (q : ProperNode × Nat) : RegionBuckets :=
      if q.1.node.border != 0 then acc else
        let g := stages.groups.getD q.2 0
        let width := q.1.node.w + 2 * (q.1.node.loopExtent : Int)
        let left := RouteImpl.xAt stages.before q.2 - Int.tdiv width 2
        let right := left + width
        { acc with
          low := setAt acc.low g (min (acc.low.getD g 2147483647) left)
          high := setAt acc.high g (max (acc.high.getD g (-2147483648)) right)
          members := setAt acc.members g (acc.members.getD g [] ++ [q.2]) }
    let gathered := p.nodes.zipIdx.foldl gather empty
    let add := addLaneEntry rm stages.groups lw
    have hbase : gathered.laneWidth.length = n := by
      apply OrderImpl.foldl_inv (fun b : RegionBuckets => b.laneWidth.length = n) _ _ _
      · exact List.length_replicate
      · intro b hb q _
        dsimp only [gather]
        split <;> exact hb
    have hbefore : (preEdges.foldl add gathered).laneWidth.length = n := by
      apply OrderImpl.foldl_inv (fun b : RegionBuckets => b.laneWidth.length = n) _ _ _ hbase
      intro b hb q _
      dsimp only [add, addLaneEntry]
      split
      · exact hb
      · split
        · exact hb
        · exact (laneSetAt_length _ _ _).trans hb
    change _ ≤ (cg.edges.zipIdx.foldl add gathered).laneWidth.getD owner 0
    rw [hentries, List.foldl_append, List.foldl_cons]
    apply OrderImpl.foldl_inv
      (fun b : RegionBuckets => (stackSize cg.slot (routeLabels labels e.decl)).width ≤
        b.laneWidth.getD owner 0) _ _ _
    · exact hentry _ hbefore
    · intro b hb q _
      exact Int.le_trans hb (hkeep b q)
  have hj' : (j : Int) + 1 ≤ (selected.length : Int) := by
    have hh := (List.getElem?_eq_some_iff.mp hj).1
    change j < selected.length at hh
    omega
  have hmul := Int.mul_le_mul_of_nonneg_left hj' hstride
  rw [Int.mul_add, Int.mul_one, Int.mul_comm (2 * P.slot + pl.buckets.laneWidth.getD owner 0) (j : Int)] at hmul
  refine ⟨j, _, hj, hwrite, Int.le_add_of_nonneg_right hp, ?_⟩
  change stages.allocation.lefts.getD owner 0 + (reserveWidths pl P).getD owner 0 -
      pl.buckets.loopWidth.getD owner 0 - regionInsetOf P - laneExtentOf pl.buckets P.slot owner +
      P.slot + (j : Int) * (2 * P.slot + pl.buckets.laneWidth.getD owner 0) +
        (P.slot + (stackSize cg.slot (routeLabels labels e.decl)).width) ≤
    stages.allocation.lefts.getD owner 0 + (reserveWidths pl P).getD owner 0 -
      pl.buckets.loopWidth.getD owner 0 - regionInsetOf P
  change _ ≤ laneExtentOf pl.buckets P.slot owner at hmul
  omega


theorem RegionCrossAllocationStages.trunk_lane_table_length {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed) :
    reserved.length = p.chains.length := by
  rw [stages.hLanes]
  have ha := stages.hAllocation
  unfold allocatePl at ha
  obtain ⟨final, ht, h⟩ := laneBindOk ha
  have hf : final.2.2 = stages.allocation.lanes :=
    congrArg (fun q : RegionAllocation × List Int => q.1.lanes) (Except.ok.inj h)
  rw [← hf]
  have hlen := (allocationVisits_preserve _ (owner := 0) (edge := 0) ht).1
  simpa only [List.length_replicate, stages.hPlacement] using hlen

/-- The synthetic root, or any nonlocal owner, cannot enter a reserved bucket. -/
theorem RegionCrossAllocationStages.trunk_lane_absent_of_nonlocal_owner {P : Params}
    {rm : ComponentRegions} {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    {edge : Nat} {e : Edge} (hedge : cg.edges[edge]? = some e)
    (howner : rm.clusters.length ≤ edgeOwnerOf rm stages.groups rm.clusters.length e.tail e.head) :
    reserved.getD edge none = none := by
  have haway (g : Nat) : edge ∉ stages.placement.buckets.lanes.getD g [] := by
    rw [stages.hPlacement, regionBuckets_lanes_exact]
    intro hm
    have hs := (selectedBucket_mem hedge).mp hm
    dsimp only [selectsLane] at hs
    split at hs
    · cases hs
    · split at hs
      · cases hs
      · rename_i _ hroot
        have hb := (of_decide_eq_true hs).2
        exact hroot (beq_iff_eq.mpr (by omega))
  rw [stages.hLanes]
  have ha := stages.hAllocation
  unfold allocatePl at ha
  obtain ⟨final, ht, h⟩ := laneBindOk ha
  have hf : final.2.2 = stages.allocation.lanes :=
    congrArg (fun q : RegionAllocation × List Int => q.1.lanes) (Except.ok.inj h)
  rw [← hf, (allocationVisits_preserve _ (owner := 0) (edge := edge) ht).2.2 (fun g _ => haway g),
    List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

end Elegant.Layered.PipelineImpl

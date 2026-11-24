import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionRunSpec

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl
open CoordsImpl (clusterSep clusterGap ownTitleAnchor coordSep)

private theorem bindOk {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ mid, x = .ok mid ∧ f mid = .ok out := by
  cases x with
  | error e => cases h
  | ok mid => exact ⟨mid, rfl, h⟩

private theorem setAtLength {α : Type} (xs : List α) (i : Nat) (value : α) :
    (setAt xs i value).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [setAt, ih]

private theorem setAtOther {α : Type} (xs : List α) (i j : Nat) (value fallback : α)
    (hne : i ≠ j) : (setAt xs i value).getD j fallback = xs.getD j fallback := by
  induction xs generalizing i j with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => cases j with
      | zero => exact (hne rfl).elim
      | succ j => rfl
    | succ i => cases j with
      | zero => rfl
      | succ j => exact ih i j (fun h => hne (congrArg Nat.succ h))

private theorem setAtSelf {α : Type} (xs : List α) (i : Nat) (value fallback : α)
    (hin : i < xs.length) : (setAt xs i value).getD i fallback = value := by
  induction xs generalizing i with
  | nil => simp at hin
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hin)

private theorem setAtOutside {α : Type} (xs : List α) (i : Nat) (value : α)
    (hout : xs.length ≤ i) : setAt xs i value = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => simp at hout
    | succ i => exact congrArg (List.cons x) (ih i (by simpa using hout))

/-- The first adjacency from a border-0 node pays at least the minimum gap.
The rest of the path needs only the zero-gap chaining lemma, so uniqueness
of title copies is not needed for this pair. -/
theorem crossCoordsClusterWith_plain_order {ng cp : Int} {p : Proper}
    {layers : List (List Nat)} {xs : List Int}
    (hcross : crossCoordsClusterWith ng cp p layers = .ok xs)
    {layer : List Nat} (hlayer : layer ∈ layers) {i j a b : Nat} {na : ProperNode}
    (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hna : p.nodes[a]? = some na) (hplain : na.node.border = 0) :
    coordSep (min ng cp) p a b ≤ xs.getD b 0 - xs.getD a 0 := by
  have hj := (List.getElem?_eq_some_iff.mp hb).1
  have hi : i + 1 < layer.length := by omega
  let c := layer[i + 1]
  have hc : layer[i + 1]? = some c := List.getElem?_eq_getElem hi
  have hgap : min ng cp ≤ clusterGap ng cp p a c := by
    apply CoordsImpl.clusterGap_ge_min
    cases hnc : p.nodes[c]? with
    | none => simp [ownTitleAnchor, hna, hnc]
    | some nc => simp [ownTitleAnchor, hna, hnc, hplain]
  have hstep := CoordsImpl.cluster_balance_separated hcross layer hlayer i a c ha hc
  unfold clusterSep coordSep at hstep
  unfold coordSep
  by_cases hn : i + 1 = j
  · have hc' : layer[j]? = some c := by simpa only [hn] using hc
    have hcb : c = b := Option.some.inj (hc'.symm.trans hb)
    subst b
    omega
  · have hrest := CoordsImpl.cluster_zero_pairs_separated hcross layer hlayer
      (i + 1) j c b (by omega) hc hb
    have hsizes := (CoordsImpl.crossCoordsClusterWith_spec hcross).2.2.2.1
    have hhalf : 0 ≤ Int.fdiv (CoordsImpl.nodeW p c) 2 := by
      rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
      exact Int.ediv_nonneg (CoordsImpl.nodeW_nonneg hsizes c) (by decide)
    omega

private def bucketMember (ngs : List Nat) (g : Nat) (q : ProperNode × Nat) : Bool :=
  q.1.node.border == 0 && ngs.getD q.2 0 == g

private theorem bucketMember_iff {ngs : List Nat} {g : Nat} {q : ProperNode × Nat} :
    bucketMember ngs g q ↔ q.1.node.border = 0 ∧ ngs.getD q.2 0 = g := by
  simp only [bucketMember, Bool.and_eq_true_iff, beq_iff_eq]

private def gatherMembers (ngs : List Nat) (members : List (List Nat))
    (q : ProperNode × Nat) : List (List Nat) :=
  if q.1.node.border != 0 then members else
    let owner := ngs.getD q.2 0
    setAt members owner (members.getD owner [] ++ [q.2])

private theorem gatherMembers_getD (ngs : List Nat) (entries : List (ProperNode × Nat))
    (members : List (List Nat)) (g : Nat) :
    (entries.foldl (gatherMembers ngs) members).getD g [] = members.getD g [] ++
      (if g < members.length then (entries.filter (bucketMember ngs g)).map Prod.snd else []) := by
  induction entries generalizing members with
  | nil => simp
  | cons q rest ih =>
    rw [List.foldl_cons, ih]
    by_cases hp : q.1.node.border = 0
    · have hstep : gatherMembers ngs members q =
          setAt members (ngs.getD q.2 0) (members.getD (ngs.getD q.2 0) [] ++ [q.2]) := by
        unfold gatherMembers
        exact ite_eq_right (fun h => (bne_iff_ne.mp h) hp)
      rw [hstep, setAtLength]
      by_cases ho : ngs.getD q.2 0 = g
      · rw [ho]
        by_cases hin : g < members.length
        · have hm : bucketMember ngs g q := bucketMember_iff.mpr ⟨hp, ho⟩
          rw [setAtSelf _ _ _ _ hin, List.filter_cons_of_pos hm]
          simp only [ite_eq_left hin, List.map_cons, List.append_assoc, List.singleton_append]
        · rw [setAtOutside _ _ _ (Nat.le_of_not_gt hin)]
          simp only [ite_eq_right hin]
      · have hm : ¬ bucketMember ngs g q := fun h => ho (bucketMember_iff.mp h).2
        rw [setAtOther _ _ _ _ _ ho, List.filter_cons_of_neg hm]
    · have hstep : gatherMembers ngs members q = members := by
        unfold gatherMembers
        exact ite_eq_left (bne_iff_ne.mpr hp)
      have hm : ¬ bucketMember ngs g q := fun h => hp (bucketMember_iff.mp h).1
      rw [hstep, List.filter_cons_of_neg hm]

private theorem newRegionBuckets_members (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (ngs : List Nat) (labelWidths x : List Int) (g : Nat) :
    (newRegionBuckets rm cg p ngs labelWidths x).members.getD g [] =
      if g < rm.clusters.length + 1 then
        (p.nodes.zipIdx.filter (bucketMember ngs g)).map Prod.snd else [] := by
  let empty : RegionBuckets :=
    ⟨List.replicate (rm.clusters.length + 1) [], List.replicate (rm.clusters.length + 1) 0,
      List.replicate (rm.clusters.length + 1) 2147483647,
      List.replicate (rm.clusters.length + 1) (-2147483648),
      List.replicate (rm.clusters.length + 1) [], List.replicate (rm.clusters.length + 1) 0,
      List.replicate (rm.clusters.length + 1) 0⟩
  let gather (acc : RegionBuckets) (q : ProperNode × Nat) : RegionBuckets :=
    if q.1.node.border != 0 then acc else
      let owner := ngs.getD q.2 0
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
      let owner := edgeOwnerOf rm ngs root q.1.tail q.1.head
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
      (entries.foldl gather acc).members = entries.foldl (gatherMembers ngs) acc.members := by
    induction entries generalizing acc with
    | nil => rfl
    | cons q rest ih =>
      rw [List.foldl_cons, List.foldl_cons, ih]
      have heq : (gather acc q).members = gatherMembers ngs acc.members q := by
        dsimp only [gather, gatherMembers]
        split <;> rfl
      rw [heq]
  rw [laneMembers, gatheredMembers, gatherMembers_getD]
  have hnil : (List.replicate (rm.clusters.length + 1) ([] : List Nat)).getD g [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  simp only [empty, hnil, List.length_replicate, List.nil_append]

private theorem newRegionBuckets_count (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (ngs : List Nat) (labelWidths x : List Int) (g v : Nat) {n : ProperNode}
    (hv : p.nodes[v]? = some n) (hp : n.node.border = 0) :
    ((newRegionBuckets rm cg p ngs labelWidths x).members.getD g []).count v =
      if g < rm.clusters.length + 1 ∧ ngs.getD v 0 = g then 1 else 0 := by
  rw [newRegionBuckets_members]
  by_cases hg : g < rm.clusters.length + 1
  · rw [ite_eq_left hg]
    have hmem : v ∈ (p.nodes.zipIdx.filter (bucketMember ngs g)).map Prod.snd ↔
        ngs.getD v 0 = g := by
      constructor
      · intro h
        obtain ⟨⟨m, k⟩, hq, rfl⟩ := List.mem_map.mp h
        obtain ⟨hm, howner⟩ := List.mem_filter.mp hq
        have hlookup := List.mem_zipIdx_iff_getElem?.mp hm
        have heq : m = n := Option.some.inj (hlookup.symm.trans hv)
        subst m
        exact (bucketMember_iff.mp howner).2
      · intro h
        exact List.mem_map.mpr ⟨(n, v), List.mem_filter.mpr
          ⟨List.mem_zipIdx_iff_getElem?.mpr hv, bucketMember_iff.mpr ⟨hp, h⟩⟩, rfl⟩
    by_cases ho : ngs.getD v 0 = g
    · rw [ite_eq_left ⟨hg, ho⟩]
      have hnd : (p.nodes.zipIdx.map Prod.snd).Nodup := by
        rw [List.zipIdx_map_snd]
        exact List.nodup_range'
      have hsub := (List.filter_sublist (p := bucketMember ngs g)
        (l := p.nodes.zipIdx)).map Prod.snd
      exact (hsub.nodup hnd).count_of_mem (hmem.mpr ho)
    · rw [ite_eq_right (fun h => ho h.2)]
      exact List.count_eq_zero_of_not_mem (fun h => ho (hmem.mp h))
  · simp [hg]

private theorem shiftMembers_getD (members : List Nat) (xs : List Int) (v : Nat)
    (shift : Int) (hv : v < xs.length) :
    (members.foldl (fun x i => setAt x i (x.getD i 0 + shift)) xs).getD v 0 =
      xs.getD v 0 + (members.count v : Int) * shift := by
  induction members generalizing xs with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons, ih _ (by rwa [setAtLength])]
    by_cases he : i = v
    · subst i
      rw [setAtSelf _ _ _ _ hv, List.count_cons_self, Int.natCast_add, Int.add_mul]
      simp only [Int.natCast_one, Int.one_mul]
      omega
    · rw [setAtOther _ _ _ _ _ he, List.count_cons_of_ne he]

private theorem shiftMembers_length (members : List Nat) (xs : List Int) (shift : Int) :
    (members.foldl (fun x i => setAt x i (x.getD i 0 + shift)) xs).length = xs.length := by
  induction members generalizing xs with
  | nil => rfl
  | cons i rest ih => rw [List.foldl_cons, ih, setAtLength]

private theorem allocateGroup_xs {pl : RegionPlacement} {P : Params} {widths : List Int}
    {group : Nat} {xs lefts : List Int} {lanes : List (Option Int)}
    {out : List Int × List Int × List (Option Int)}
    (h : allocateGroup pl P widths group (xs, lefts, lanes) = .ok out) :
    out.1 = (pl.buckets.members.getD group []).foldl (fun x v => setAt x v (x.getD v 0 +
      (lefts.getD group 0 + (if group != pl.rm.clusters.length then
        pl.minimum.origins.getD group 0 else 0) - pl.buckets.low.getD group 0))) xs := by
  unfold allocateGroup at h
  dsimp only at h
  obtain ⟨placed, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  have he := (congrArg Prod.fst (Except.ok.inj h)).symm
  let members := pl.buckets.members.getD group []
  let shift := lefts.getD group 0 + (if group != pl.rm.clusters.length then
    pl.minimum.origins.getD group 0 else 0) - pl.buckets.low.getD group 0
  let step (x : List Int) (v : Nat) := setAt x v (x.getD v 0 + shift)
  change out.1 = (if members.isEmpty then xs else members.foldl step xs) at he
  change out.1 = members.foldl step xs
  by_cases hm : members.isEmpty
  · rw [ite_eq_left hm] at he
    rwa [List.nil_of_isEmpty hm, List.foldl_nil]
  · rwa [ite_eq_right hm] at he

private theorem allocatePl_same_bucket {pl : RegionPlacement} {P : Params} {xs out : List Int}
    {alloc : RegionAllocation} {a b : Nat}
    (h : allocatePl pl P xs = .ok (alloc, out)) (ha : a < xs.length) (hb : b < xs.length)
    (hcount : ∀ g, ((pl.buckets.members.getD g []).count a) =
      ((pl.buckets.members.getD g []).count b)) :
    out.getD b 0 - out.getD a 0 = xs.getD b 0 - xs.getD a 0 := by
  have foldDiff (groups : List Nat) (initial final : List Int × List Int × List (Option Int))
      (hlenA : a < initial.1.length) (hlenB : b < initial.1.length)
      (hf : groups.foldlM (fun state g => allocateGroup pl P (reserveWidths pl P) g state) initial =
        Except.ok final) :
      final.1.getD b 0 - final.1.getD a 0 = initial.1.getD b 0 - initial.1.getD a 0 := by
    induction groups generalizing initial with
    | nil =>
      change Except.ok initial = Except.ok final at hf
      cases hf
      rfl
    | cons g gs ih =>
      rw [List.foldlM_cons] at hf
      obtain ⟨mid, hmid, htail⟩ := bindOk hf
      rcases initial with ⟨x0, l0, r0⟩
      have hx := allocateGroup_xs hmid
      have hlen : mid.1.length = x0.length := by rw [hx, shiftMembers_length]
      have hdiff := ih mid (by rwa [hlen]) (by rwa [hlen]) htail
      rw [hdiff, hx, shiftMembers_getD _ _ b _ hlenB,
        shiftMembers_getD _ _ a _ hlenA, hcount g]
      omega
  unfold allocatePl at h
  obtain ⟨fin, hfin, h⟩ := bindOk h
  have ho : out = fin.1 := (congrArg Prod.snd (Except.ok.inj h)).symm
  rw [ho]
  exact foldDiff _ _ _ ha hb hfin

private def NotClusterAnchor (rm : ComponentRegions) (v : Nat) : Prop :=
  ∀ c ∈ rm.clusters, c.top ≠ v ∧ c.bottom ≠ v

private def regionFrameStep (pl : RegionPlacement) (P : Params) (alloc : RegionAllocation)
    (x : List Int) (q : RegionCluster × Nat) : List Int :=
  let c := q.1
  let left := alloc.lefts.getD q.2 0
  let frameRight := left + alloc.widths.getD q.2 0 - pl.buckets.loopWidth.getD q.2 0
  let center := left + Int.tdiv (frameRight - left) 2
  let x := pl.p.nodes.zipIdx.foldl (fun x nq =>
    if nq.1.node.clusterPath.getLast? != some c.decl then x
    else
      match nq.1.node.border with
      | -1 => setAt x nq.2 (left + Int.tdiv P.clusterBorderW 2)
      | 1 => setAt x nq.2 (frameRight - P.clusterBorderW + Int.tdiv P.clusterBorderW 2)
      | 3 => setAt x nq.2 center
      | _ => x) x
  setAt (setAt x c.top center) c.bottom center

private theorem regionFrames_plain {pl : RegionPlacement} {P : Params}
    {alloc : RegionAllocation} {xs : List Int} {v : Nat} {n : ProperNode}
    (hv : pl.p.nodes[v]? = some n) (hplain : n.node.border = 0)
    (hanchor : NotClusterAnchor pl.rm v) :
    (regionFrames pl P alloc xs).getD v 0 = xs.getD v 0 := by
  have markers (ns : List (ProperNode × Nat)) (x : List Int) (decl : Nat)
      (left right center : Int)
      (hns : ∀ q ∈ ns, pl.p.nodes[q.2]? = some q.1) :
      (ns.foldl (fun x q =>
        if q.1.node.clusterPath.getLast? != some decl then x else
          match q.1.node.border with
          | -1 => setAt x q.2 (left + Int.tdiv P.clusterBorderW 2)
          | 1 => setAt x q.2 (right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2)
          | 3 => setAt x q.2 center
          | _ => x) x).getD v 0 = x.getD v 0 := by
    induction ns generalizing x with
    | nil => rfl
    | cons q qs ih =>
      rw [List.foldl_cons, ih _ (fun e he => hns e (List.mem_cons_of_mem _ he))]
      by_cases heq : q.2 = v
      · have hq := hns q List.mem_cons_self
        rw [heq, hv] at hq
        have hborder : q.1.node.border = 0 :=
          (congrArg (fun m : ProperNode => m.node.border) (Option.some.inj hq)).symm.trans hplain
        simp [hborder]
      · split
        · rfl
        · split <;> first | rfl | exact setAtOther _ _ _ _ _ heq
  have step_plain (q : RegionCluster × Nat) (x : List Int)
      (hq : q.1 ∈ pl.rm.clusters) :
      (regionFrameStep pl P alloc x q).getD v 0 = x.getD v 0 := by
    obtain ⟨ht, hb⟩ := hanchor q.1 hq
    unfold regionFrameStep
    dsimp only
    rw [setAtOther _ _ _ _ _ hb, setAtOther _ _ _ _ _ ht]
    exact markers pl.p.nodes.zipIdx x _ _ _ _
      (fun e he => List.mem_zipIdx_iff_getElem?.mp he)
  have fold_plain (entries : List (RegionCluster × Nat)) (x : List Int)
      (hentries : ∀ q ∈ entries, q.1 ∈ pl.rm.clusters) :
      (entries.foldl (regionFrameStep pl P alloc) x).getD v 0 = x.getD v 0 := by
    induction entries generalizing x with
    | nil => rfl
    | cons q qs ih =>
      rw [List.foldl_cons, ih _ (fun e he => hentries e (List.mem_cons_of_mem _ he))]
      exact step_plain q x (hentries q List.mem_cons_self)
  have hframe : regionFrames pl P alloc xs =
      pl.rm.clusters.zipIdx.foldl (regionFrameStep pl P alloc) xs := rfl
  rw [hframe]
  exact fold_plain pl.rm.clusters.zipIdx xs (fun q hq =>
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq))

private theorem clusterPortR_other {pl : RegionPlacement} {g k v : Nat} {xs out : List Int}
    (h : clusterPortR pl g k xs = .ok out) (hne : k ≠ v) :
    out.getD v 0 = xs.getD v 0 := by
  unfold clusterPortR at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · have he := (Except.ok.inj h).symm
      rw [he, setAtOther _ _ _ _ _ hne]
  · cases h

private theorem reservedPortsR_other {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {xs out : List Int} {outP : Proper} {v : Nat}
    (h : reservedPortsR pl cg labels xs = .ok (out, outP))
    (hanchor : NotClusterAnchor pl.rm v) :
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
      obtain ⟨mid, hmid, htail⟩ := bindOk hf
      have hrest := ih mid (fun e he => hentries e (List.mem_cons_of_mem _ he)) htail
      obtain ⟨ht, hb⟩ := hanchor q.1 (hentries q List.mem_cons_self)
      dsimp only [step] at hmid
      split at hmid
      · cases hmid
      · obtain ⟨x1, hx1, hmid⟩ := bindOk hmid
        obtain ⟨x2, hx2, hmid⟩ := bindOk hmid
        rw [← Except.ok.inj hmid] at hrest
        refine ⟨hrest.1.trans ((clusterPortR_other hx2 hb).trans (clusterPortR_other hx1 ht)), ?_⟩
        exact hrest.2.trans (by
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne ht])
  unfold reservedPortsR at h
  change ((pl.rm.clusters.zipIdx.foldlM step (xs, pl.p.nodes.toArray)).bind _) = .ok (out, outP) at h
  obtain ⟨fin, hf, h⟩ := bindOk h
  have hother := foldOther _ _ _ (fun _ he =>
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)) hf
  have hout := Except.ok.inj h
  have hx : out = fin.1 := (congrArg Prod.fst hout).symm
  have hp : outP.nodes = fin.2.toList :=
    (congrArg (fun q : List Int × Proper => q.2.nodes) hout).symm
  rw [hx, hp, Array.getElem?_toList, ← List.getElem?_toArray]
  exact hother

private theorem regionFrames_reservedPorts_plain {pl : RegionPlacement} {P : Params}
    {cg : Graph} {labels : List MeasuredLabel} {alloc : RegionAllocation}
    {xs out : List Int} {outP : Proper} {v : Nat} {n : ProperNode}
    (h : reservedPortsR pl cg labels (regionFrames pl P alloc xs) = .ok (out, outP))
    (hv : pl.p.nodes[v]? = some n) (hplain : n.node.border = 0)
    (hanchor : NotClusterAnchor pl.rm v) :
    out.getD v 0 = xs.getD v 0 ∧ outP.nodes[v]? = pl.p.nodes[v]? := by
  obtain ⟨hx, hp⟩ := reservedPortsR_other h hanchor
  exact ⟨hx.trans (regionFrames_plain (pl := pl) (P := P) (alloc := alloc) (xs := xs)
    hv hplain hanchor), hp⟩

/-- The actual placement keeps the `coordSep` gap within an owner bucket.
Each allocation step translates both members the same number of times;
frame placement and reserved ports do not write these two indices. -/
theorem crossCoordsR_same_bucket_separated {P : Params} {rm : ComponentRegions} {cg : Graph}
    {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok (xs, pinned, reserved, placed))
    {layer : List Nat} (hlayer : layer ∈ pinned) {i j a b : Nat} {na nb : ProperNode}
    (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hna : p.nodes[a]? = some na) (hnb : p.nodes[b]? = some nb)
    (hpa : na.node.border = 0) (hpb : nb.node.border = 0)
    (hanchorA : ∀ c ∈ rm.clusters, c.top ≠ a ∧ c.bottom ≠ a)
    (hanchorB : ∀ c ∈ rm.clusters, c.top ≠ b ∧ c.bottom ≠ b)
    (howner : ∀ ngs, nodeGroupsOf rm p = .ok ngs → ngs.getD a 0 = ngs.getD b 0) :
    coordSep (min P.nodeGap P.clusterPad) placed a b ≤ xs.getD b 0 - xs.getD a 0 := by
  unfold crossCoordsR at h
  obtain ⟨children, _, h⟩ := bindOk h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    cases h
  · obtain ⟨ngs, hngs, h⟩ := bindOk h
    obtain ⟨before, hcross, h⟩ := bindOk h
    obtain ⟨_, _, h⟩ := bindOk h
    obtain ⟨⟨alloc, shifted⟩, halloc, h⟩ := bindOk h
    obtain ⟨⟨final, pFinal⟩, hports, h⟩ := bindOk h
    have he := Except.ok.inj h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    have hbefore := crossCoordsClusterWith_plain_order hcross hlayer hij ha hb hna hpa
    have hlen := CoordsImpl.crossCoordsClusterWith_length hcross
    have haLen : a < before.length := by
      rw [hlen]
      exact (List.getElem?_eq_some_iff.mp hna).1
    have hbLen : b < before.length := by
      rw [hlen]
      exact (List.getElem?_eq_some_iff.mp hnb).1
    have hdiff := allocatePl_same_bucket halloc haLen hbLen (fun g => by
      rw [newRegionBuckets_count _ _ _ _ _ _ _ _ hna hpa,
        newRegionBuckets_count _ _ _ _ _ _ _ _ hnb hpb, howner ngs hngs])
    obtain ⟨hxa, hna'⟩ := regionFrames_reservedPorts_plain hports hna hpa hanchorA
    obtain ⟨hxb, hnb'⟩ := regionFrames_reservedPorts_plain hports hnb hpb hanchorB
    rw [hxa, hxb, hdiff]
    simpa only [coordSep, CoordsImpl.nodeW, hna', hnb'] using hbefore

private theorem same_node_group {rm : ComponentRegions} {p : Proper} {ngs : List Nat}
    (hngs : nodeGroupsOf rm p = .ok ngs) {a b : Nat} {na nb : ProperNode}
    (ha : p.nodes[a]? = some na) (hb : p.nodes[b]? = some nb)
    (hpath : na.node.clusterPath.getLast? = nb.node.clusterPath.getLast?) :
    ngs.getD a 0 = ngs.getD b 0 := by
  let owner (q : ProperNode × Nat) : Except LayoutError Nat :=
    match q.1.node.clusterPath.getLast? with
    | none => pure rm.clusters.length
    | some decl =>
      match clusterOfDecl rm decl with
      | some k => pure k
      | none => throw .domain
  have hmap : p.nodes.zipIdx.mapM owner = .ok ngs := hngs
  have hza : p.nodes.zipIdx[a]? = some (na, a) := by
    simp only [List.getElem?_zipIdx, ha, Option.map_some, Nat.zero_add]
  have hzb : p.nodes.zipIdx[b]? = some (nb, b) := by
    simp only [List.getElem?_zipIdx, hb, Option.map_some, Nat.zero_add]
  have hlookup := (mapM_getElem? owner _ _ hmap).2
  obtain ⟨ga, hga, ha'⟩ := hlookup a _ hza
  obtain ⟨gb, hgb, hb'⟩ := hlookup b _ hzb
  have he : owner (na, a) = owner (nb, b) := by
    dsimp only [owner]
    rw [hpath]
  have hEq : ga = gb := Except.ok.inj (hga.symm.trans (he.trans hgb))
  simp only [List.getD_eq_getElem?_getD, ha', hb', Option.getD_some, hEq]

private theorem resolved_cluster_anchor_source {P : Params} {s : RegionSpec}
    {inp : Input} {cg : Graph} {rm : ComponentRegions}
    (h : newComponentRegions (some s) P inp cg = .ok (some rm))
    {c : RegionCluster} (hc : c ∈ rm.clusters) :
    (∃ n, cg.nodes[c.top]? = some n ∧ n.border ≠ 0) ∧
    (∃ n, cg.nodes[c.bottom]? = some n ∧ n.border ≠ 0) := by
  unfold newComponentRegions at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bindOk h
    split at h
    · cases h
    · have hcluster : rm.clusters = clusterRows inp s cg := by
        have he := Option.some.inj (Except.ok.inj h)
        exact (congrArg ComponentRegions.clusters he).symm
      rw [hcluster] at hc
      unfold clusterRows at hc
      obtain ⟨q, hq, hc⟩ := List.mem_filterMap.mp hc
      dsimp only at hc
      split at hc
      · cases hc
      · rename_i hborder
        have ht : ∃ n, cg.nodes[q.2]? = some n ∧ n.border ≠ 0 := by
          refine ⟨q.1, List.mem_zipIdx_iff_getElem?.mp hq, ?_⟩
          intro hh
          simp [hh] at hborder
        have he := Option.some.inj hc
        rw [← he]
        refine ⟨ht, ?_⟩
        dsimp only
        split
        · rename_i b hb
          have hmem := List.mem_of_find?_eq_some hb
          have htest := List.find?_some hb
          refine ⟨b.1, List.mem_zipIdx_iff_getElem?.mp hmem, ?_⟩
          intro hh
          simp [hh] at htest
        · exact ht

private theorem source_coordinate_record (P : Params) (exact : List Nat) (s : RegionSpec)
    {labeled : Proper} {v : Nat} {n : Node}
    (h : labeled.nodes[v]? = some ⟨n, false, none, false⟩) :
    ∃ m, (coordinateGraphR P exact (some s) labeled).nodes[v]? = some m ∧
      m.node.border = n.border ∧ m.node.clusterPath = n.clusterPath := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservationsR s.titles P.clusterPad sized
  have hkeys := sizeProperPortsX_key P exact labeled v
  change (sized.nodes[v]?).map _ = _ at hkeys
  rw [h] at hkeys
  cases hs : sized.nodes[v]? with
  | none => simp [hs] at hkeys
  | some sz =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkeys
    let t : ProperNode := if sz.node.border == -2 || sz.node.border == 2 then
      { sz with node := { sz.node with w := 0, h := 0 } } else sz
    have hlookupT : titled.nodes[v]? = some t := by
      unfold titled titleReservationsR
      dsimp only
      rw [List.getElem?_append_left (by
        simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hs).1)]
      simp only [List.getElem?_map, hs, Option.map_some] <;> rfl
    have htkeys : t.node.border = sz.node.border ∧ t.node.clusterPath = sz.node.clusterPath := by
      dsimp only [t]
      split <;> exact ⟨rfl, rfl⟩
    obtain ⟨extra, hbordered, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    have hlookupC : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[v]? =
        some (clearF t) := by
      rw [clearProxyExtents_nodes, List.getElem?_map, hbordered,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp hlookupT).1, hlookupT] <;> rfl
    obtain ⟨m, hm, _⟩ := materialize_exists _ hlookupC
    have ⟨old, ho, _, hb, _, hsame⟩ := materialize_lookup _ hm
    have he : old = clearF t := Option.some.inj (ho.symm.trans hlookupC)
    subst old
    have htDummy : t.dummy = false := by
      dsimp only [t]
      split <;> exact hkeys.1
    have hcDummy : (clearF t).dummy = false := (clearF_keys t).1.trans htDummy
    refine ⟨m, hm, hb.trans ((clearF_keys t).2.1.trans (htkeys.1.trans hkeys.2.1)), ?_⟩
    rw [hsame hcDummy, (clearF_keys t).2.2.1, htkeys.2, hkeys.2.2]

/-- In a component run, region ports target original frame markers, not
plain proper nodes. Ranking preserves the graph records that identify them. -/
private theorem resolved_anchors_not_plain {P : Params} {s : RegionSpec}
    {inp : Input} {cg cg' : Graph} {rm : ComponentRegions} {exact : List Nat}
    {ranks : List Int} {rankBudget : Bool} {p0 labeled : Proper}
    {labels : List MeasuredLabel}
    (hresolved : newComponentRegions (some s) P inp cg = .ok (some rm))
    (hrank : rankEquivalentR rm cg = .ok (ranks, cg', rankBudget))
    (hnorm : normalize cg' ranks = .ok p0)
    (hlab : Labels.addLabelNodes cg' p0 (componentLabels cg' labels) = .ok labeled)
    {v : Nat} {n : ProperNode}
    (hv : (coordinateGraphR P exact (some s) labeled).nodes[v]? = some n)
    (hp : n.node.border = 0) : NotClusterAnchor rm v := by
  have hnodes := rankEquivalentR_nodes_eq hrank
  have away {i : Nat} (hi : ∃ nd, cg.nodes[i]? = some nd ∧ nd.border ≠ 0) : i ≠ v := by
    obtain ⟨nd, hnd, hborder⟩ := hi
    intro heq
    subst i
    rw [← hnodes] at hnd
    obtain ⟨m, hm, hb, _⟩ := source_coordinate_record P exact s
      (addLabelNodes_untouched_node hlab (normalize_node_record hnorm hnd) rfl)
    have he : m = n := Option.some.inj (hm.symm.trans hv)
    rw [he, hp] at hb
    exact hborder hb.symm
  intro c hc
  obtain ⟨ht, hb⟩ := resolved_cluster_anchor_source hresolved hc
  exact ⟨away ht, away hb⟩

/-- Same-owner ordered original nodes retain their cross-axis separation in
both placement branches of a some-spec component run. In the region-active
branch, the resolved marker records establish that neither index is a port. -/
theorem componentRunR_region_same_owner_separated {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {i j a b : Nat} {na nb : Node}
    (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hna : cg'.nodes[a]? = some na) (hnb : cg'.nodes[b]? = some nb)
    (hpa : na.border = 0) (hpb : nb.border = 0)
    (hpath : na.clusterPath.getLast? = nb.clusterPath.getLast?) :
    coordSep (min P.nodeGap P.clusterPad) run.coordinateProper a b ≤
      run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  obtain ⟨rs, ranks, budget, p0, labeled, pCoord, minimum, ord, widths, reserved,
    placed, q0, yt, ysMid, hs⟩ := componentRunR_stages hrun
  have hplaced := hs.hPlaced
  obtain ⟨aCoord, haCoord, hba, hpathA⟩ := source_coordinate_record P exact s
    (addLabelNodes_untouched_node hs.hLabels (normalize_node_record hs.hNorm hna) rfl)
  obtain ⟨bCoord, hbCoord, hbb, hpathB⟩ := source_coordinate_record P exact s
    (addLabelNodes_untouched_node hs.hLabels (normalize_node_record hs.hNorm hnb) rfl)
  rw [hs.hCoordProper]
  rcases hplaced with ⟨_, hcross, hlayers, _, hp⟩ | ⟨rm, m, he, _, hplace⟩
  · rw [hp, ← hs.hCoord]
    have hleft : layer ∈ ord.layers := by simpa only [hlayers] using hlayer
    rw [← hs.hCoord] at hcross
    exact crossCoordsClusterWith_plain_order hcross hleft hij ha hb haCoord (hba.trans hpa)
  · have hrm : newComponentRegions (some s) P inp cg = .ok (some rm) :=
      hs.hRs.trans (congrArg Except.ok he)
    rcases hs.hRank with ⟨_, hnone, _, _, _, _⟩ | ⟨rm', he', hrank⟩
    · rw [he] at hnone
      cases hnone
    have heR : rm = rm' := Option.some.inj (he.symm.trans he')
    subst rm'
    have hanchorA := resolved_anchors_not_plain hrm hrank hs.hNorm hs.hLabels haCoord (hba.trans hpa)
    have hanchorB := resolved_anchors_not_plain hrm hrank hs.hNorm hs.hLabels hbCoord (hbb.trans hpb)
    rw [hs.hCoord] at haCoord hbCoord
    exact crossCoordsR_same_bucket_separated hplace hlayer hij ha hb haCoord hbCoord
      (hba.trans hpa) (hbb.trans hpb) hanchorA hanchorB
      (fun _ hngs => same_node_group hngs haCoord hbCoord (by rw [hpathA, hpathB, hpath]))

private theorem exactGraph_plain_path_from_box {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {labels : List MeasuredLabel} {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o labels graph0 = .ok graph)
    {i : Nat} {n : Node} {box : ModelBox}
    (hn : graph.nodes[i]? = some n) (hb : inp.boxes[i]? = some box)
    (hplain : n.border = 0) : n.clusterPath = Compound.path inp.boxes box := by
  cases hsource : graph0.nodes[i]? with
  | none =>
    have hbound := (List.getElem?_eq_some_iff.mp hn).1
    rw [exactGraph_length h] at hbound
    have houtside := List.getElem?_eq_none_iff.mp hsource
    omega
  | some source =>
    obtain ⟨nd, hd, hborder, hpath, _⟩ := exactGraph_node_key h hsource
    have he : nd = n := Option.some.inj (hd.symm.trans hn)
    subst nd
    obtain ⟨nodes, edges, titles, hprepared, _, hmetadata⟩ := measuredGraph_prepared_source h0
    rw [hprepared] at hsource
    obtain ⟨_, hbox, heq⟩ := fixedSizes_path_index inp hb
    obtain ⟨_, hsourcePath⟩ := prepare_plain_path_origin _ _ _ _ hmetadata hsource
      (hborder.symm.trans hplain) hbox
    exact hpath.trans (hsourcePath.trans heq)

/-- Border-0 boxes sharing a source-model parent are in one owner bucket.
This uses the actual measured and exact graph equations, not a restriction
on the intervening nodes of the pinned layer. -/
theorem exactGraph_sibling_cluster_paths {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {labels : List MeasuredLabel} {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o labels graph0 = .ok graph)
    {a b : Nat} {na nb : Node} {ba bb : ModelBox}
    (ha : graph.nodes[a]? = some na) (hb : graph.nodes[b]? = some nb)
    (hba : inp.boxes[a]? = some ba) (hbb : inp.boxes[b]? = some bb)
    (hpa : na.border = 0) (hpb : nb.border = 0) (hparent : ba.parent = bb.parent) :
    na.clusterPath = nb.clusterPath := by
  rw [exactGraph_plain_path_from_box h0 h ha hba hpa, exactGraph_plain_path_from_box h0 h hb hbb hpb]
  unfold Compound.path
  rw [hparent]

/-- The cross-axis inequality for the same-layer sibling pair selected by
the region scene's C2 check, with owner equality derived from the source boxes. -/
theorem componentRunR_region_sibling_order {P : Params} {exactIds : List String}
    {s : RegionSpec} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {labels : List MeasuredLabel} {graph0 graph cg' : Graph}
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hgraph : exactGraph P exactIds inp o labels graph0 = .ok graph)
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) graph comp candidate) labels orderOptions = .ok (cg', run))
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {i j a b keyA keyB : Nat} {na nb : Node} {ba bb : ModelBox}
    (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hpartA : comp[a]? = some keyA) (hpartB : comp[b]? = some keyB)
    (hna : graph.nodes[keyA]? = some na) (hnb : graph.nodes[keyB]? = some nb)
    (hboxA : inp.boxes[keyA]? = some ba) (hboxB : inp.boxes[keyB]? = some bb)
    (hpa : na.border = 0) (hpb : nb.border = 0) (hparent : ba.parent = bb.parent) :
    coordSep (min P.nodeGap P.clusterPad) run.coordinateProper a b ≤
      run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  obtain ⟨rs, ranks, budget, p0, labeled, pCoord, minimum, ord, widths, reserved,
    placed, q0, yt, ysMid, hs⟩ := componentRunR_stages hrun
  have hnodes : cg'.nodes = (componentCandidateR (some s) graph comp candidate).nodes := by
    rcases hs.hRank with ⟨_, _, _, _, heq, _⟩ | ⟨_, _, hrank⟩
    · rw [heq]
    · exact rankEquivalentR_nodes_eq hrank
  have hna' : cg'.nodes[a]? = some na := by
    rw [hnodes]
    exact component_node_lookupR hpartA hna
  have hnb' : cg'.nodes[b]? = some nb := by
    rw [hnodes]
    exact component_node_lookupR hpartB hnb
  have hpath := exactGraph_sibling_cluster_paths h0 hgraph hna hnb hboxA hboxB hpa hpb hparent
  exact componentRunR_region_same_owner_separated hrun hlayer hij ha hb hna' hnb' hpa hpb
    (congrArg List.getLast? hpath)

end Elegant.Layered.PipelineImpl

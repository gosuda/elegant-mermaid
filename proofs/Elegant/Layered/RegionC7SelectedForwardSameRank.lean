import Elegant.Layered.RegionC7SelectedForwardRank
import Elegant.Layered.RegionForwardAnchorOrigin
import Elegant.Layered.RegionC7SelectedCrossOwnerLoops
import Elegant.Layered.RegionC7ExactLaterLoops
import Elegant.Layered.RegionC7SelectedExteriorGroupOwnerLoops

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl RegionOrdinaryC6

private abbrev r7fsRank (run : Run) (e : Edge) : Int :=
  rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2

private abbrev r7fsBox (run : Run) (v : Nat) : Rect :=
  RouteImpl.boxRect run.proper run.xs run.ys v

private abbrev r7fsXGap (a b : Rect) : Prop :=
  a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x

private theorem r7fs_indexOfDistinct {row : List Nat} {i j a b : Nat}
    (ha : row[i]? = some a) (hb : row[j]? = some b) (hab : a ≠ b) : i ≠ j := by
  intro h
  rw [h] at ha
  exact hab (Option.some.inj (ha.symm.trans hb))

private theorem r7fs_sameTranslation_gap {ng cp shift : Int} {run : Run} {p : Proper}
    {layers : List (List Nat)} {xs : List Int} {row : List Nat} {a b : Nat}
    {na nb : ProperNode}
    (hcross : CoordsImpl.crossCoordsClusterWith ng cp p layers = .ok xs)
    (hrow : row ∈ layers) (ha : a ∈ row) (hb : b ∈ row) (hne : a ≠ b)
    (hca : p.nodes[a]? = some na) (hcb : p.nodes[b]? = some nb)
    (hpa : run.proper.nodes[a]? = some na) (hpb : run.proper.nodes[b]? = some nb)
    (hba : na.node.border = 0) (hbb : nb.node.border = 0)
    (hxa : run.xs.getD a 0 = xs.getD a 0 + shift)
    (hxb : run.xs.getD b 0 = xs.getD b 0 + shift) :
    r7fsXGap (r7fsBox run a) (r7fsBox run b) := by
  obtain ⟨hng, hcp, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
  have hgap : 1 ≤ min ng cp := Int.le_min.mpr ⟨hng, hcp⟩
  have half (w : Int) : Int.fdiv w 2 = w / 2 := Int.fdiv_eq_ediv_of_nonneg w (by decide)
  have extendedHalf (w e : Int) : Int.fdiv (w + 2 * e) 2 = w / 2 + e := by
    rw [half, Int.mul_comm 2 e]
    exact Int.add_mul_ediv_right w e (by decide)
  have hea : (0 : Int) ≤ na.node.loopExtent := Int.natCast_nonneg _
  have heb : (0 : Int) ≤ nb.node.loopExtent := Int.natCast_nonneg _
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  change (r7fsBox run a).x + (r7fsBox run a).w ≤ (r7fsBox run b).x ∨
    (r7fsBox run b).x + (r7fsBox run b).w ≤ (r7fsBox run a).x
  simp only [r7fsBox, RouteImpl.boxRect, RouteImpl.xAt, RouteImpl.nodeW, hpa, hpb, hxa, hxb, half]
  rcases Nat.lt_or_gt_of_ne (r7fs_indexOfDistinct hi hj hne) with hlt | hgt
  · have hs := crossCoordsClusterWith_plain_order hcross hrow hlt hi hj hca hba
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hca, hcb, extendedHalf] at hs
    exact Or.inl (by omega)
  · have hs := crossCoordsClusterWith_plain_order hcross hrow hgt hj hi hcb hbb
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hca, hcb, extendedHalf] at hs
    exact Or.inr (by omega)

private abbrev r7fsBucketLeft (P : Params) (root : Nat) (alloc : RegionAllocation) (g : Nat) : Int :=
  alloc.lefts.getD g 0 + (if g = root then 0 else regionInsetOf P)

private abbrev r7fsBucketRight (P : Params) (root : Nat)
    (pl : RegionPlacement) (alloc : RegionAllocation) (g : Nat) : Int :=
  r7fsBucketLeft P root alloc g + pl.buckets.widths.getD g 0

private theorem r7fs_differentBuckets_gap {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)} {xs : List Int}
    {reserved : List (Option Int)}
    (st : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length) (hmin : constrainR rm P p = .ok minimum)
    (hinset : 0 < regionInsetOf P) (hslot : 1 ≤ P.slot)
    {g a b : Nat} (hg : g ≤ rm.clusters.length)
    (ha : TrunkBranch st.placement.children g a) (hb : TrunkBranch st.placement.children g b)
    (hne : a ≠ b) :
    r7fsBucketRight P rm.clusters.length st.placement st.allocation a ≤
        r7fsBucketLeft P rm.clusters.length st.allocation b ∨
      r7fsBucketRight P rm.clusters.length st.placement st.allocation b ≤
        r7fsBucketLeft P rm.clusters.length st.allocation a := by
  let L (k : Nat) := st.allocation.lefts.getD k 0
  let W (k : Nat) := st.allocation.widths.getD k 0
  let A := r7fsBucketLeft P rm.clusters.length st.allocation
  let B := r7fsBucketRight P rm.clusters.length st.placement st.allocation
  have hchild {g c : Nat} (hc : c ∈ st.placement.children.getD g []) :
      c < rm.clusters.length := actualChild_bound st hparents hmin hc
  obtain ⟨hown, hlane, hloop⟩ := st.bucket_signs (by omega : 0 ≤ P.slot)
  have hwidth : ∀ k, 0 ≤ W k := by
    unfold W
    rw [allocationWidths_exact st]
    exact reserveWidths_nonnegative (by omega : 0 ≤ regionInsetOf P) hown hlane hloop
  have totals (lst : List Nat) : 0 ≤ (lst.map W).sum := by
    induction lst with
    | nil => simp
    | cons k ks ih => exact Int.add_nonneg (hwidth k) ih
  have inside {k d : Nat} (hk : k < rm.clusters.length)
      (path : TrunkBranch st.placement.children k d) : L k ≤ A d ∧ B d ≤ L k + W k := by
    have hd : d < rm.clusters.length := by
      revert hk
      induction path with
      | here => exact id
      | @step g c d hc _ ih => exact fun _ => ih (hchild hc)
    have hroom : regionInsetOf P + st.placement.buckets.widths.getD d 0 ≤ W d := by
      obtain ⟨_, _, ho, hlast, hchildren⟩ := (st.reservation_order hparents hmin).2 d
        (Nat.le_of_lt hd)
      have hsmall : d < st.placement.rm.clusters.length := by simpa only [st.hPlacement] using hd
      have hr := reserveWidths_room_from_last_writes (P := P) ho hsmall hlast hchildren
      have hchildrenWidths := totals (st.placement.children.getD d [])
      have hl := hlane d
      have hlo := hloop d
      change (2 * regionInsetOf P + st.placement.buckets.widths.getD d 0 +
        ((st.placement.children.getD d []).map (fun c => (reserveWidths st.placement P).getD c 0)).sum +
        laneExtentOf st.placement.buckets P.slot d ≤
          (reserveWidths st.placement P).getD d 0 - st.placement.buckets.loopWidth.getD d 0) at hr
      unfold W at hchildrenWidths ⊢
      rw [allocationWidths_exact st] at hchildrenWidths ⊢
      omega
    have halloc := actualBranch_budget st hparents hmin hinset hslot hk path
    have hbounds : L d ≤ A d ∧ B d ≤ L d + W d := by
      simp only [L, W, A, B, r7fsBucketLeft, r7fsBucketRight, ite_eq_right (Nat.ne_of_lt hd)]
      change regionInsetOf P + st.placement.buckets.widths.getD d 0 ≤
        st.allocation.widths.getD d 0 at hroom
      constructor <;> omega
    exact ⟨Int.le_trans halloc.1 hbounds.1, Int.le_trans hbounds.2 halloc.2⟩
  have beforeChild {k c : Nat} (hk : k ≤ rm.clusters.length)
      (hc : c ∈ st.placement.children.getD k []) : B k ≤ L c :=
    (actualChildBudget_inside st hparents hmin hinset hslot hk hc).1
  change B a ≤ A b ∨ B b ≤ A a
  revert hg hb hne
  induction ha with
  | here g =>
    intro hg hb hne
    cases hb with
    | here => exact (hne rfl).elim
    | @step _ c _ hc rest =>
      exact Or.inl (Int.le_trans (beforeChild hg hc) (inside (hchild hc) rest).1)
  | @step g c a hc left ih =>
    intro hg hb hne
    cases hb with
    | here => exact Or.inr (Int.le_trans (beforeChild hg hc) (inside (hchild hc) left).1)
    | @step _ d _ hd right =>
      by_cases hcd : c = d
      · subst d
        exact ih (Nat.le_of_lt (hchild hc)) right hne
      · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
        have hl := inside (hchild hc) left
        have hr := inside (hchild hd) right
        rcases Nat.lt_or_gt_of_ne (r7fs_indexOfDistinct hi hj hcd) with hij | hji
        · have hs := actualSiblingBudget_order st hparents hmin hinset hslot hg hi hj hij
          exact Or.inl (Int.le_trans hl.2 (Int.le_trans hs hr.1))
        · have hs := actualSiblingBudget_order st hparents hmin hinset hslot hg hj hi hji
          exact Or.inr (Int.le_trans hr.2 (Int.le_trans hs hl.1))

private theorem r7fs_active_sameRow_gap {P : Params} {exact : List Nat} {s : RegionSpec}
    {inp : Input} {o : Options} {candidate cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {order : OrderOptions} {rm : ComponentRegions} {k a v : Nat} {rank : Int} {na : ProperNode}
    {nv : Node} {row : List Nat}
    (hp : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P exact (some s) inp candidate labels order = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (ha : labelAnchorIndex run.proper k rank = some a) (hna : run.proper.nodes[a]? = some na)
    (hv : cg.nodes[v]? = some nv) (hbv : nv.border = 0)
    (hrow : row ∈ run.layers) (harow : a ∈ row) (hvrow : v ∈ row) :
    r7fsXGap (r7fsBox run a) (r7fsBox run v) := by
  obtain ⟨_, _, _, _, _, _, _, _, hrank, hnorm, hlab, hcoord, hmin, _, ⟨st⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  obtain ⟨hpreA, hplainA, hxA, _, _, hboundA, _⟩ :=
    componentRunR_selectedAnchor_origin hrun hactive hrank hnorm hlab hcoord st ha hna
  obtain ⟨nd, hpreV, hplainV, hproperV, hxV⟩ :=
    actualPlainNode_record hrun hactive hrank hnorm hlab hcoord st hv hbv
  have hboundV := (List.getElem?_eq_some_iff.mp hv).1
  have hne : a ≠ v := by omega
  have hparents := activeRegion_parent_count hactive
  let ga := st.groups.getD a 0
  let gv := st.groups.getD v 0
  by_cases hsame : ga = gv
  · obtain ⟨_, hmoveA⟩ := actualMember_shift st hparents hmin hpreA hplainA (show _ = ga from rfl)
    obtain ⟨_, hmoveV⟩ := actualMember_shift st hparents hmin hpreV hplainV (show _ = ga from hsame.symm)
    exact r7fs_sameTranslation_gap st.hCross hrow harow hvrow hne hpreA hpreV hna hproperV
      hplainA hplainV (hxA.trans hmoveA) (hxV.trans hmoveV)
  · have haPath := actualBranch_from_root st hparents hmin (actualMember_group_bound st hpreA)
    have hvPath := actualBranch_from_root st hparents hmin (actualMember_group_bound st hpreV)
    have hinset : 0 < regionInsetOf P := by
      have hpad := (checkedParams_sizing_nonneg hp).2.1
      have hb := checkedParams_clusterBorderW_ge_one hp
      unfold regionInsetOf
      omega
    have hslot := componentRunR_slot_pos hrun
    have hgap := r7fs_differentBuckets_gap st hparents hmin hinset hslot (Nat.le_refl _)
      haPath hvPath hsame
    have hA : r7fsBucketLeft P rm.clusters.length st.allocation ga ≤ (r7fsBox run a).x ∧
        (r7fsBox run a).x + (r7fsBox run a).w ≤
          r7fsBucketRight P rm.clusters.length st.placement st.allocation ga := by
      simpa only [r7fsBox, RouteImpl.boxRect, RouteImpl.xAt, RouteImpl.nodeW, hna, hxA] using!
        allocatedMember_crossHull st hparents hmin hpreA hplainA (show _ = ga from rfl)
    have hV : r7fsBucketLeft P rm.clusters.length st.allocation gv ≤ (r7fsBox run v).x ∧
        (r7fsBox run v).x + (r7fsBox run v).w ≤
          r7fsBucketRight P rm.clusters.length st.placement st.allocation gv := by
      simpa only [r7fsBox, RouteImpl.boxRect, RouteImpl.xAt, RouteImpl.nodeW, hproperV, hxV] using!
        allocatedMember_crossHull st hparents hmin hpreV hplainV (show _ = gv from rfl)
    rcases hgap with h | h
    · exact Or.inl (Int.le_trans hA.2 (Int.le_trans h hV.1))
    · exact Or.inr (Int.le_trans hV.2 (Int.le_trans h hA.1))

private theorem r7fs_sameRow_anchor_gap {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {o : Options} {candidate cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {order : OrderOptions} {k a v : Nat} {e : Edge} {first : MeasuredLabel}
    {na : ProperNode} {nv : Node} {row : List Nat}
    (hp : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P exact spec inp candidate labels order = .ok (cg, run))
    (he : cg.edges[k]? = some e) (hne : e.tail ≠ e.head)
    (hfirst : (routeLabels labels e.decl).head? = some first)
    (ha : labelAnchorIndex run.proper k (r7fsRank run e) = some a)
    (hna : run.proper.nodes[a]? = some na) (hv : cg.nodes[v]? = some nv) (hbv : nv.border = 0)
    (hrow : row ∈ run.layers) (harow : a ∈ row) (hvrow : v ∈ row) :
    r7fsXGap (r7fsBox run a) (r7fsBox run v) := by
  obtain ⟨_, _, _, p0, labeled, p, _, _, _, _, _, _, _, _, trace⟩ := componentRunR_stages hrun
  rcases trace.hPlaced with ⟨_, hcross, hlayers, _, hplace⟩ | ⟨rm, _, hsome, _, _⟩
  · have hcp : run.coordinateProper = p := trace.hCoordProper.trans hplace
    have hproxy := trace.hProxy
    rw [hplace] at hproxy
    have hpNode : ∀ {i : Nat} {nd : ProperNode}, p.nodes[i]? = some nd → nd.node.border = 0 →
        run.proper.nodes[i]? = some nd ∧ run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
      intro i nd hi hb
      refine ⟨?_, componentRunR_placement_xsR hrun (by rwa [hcp]) (by simp [hb])⟩
      rw [← trace.hDrop, OrderImpl.dropSynthetic_nodes]
      exact proxyWidths_plain_node hproxy hi hb
    obtain ⟨i, before, hi, hbefore, _, _⟩ := componentLabels_selected_size he hne hfirst trace.hLabels
    have hkey := labelAnchorIndex_node_edge hi hbefore
    have hplain := addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain trace.hNorm) trace.hLabels
    have hb : before.node.border = 0 := hplain before (List.mem_of_getElem? hbefore) (by simp [hkey])
    obtain ⟨ndA, hcA, hbA, _, _⟩ := regionCoordinatePlainDims P exact spec hbefore hb
    have hvOrig := addLabelNodes_untouched_node trace.hLabels (normalize_node_record trace.hNorm hv) rfl
    obtain ⟨ndV, hcV, hbV, _, _⟩ := regionCoordinatePlainDims P exact spec hvOrig hbv
    rw [trace.hCoord] at hcA hcV
    have hneq : i ≠ v := by
      intro h
      rw [h, hvOrig] at hbefore
      rw [← Option.some.inj hbefore] at hkey
      cases hkey
    obtain ⟨hAlign0, hwf⟩ := normalize_node_rank_alignment trace.hNorm
    obtain ⟨hRank, hKeys⟩ := addLabelNodes_anchor_keys trace.hLabels
    have hLen : labeled.nodes.length = p0.nodes.length := by
      simpa only [List.length_map] using congrArg List.length hKeys
    have hAlign : labeled.nodes.length = labeled.rank.length := by rw [hLen, hRank, hAlign0]
    obtain ⟨ht, hh, _⟩ := RankImpl.wellformed_spec hwf e (List.mem_of_getElem? he)
    have ht' : e.tail < labeled.rank.length := by
      rw [← hAlign, hLen]
      exact Nat.lt_of_lt_of_le ht (normalize_nodes_length_le trace.hNorm)
    have hh' : e.head < labeled.rank.length := by
      rw [← hAlign, hLen]
      exact Nat.lt_of_lt_of_le hh (normalize_nodes_length_le trace.hNorm)
    have hprefix := coordinateGraphR_label_prefix P exact spec labeled
    rw [trace.hCoord] at hprefix
    have hpIndex := labelAnchorIndex_prefix hAlign hprefix.1 hprefix.2 hi
    obtain ⟨extra, hr⟩ := hprefix.2
    have hFinalKey : run.proper.nodes.map ProperNode.edge = p.nodes.map ProperNode.edge := by
      rw [← trace.hDrop, OrderImpl.dropSynthetic_nodes, proxyWidths_edge_keys hproxy]
    have hFinalRank : run.proper.rank = p.rank := by
      rw [← trace.hDrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]
    have htOut : rk run.proper.rank e.tail = rk labeled.rank e.tail := by
      rw [hFinalRank, hr, NormalizeImpl.rk_append_left ht']
    have hhOut : rk run.proper.rank e.head = rk labeled.rank e.head := by
      rw [hFinalRank, hr, NormalizeImpl.rk_append_left hh']
    have hiOut : labelAnchorIndex run.proper k (r7fsRank run e) = some i := by
      dsimp only [r7fsRank]
      rw [htOut, hhOut]
      unfold labelAnchorIndex at hpIndex ⊢
      rwa [hFinalKey, hFinalRank]
    have eIndex := Option.some.inj (ha.symm.trans hiOut)
    subst a
    obtain ⟨hpA, hxA⟩ := hpNode hcA hbA
    obtain ⟨hpV, hxV⟩ := hpNode hcV hbV
    rw [← hlayers] at hcross
    exact r7fs_sameTranslation_gap (shift := 0) hcross hrow harow hvrow hneq hcA hcV hpA hpV
      hbA hbV (by simpa only [Int.add_zero] using hxA) (by simpa only [Int.add_zero] using hxV)
  · have hactive := trace.hRs.trans (congrArg Except.ok hsome)
    cases spec with
    | none => cases hactive
    | some s => exact r7fs_active_sameRow_gap (o := o) hp hrun hactive ha hna hv hbv hrow harow hvrow

def R7_SelectedForwardSamePlainRank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b) : Prop :=
  pair.edge.tail ≠ pair.edge.head ∧ pair.edge.reversed = false ∧
    (∃ node, pair.cg.nodes[pair.target]? = some node ∧ node.border = 0) ∧
    (rk pair.run.proper.rank pair.target).toNat = (r7fsRank pair.run pair.edge).toNat

theorem r7Selected_forwardSamePlainRank_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (hpair : R7_SelectedForwardSamePlainRank pair) :
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  obtain ⟨hne, hrev, ⟨node, hv, hb⟩, hsame⟩ := hpair
  let spec := r7Eff idSets o execution.params execution.lines pair.rs
  have hrun : componentRunR execution.params (exactDecls exactIds inp) spec inp
      (componentCandidateR spec execution.graph pair.part.1 pair.candidate)
      execution.measured (candidateOrder pair.candidate) = .ok (pair.cg, pair.run) := pair.run_eq
  obtain ⟨first, anchor, hfirst, hfind, henv⟩ := forward_envelope_eq hne hrev pair.envelope_eq
  obtain ⟨a, na, ha, hna, hw, _⟩ := componentRunR_forward_anchor_size hrun pair.edge_eq hne hfirst
  have ha' : labelAnchorIndex pair.run.proper pair.edgeIndex (r7fsRank pair.run pair.edge) = some a := ha
  have hindex : anchor.2 = a := by
    rw [labelAnchorIndex_eq] at ha
    simpa only [hfind, Option.map_some, Option.some.injEq] using ha
  have hrank := (labelAnchorIndex_rank ha').1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, trace⟩ := componentRunR_stages hrun
  have hlayers : RouteImpl.layersOk pair.run.proper pair.run.layers = true := by
    rcases trace.hLanes with ⟨_, h⟩ | ⟨_, h⟩
    · exact (RouteImpl.routeWithLanes_geometry h).1
    · exact (rcbRouteWithLanesR_geometry h).1
  have hcover := (RouteImpl.layersOk_spec hlayers).2.2.2.1
  obtain ⟨row, hrow, harow, _⟩ := hcover a (List.getElem?_eq_some_iff.mp hna).1
  obtain ⟨vrow, hvrow, htrow, _⟩ := hcover pair.target pair.target_size
  rw [hsame, ← hrank, hrow] at hvrow
  have htrow' : pair.target ∈ row := (Option.some.inj hvrow).symm ▸ htrow
  have hsep := r7fs_sameRow_anchor_gap (o := o) execution.checked hrun pair.edge_eq hne hfirst
    ha' hna hv hb (List.mem_of_getElem? hrow) harow htrow'
  have hfirstMem := List.mem_of_head? hfirst
  have hg := (execution.measured_nonnegR first (List.mem_filter.mp hfirstMem).1).2.2
  have hstack := (List.of_mem_zip pair.stack).2
  have hx : pair.rect.x = (r7fsBox pair.run a).x + first.gutter := by
    rw [(stackRects_entry hstack).1, henv, hindex] <;> rfl
  have hrectW := stackRect_width_le hstack
  rw [stackSize_width_eq] at hw
  have haW : (r7fsBox pair.run a).w = na.node.w := by
    simp only [r7fsBox, RouteImpl.boxRect, RouteImpl.nodeW, hna]
  change R7_OverlapRowsXGap pair.rect (r7fsBox pair.run pair.target)
  intro _ _ _
  rcases hsep with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

def R7_SelectedRouteAfterForwardPlainRanks {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (pair : R7_SelectedRoutePair execution l b),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel → ¬ R7_SelectedSettledLoop pair →
    ¬ R7_SelectedReversedPlainPair pair → ¬ R7_SelectedForwardDifferentPlainRank pair →
    ¬ R7_SelectedForwardSamePlainRank pair →
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target)

theorem r7SelectedRoute_iff_afterForwardPlainRanks {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    R7_SelectedRouteAfterForwardDifferentPlainRank execution ↔
      R7_SelectedRouteAfterForwardPlainRanks execution := by
  classical
  constructor
  · intro h l b pair hl hb he ho hloop hrev hdiff _
    exact h l b pair hl hb he ho hloop hrev hdiff
  · intro h l b pair hl hb he ho hloop hrev hdiff
    by_cases hsame : R7_SelectedForwardSamePlainRank pair
    · exact r7Selected_forwardSamePlainRank_clear pair hsame
    · exact h l b pair hl hb he ho hloop hrev hdiff hsame

theorem r7Selected_forward_of_plainTarget {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (hplain : ∃ node : Node, pair.cg.nodes[pair.target]? = some node ∧ node.border = 0)
    (hne : pair.edge.tail ≠ pair.edge.head) (hfwd : pair.edge.reversed = false) :
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  by_cases hsame : (rk pair.run.proper.rank pair.target).toNat =
      (rk pair.run.proper.rank pair.edge.tail + Int.fdiv
        (rk pair.run.proper.rank pair.edge.head - rk pair.run.proper.rank pair.edge.tail) 2).toNat
  · exact r7Selected_forwardSamePlainRank_clear pair ⟨hne, hfwd, hplain, hsame⟩
  · exact r7Selected_forwardDifferentPlainRank_clear pair ⟨hne, hfwd, hplain, hsame⟩

theorem r7Selected_nonloop_of_plainTarget {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (hplain : ∃ node : Node, pair.cg.nodes[pair.target]? = some node ∧ node.border = 0)
    (hne : pair.edge.tail ≠ pair.edge.head) :
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  cases hrev : pair.edge.reversed with
  | false => exact r7Selected_forward_of_plainTarget pair hplain hne hrev
  | true => exact r7Selected_reversedPlain_clear pair ⟨hne, hrev, hplain⟩

def R7_SelectedUnsettledLoopClearance {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (pair : R7_SelectedRoutePair execution l b),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    (∃ node : Node, pair.cg.nodes[pair.target]? = some node ∧ node.border = 0) →
    pair.edge.tail = pair.edge.head → ¬ R7_SelectedSettledLoop pair →
    ¬ R7_SelectedActiveCrossOwnerPlainLoop pair →
    ¬ R7_SelectedExactLaterPlainLoop pair →
    ¬ (WellFormed (inputModel inp o) ∧ framedParents inp = true ∧
      ∃ (s : RegionSpec) (owner : Node),
        r7Eff idSets o execution.params execution.lines pair.rs = some s ∧
        pair.cg.nodes[pair.edge.tail]? = some owner ∧ owner.border = -2) →
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target)

theorem r7Selected_route_from_unsettledLoops {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (loops : R7_SelectedUnsettledLoopClearance execution)
    (l : SceneLabel) (b : Box) (pair : R7_SelectedRoutePair execution l b)
    (hl : l ∈ res.scene.labels) (hb : b ∈ res.scene.layoutDump.boxes)
    (he : b.exclusive = true) (ho : b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel)
    (hplain : ∃ node : Node, pair.cg.nodes[pair.target]? = some node ∧ node.border = 0)
    (hunsettled : ¬ R7_SelectedSettledLoop pair) :
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  classical
  by_cases hloop : pair.edge.tail = pair.edge.head
  · by_cases hcross : R7_SelectedActiveCrossOwnerPlainLoop pair
    · exact r7Selected_activeCrossOwnerPlainLoop_clear pair hcross
    by_cases hlater : R7_SelectedExactLaterPlainLoop pair
    · obtain ⟨hself, hexact, horder, nu, nv, hu, hv, hbu, hbv⟩ := hlater
      exact r7Selected_exactLaterPlainLoop_clear pair hu hv hbu hbv hexact hself horder
    by_cases hgroup : WellFormed (inputModel inp o) ∧ framedParents inp = true ∧
        ∃ (s : RegionSpec) (owner : Node),
          r7Eff idSets o execution.params execution.lines pair.rs = some s ∧
          pair.cg.nodes[pair.edge.tail]? = some owner ∧ owner.border = -2
    · obtain ⟨hwf, hfp, s, owner, hs, hu, howner⟩ := hgroup
      obtain ⟨target, hv, htarget⟩ := hplain
      by_cases hdesc : owner.decl ∈ target.clusterPath
      · exact r7Selected_activeGroupLoop_xgap hwf hfp pair
          ⟨hloop, s, owner, target, hs, hu, howner, hv, htarget, Or.inl hdesc⟩
      by_cases hearlier : (rk pair.run.proper.rank pair.target).toNat <
          (rk pair.run.proper.rank pair.edge.tail).toNat
      · exact r7Selected_activeGroupLoop_xgap hwf hfp pair
          ⟨hloop, s, owner, target, hs, hu, howner, hv, htarget, Or.inr hearlier⟩
      have hexterior : target.clusterPath.contains owner.decl = false :=
        Bool.eq_false_iff.mpr (fun h => hdesc (List.contains_iff_mem.mp h))
      exact r7Selected_activeExteriorGroupLoop_xgap hwf hfp pair
        ⟨hloop, s, owner, target, hs, hu, howner, hv, htarget, hexterior, Nat.le_of_not_gt hearlier⟩
    exact loops l b pair hl hb he ho hplain hloop hunsettled hcross hlater hgroup
  · exact r7Selected_nonloop_of_plainTarget pair hplain hloop

theorem r7Selected_routeWithPlainTarget_iff_unsettledLoops {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    R7_SelectedRouteWithPlainTarget execution ↔ R7_SelectedUnsettledLoopClearance execution := by
  constructor
  · intro route l b pair hl hb he ho hplain _ hunsettled _ _ _
    exact route l b pair hl hb he ho hplain hunsettled
  · exact fun loops => r7Selected_route_from_unsettledLoops execution loops

end Elegant.Layered.PipelineImpl

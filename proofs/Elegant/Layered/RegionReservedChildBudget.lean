import Elegant.Layered.RegionActiveFrameLabels
import Elegant.Layered.RegionSharedAllocation

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem prefixWidth_nonnegative (w : List Int) (h : ∀ g, 0 ≤ w.getD g 0)
    (row : List Nat) : 0 ≤ (row.map fun c => w.getD c 0).sum := by
  induction row with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.sum_cons]
    exact Int.add_nonneg (h c) ih

private theorem prefixWidth_child_le (w : List Int) (h : ∀ g, 0 ≤ w.getD g 0)
    {row : List Nat} {k child : Nat} (hchild : row[k]? = some child) :
    ((row.take k).map fun c => w.getD c 0).sum + w.getD child 0 ≤
      (row.map fun c => w.getD c 0).sum := by
  induction row generalizing k with
  | nil => simp at hchild
  | cons c cs ih =>
    cases k with
    | zero =>
      have he : c = child := Option.some.inj hchild
      subst c
      simp only [List.take_zero, List.map_nil, List.sum_nil, Int.zero_add,
        List.map_cons, List.sum_cons]
      have hsum := prefixWidth_nonnegative w h cs
      omega
    | succ k =>
      have hk := ih (by simpa only [List.getElem?_cons_succ] using hchild)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

/-- The budget proof is for one real parent and one selected child. It bounds
that child's full reserved footprint, not just its frame or its own member bucket.
The start of the lane band is the actual cursor formula of `allocateGroup`. -/
theorem RegionCrossAllocationStages.childBudget_precedes_laneBand
    {P : Params} {rm : ComponentRegions} {cg : Graph} {labels : List MeasuredLabel}
    {p placed : Proper} {minimum : RegionConstraints} {layers pinned : List (List Nat)}
    {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    {s : RegionSpec} {inp : Input} {candidate : Graph} {o : Options}
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hparams : checkedParams o.profile inp.kind = .ok P) (hslot : 0 ≤ P.slot)
    (hmin : constrainR rm P p = .ok minimum)
    {owner child k : Nat} (howner : owner < rm.clusters.length)
    (hchild : (stages.placement.children.getD owner [])[k]? = some child) :
    let pl := stages.placement
    let w := reserveWidths pl P
    let ownerX := stages.allocation.lefts.getD owner 0
    let childX := ownerX + regionInsetOf P + pl.buckets.widths.getD owner 0 +
      (((pl.children.getD owner []).take k).map fun c => w.getD c 0).sum
    childX + w.getD child 0 ≤ ownerX + w.getD owner 0 - pl.buckets.loopWidth.getD owner 0 -
      regionInsetOf P - laneExtentOf pl.buckets P.slot owner := by
  dsimp only
  have hpad := (checkedParams_sizing_nonneg hparams).2.1
  have hb := checkedParams_clusterBorderW_ge_one hparams
  have hinset : 0 ≤ regionInsetOf P := by unfold regionInsetOf; omega
  obtain ⟨hown, hlane, hloop⟩ := stages.bucket_signs hslot
  have hwidth := reserveWidths_nonnegative (pl := stages.placement) hinset hown hlane hloop
  have hparents := activeRegion_parent_count hactive
  obtain ⟨_, horder⟩ := stages.reservation_order hparents hmin
  obtain ⟨pre, post, hsplit, hlast, hread⟩ := horder owner (Nat.le_of_lt howner)
  have hownerPl : owner < stages.placement.rm.clusters.length := by
    simpa only [stages.hPlacement] using howner
  have hroom := reserveWidths_room_from_last_writes (pl := stages.placement) (P := P)
    hsplit hownerPl hlast hread
  dsimp only at hroom
  have hprefix := prefixWidth_child_le _ hwidth hchild
  omega

/-- The reserved border-center formulas imply the emitted frame's right edge.
The remaining bridge is these formulas at final `Run.proper`/`Run.xs` lookups,
not an inequality involving an arbitrary frame. -/
theorem activeFrame_right_of_side_centers {P : Params} {cg : Graph} {run : Run}
    {pos : Nat} {frame : Node} {left right : Int}
    (hnode : cg.nodes[pos]? = some frame) (hgroup : frame.border = -2)
    (hb : 0 ≤ P.clusterBorderW) (hright : 0 ≤ right)
    (hroom : left + P.clusterBorderW ≤ right)
    (hside : ∀ {i : Nat} {side : ProperNode}, run.proper.nodes[i]? = some side →
      (side.node.border = -1 ∨ side.node.border = 1) →
      side.node.clusterPath.getLast? = some frame.decl →
      side.node.w = P.clusterBorderW ∧
      run.xs.getD i 0 = if side.node.border = -1 then left + Int.tdiv P.clusterBorderW 2
        else right - P.clusterBorderW + Int.tdiv P.clusterBorderW 2) :
    (frameRect P cg run pos).x + (frameRect P cg run pos).w ≤ right := by
  have hhalf : Int.tdiv P.clusterBorderW 2 = Int.fdiv P.clusterBorderW 2 := by
    rw [Int.tdiv_eq_ediv_of_nonneg hb, Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have hbounds : (boundsOf (groupBorderRects cg run frame.decl) []).right ≤ right := by
    apply boundsOf_right_le_of_all hright
    intro rect hrect
    obtain ⟨i, side, hi, hkind, hpath, rfl⟩ := groupBorderRects_inv hrect
    obtain ⟨hw, hx⟩ := hside hi hkind hpath
    change run.xs.getD i 0 - Int.fdiv (RouteImpl.nodeW run.proper i) 2 +
      RouteImpl.nodeW run.proper i ≤ right
    simp only [RouteImpl.nodeW, hi, hw]
    rw [hx, hhalf]
    rcases hkind with hl | hr
    · rw [hl, ite_eq_left rfl]
      omega
    · rw [hr, ite_eq_right (by decide : (1 : Int) ≠ -1)]
      omega
  rw [frameRect_group_span hnode hgroup]
  dsimp only
  omega

/-- The exact remaining coordinate interface for a parent-owned allocated lane
versus its direct child. The frame condition is on its emitted border hull,
not an assumed disjointness, containment or validator result. -/
def ActiveReservedChildCoordinates (P : Params) (pl : RegionPlacement) (a : RegionAllocation)
    (cg : Graph) (run : Run) (owner child childSlot edge pos : Nat) (laneX : Int) : Prop :=
  let w := reserveWidths pl P
  let ownerX := a.lefts.getD owner 0
  let childEnd := a.lefts.getD child 0 + w.getD child 0
  a.lefts.getD child 0 = ownerX + regionInsetOf P + pl.buckets.widths.getD owner 0 +
      (((pl.children.getD owner []).take childSlot).map fun c => w.getD c 0).sum ∧
  a.lanes.getD edge none = some laneX ∧
  ownerX + w.getD owner 0 - pl.buckets.loopWidth.getD owner 0 - regionInsetOf P -
      laneExtentOf pl.buckets P.slot owner + P.slot ≤ laneX ∧
  (frameRect P cg run pos).x + (frameRect P cg run pos).w ≤ childEnd

/-- Once the stable child/lane writes and the side-marker hull are related to
the reservation, disjointness follows with no rank assumptions. Both the
label and the frame are the ones used by `placeComponentExact`. -/
theorem RegionCrossAllocationStages.reservedChildReversedLabel_disjoint
    {P : Params} {exact : List Nat} {s : RegionSpec} {inp : Input} {o : Options}
    {candidate cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {rm : ComponentRegions} {p : Proper} {minimum : RegionConstraints} {layers : List (List Nat)}
    {reserved : List (Option Int)}
    (hrun : componentRunR P exact (some s) inp candidate labels orderOptions = .ok (cg, run))
    (hactive : newComponentRegions (some s) P inp candidate = .ok (some rm))
    (hparams : checkedParams o.profile inp.kind = .ok P)
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    (hmin : constrainR rm P p = .ok minimum)
    {owner child k edge pos index : Nat} {rect : Rect} {source : MeasuredLabel} {e : Edge}
    (howner : owner < rm.clusters.length)
    (hchild : (stages.placement.children.getD owner [])[k]? = some child)
    (hslot : 0 ≤ cg.slot)
    (hmem : (index, rect) ∈ placedLabels P cg run labels)
    (huniq : (labels.map (·.index)).Nodup)
    (hsource : source ∈ labels) (hindex : source.index = index)
    (hfind : cg.edges.findIdx? (fun x => x.decl == source.edge) = some edge)
    (hedge : cg.edges[edge]? = some e) (htail : e.tail ≠ e.head) (hrev : e.reversed = true)
    (hregionRouter : routeWithLanesR P.slot run.proper run.layers run.xs
      (cg.edges.map (·.reversed)) (cg.edges.map fun e => (stackSize cg.slot (routeLabels labels e.decl)).width)
      reserved = .ok run.lanes)
    {laneX : Int}
    (hcoords : ActiveReservedChildCoordinates P stages.placement stages.allocation cg run
      owner child k edge pos laneX) :
    Disjoint (frameRect P cg run pos) rect := by
  have hslotP : 0 ≤ P.slot := by have := componentRunR_slot_pos hrun; omega
  have hcut := stages.childBudget_precedes_laneBand hactive hparams hslotP hmin howner hchild
  dsimp only at hcut
  obtain ⟨hleft, hreserve, hband, hframe⟩ := hcoords
  obtain ⟨lane, hlane, hkey, hx⟩ :=
    placedLabels_reversed_lane_x hmem huniq hsource hindex hfind hedge htail hrev
  have hfinal : reserved.getD edge none = some laneX := by rw [stages.hLanes]; exact hreserve
  have hactual := routeWithLanesR_label_lane_origin hregionRouter (List.mem_of_find?_eq_some hlane)
  rw [hkey, hfinal] at hactual
  change lane.lane = laneX at hactual
  exact rect_disjoint_of_x (Or.inl (by omega))

end Elegant.Layered.PipelineImpl

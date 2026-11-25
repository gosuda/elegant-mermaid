import Elegant.Layered.RegionFlatC7
import Elegant.Layered.RegionSiblingSameLayer
import Elegant.Layered.RegionDifferentLayerClearance
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.RegionBaseExecutedValidity
import Elegant.Layered.RegionBucketBounds
import Elegant.Layered.RegionFixedBoxDominance

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem loopSizes_orient_zip {labels : List MeasuredLabel} {v : Nat} {slot : Int}
    (edges : List Edge) (f : Edge × Nat → Edge)
    (hf : ∀ q, (f q).decl = q.1.decl ∧
      ((f q).tail == v && (f q).head == v) = (q.1.tail == v && q.1.head == v))
    (start : Nat) :
    loopSizes ((edges.zipIdx start).map f) labels v slot = loopSizes edges labels v slot := by
  induction edges generalizing start with
  | nil => rfl
  | cons e rest ih =>
    have hrest := ih (start + 1)
    unfold loopSizes at hrest ⊢
    rw [List.zipIdx_cons, List.map_cons]
    unfold loopEdges at hrest ⊢
    obtain ⟨hdecl, htest⟩ := hf (e, start)
    simp only [List.filter_cons, htest]
    by_cases hself : (e.tail == v && e.head == v) = true
    · simp only [ite_eq_left hself, List.map_cons, hdecl, hrest]
    · simp only [ite_eq_right hself, hrest]

theorem componentRunR_loopSizes_eq {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    (v : Nat) (slot : Int) :
    loopSizes cg'.edges labels v slot = loopSizes cg.edges labels v slot := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, h⟩
  · rw [he]
  · unfold rankEquivalentR at h
    dsimp only at h
    split at h
    · simp only [bind, Except.bind] at h
      cases h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      have he := congrArg (fun q : List Int × Graph × Bool => q.2.1.edges) (Except.ok.inj h)
      dsimp only at he
      rw [← he]
      apply loopSizes_orient_zip
      intro q
      split
      · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl⟩
        · exact ⟨rfl, Bool.and_comm _ _⟩

theorem componentCandidateR_loopSizes_preserved (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (hn : comp.Nodup) (candidate v : Nat) (hv : v < comp.length)
    (labels : List MeasuredLabel) (slot : Int) :
    loopSizes (componentCandidateR spec g comp candidate).edges labels v slot =
      loopSizes g.edges labels comp[v] slot := by
  cases spec with
  | none => exact componentCandidate_loopSizes_preserved g comp hn candidate v hv labels slot
  | some s =>
    rw [← componentGraph_loopSizes_preserved g comp hn v hv labels slot]
    refine Eq.trans (b := loopSizes ((componentGraph g comp).edges.map Edge.original)
      labels v slot) ?_ ?_
    · simp only [componentCandidateR]
      apply loopSizes_orient_zip
      intro q
      split
      · split
        · exact ⟨rfl, Bool.and_comm _ _⟩
        · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, Bool.and_comm _ _⟩
        · exact ⟨rfl, rfl⟩
    · have h := loopSizes_orient_zip (labels := labels) (v := v) (slot := slot)
        (componentGraph g comp).edges (fun q => q.1.original) (fun q => by
          unfold Edge.original
          split
          · exact ⟨rfl, Bool.and_comm _ _⟩
          · exact ⟨rfl, rfl⟩) 0
      have hmap :
          (((componentGraph g comp).edges.zipIdx 0).map fun q => q.1.original) =
            (componentGraph g comp).edges.map Edge.original := by
        change (((componentGraph g comp).edges.zipIdx 0).map (Edge.original ∘ Prod.fst)) = _
        rw [← List.map_map, List.zipIdx_map_fst]
      rwa [hmap] at h

private theorem plain_frame_eq_run_box {P : Params} {cg : Graph} {run : Run}
    {v : Nat} {source : Node} (hv : cg.nodes[v]? = some source) (hb : source.border = 0)
    (hlen : v < run.proper.nodes.length) :
    frameRect P cg run v = RouteImpl.boxRect run.proper run.xs run.ys v := by
  apply plain_frame_eq_boxRect P cg run v hlen
  simp [List.getD_eq_getElem?_getD, hv, hb]

theorem componentRunR_loopFootprint_miss_plain_self {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {u : Nat} {source : Node} (hu : cg'.nodes[u]? = some source) (hb : source.border = 0) :
    ¬ (loopFootprintExt cg' run labels u).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys u) := by
  have hlen := componentRunR_original_nodes_covered hrun u (List.getElem?_eq_some_iff.mp hu).1
  have hframe := plain_frame_eq_run_box (P := default) hu hb hlen
  unfold loopFootprintExt
  rw [hframe]
  unfold Rect.meetsInterior
  dsimp only
  omega

private theorem plain_run_cross_geometry {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    1 ≤ min P.nodeGap P.clusterPad ∧
      ∀ {i : Nat} {source : Node}, cg'.nodes[i]? = some source → source.border = 0 →
        ∃ n, run.coordinateProper.nodes[i]? = some n ∧ run.proper.nodes[i]? = some n ∧
          n.node.border = 0 ∧ run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
  cases spec with
  | some s => exact componentRunR_region_plain_cross_geometry hrun
  | none =>
    obtain ⟨rs, _, _, _, _, _, _, _, _, _, placed, _, _, _, stages⟩ :=
      componentRunR_stages hrun
    have hnone : rs = none := (Except.ok.inj stages.hRs).symm
    rcases stages.hPlaced with ⟨_, hcross, _, _, he⟩ | ⟨_, _, hsome, _, _⟩
    · obtain ⟨hng, hcp, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
      refine ⟨Int.le_min.mpr ⟨hng, hcp⟩, ?_⟩
      intro i source hsource hb
      obtain ⟨n, hn, hnBorder, _, _⟩ :=
        regionCoordinatePlainDims P exact none
          (addLabelNodes_untouched_node stages.hLabels
            (normalize_node_record stages.hNorm hsource) rfl) hb
      have hplaced : placed.nodes[i]? = some n := by rwa [he, ← stages.hCoord]
      have hcoord : run.coordinateProper.nodes[i]? = some n := by
        rwa [stages.hCoordProper]
      have hnonproxy : ¬ (n.node.border = -2 ∨ n.node.border = 2) := by simp [hnBorder]
      have hproper : run.proper.nodes[i]? = some n := by
        rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
        exact ((proxyWidths_rel stages.hProxy).2.2.2.2.2 i n hplaced hnonproxy).1
      exact ⟨n, hcoord, hproper, hnBorder, componentRunR_placement_xsR hrun hcoord hnonproxy⟩
    · rw [hnone] at hsome
      cases hsome

private theorem plain_run_order_gap {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {i j a b : Nat} {na nb : Node} (hij : i < j)
    (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hna : cg'.nodes[a]? = some na) (hnb : cg'.nodes[b]? = some nb)
    (hpa : na.border = 0) (hpb : nb.border = 0)
    (howner : spec.isSome = true → na.clusterPath.getLast? = nb.clusterPath.getLast?) :
    CoordsImpl.coordSep (min P.nodeGap P.clusterPad) run.coordinateProper a b ≤
      run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  cases spec with
  | some s =>
    exact componentRunR_region_same_owner_separated hrun hlayer hij ha hb hna hnb hpa hpb
      (howner rfl)
  | none =>
    obtain ⟨rs, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ :=
      componentRunR_stages hrun
    have hnone : rs = none := (Except.ok.inj stages.hRs).symm
    rcases stages.hPlaced with ⟨_, hcross, hlayers, _, he⟩ | ⟨_, _, hsome, _, _⟩
    · obtain ⟨_, hgeom⟩ := plain_run_cross_geometry hrun
      obtain ⟨_, hcoord, _, hborder, _⟩ := hgeom hna hpa
      rw [← he, ← stages.hCoordProper, ← hlayers] at hcross
      exact crossCoordsClusterWith_plain_order hcross hlayer hij ha hb hcoord hborder
    · rw [hnone] at hsome
      cases hsome

theorem componentRunR_loopFootprint_miss_plain_same_rank {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {u v : Nat} {nu nv : Node} (hu : cg'.nodes[u]? = some nu) (hv : cg'.nodes[v]? = some nv)
    (hbu : nu.border = 0) (hbv : nv.border = 0)
    (howner : spec.isSome = true → nu.clusterPath.getLast? = nv.clusterPath.getLast?)
    {layer : List Nat} (hlayer : layer ∈ run.layers) (hmu : u ∈ layer) (hmv : v ∈ layer)
    (hwidth : (loopFootprintExt cg' run labels u).w ≤
      ((run.coordinateProper.nodes.getD u default).node.loopExtent : Int)) :
    ¬ (loopFootprintExt cg' run labels u).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  by_cases he : u = v
  · subst v
    exact componentRunR_loopFootprint_miss_plain_self hrun hu hbu
  obtain ⟨hgap, hgeom⟩ := plain_run_cross_geometry hrun
  obtain ⟨a, hca, hpa, _, hxa⟩ := hgeom hu hbu
  obtain ⟨b, hcb, hpb, _, hxb⟩ := hgeom hv hbv
  have hframe := plain_frame_eq_run_box (P := default) hu hbu
    (List.getElem?_eq_some_iff.mp hpa).1
  have hleft : (loopFootprintExt cg' run labels u).x =
      (RouteImpl.boxRect run.proper run.xs run.ys u).x +
        (RouteImpl.boxRect run.proper run.xs run.ys u).w := by
    simp only [loopFootprintExt, hframe]
  simp only [List.getD_eq_getElem?_getD, hca, Option.getD_some] at hwidth
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmu
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmv
  have hij : i ≠ j := fun h => he (Option.some.inj ((h ▸ hi).symm.trans hj))
  have half (w : Int) : Int.fdiv w 2 = w / 2 := Int.fdiv_eq_ediv_of_nonneg w (by decide)
  have half_with_extent (w extent : Int) :
      Int.fdiv (w + 2 * extent) 2 = w / 2 + extent := by
    rw [half, Int.mul_comm 2 extent]
    exact Int.add_mul_ediv_right w extent (by decide)
  have hea : (0 : Int) ≤ a.node.loopExtent := Int.natCast_nonneg _
  have heb : (0 : Int) ≤ b.node.loopExtent := Int.natCast_nonneg _
  unfold Rect.meetsInterior
  rw [hleft]
  simp only [RouteImpl.boxRect, RouteImpl.xAt, RouteImpl.nodeW, hpa, hpb, hxa, hxb, half]
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · have hs := plain_run_order_gap hrun hlayer hlt hi hj hu hv hbu hbv howner
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hca, hcb, half_with_extent] at hs
    omega
  · have hs := plain_run_order_gap hrun hlayer hgt hj hi hv hu hbv hbu
      (fun hs => (howner hs).symm)
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hca, hcb, half_with_extent] at hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, yt, _, stages⟩ := componentRunR_stages hrun
    obtain ⟨y, top⟩ := yt
    have hsizes : CoordsImpl.sizesNonneg run.coordinateProper = true := by
      rw [stages.hCoordProper]
      exact (CoordsImpl.rankCoordsWith_spec stages.hYt).2.2.2.2.1
    have hwa := (sizesNonneg_lookup hsizes u a hca).1
    omega

theorem componentRunR_loopFootprint_rank_cap_of_requiredHeight
    {P : Params} {exactIds : List String} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run))
    {u : Nat} {node : Node} (hu : cg.nodes[u]? = some node) (hb : node.border = 0)
    (hslot : 0 ≤ cg'.slot)
    (hsize : Loops.requiredHeight cg'.slot (loopSizes cg'.edges labels u cg'.slot) ≤ node.h) :
    ∀ (s : Nat) (above : List Nat),
      (rk run.proper.rank u).toNat < s → run.layers[s]? = some above →
      (loopFootprintExt cg' run labels u).y + (loopFootprintExt cg' run labels u).h ≤
        run.top.getD s 0 := by
  intro s layer hlt hl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  have hnodes : cg'.nodes = cg.nodes := by
    rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, h⟩
    · rw [he]
    · exact rankEquivalentR_nodes_eq h
  have hu' : cg'.nodes[u]? = some node := by rwa [hnodes]
  obtain ⟨hband, hsep⟩ := componentRunR_plain_rank_bands hrun
  obtain ⟨ownerLayer, ho, _, _, hbottom⟩ := hband hu' hb
  let sizes := loopSizes cg'.edges labels u cg'.slot
  have fold_ge (rest : List LoopLabel) (a : Int) :
      a ≤ rest.foldl (fun h l => max h l.height) a := by
    induction rest generalizing a with
    | nil => exact Int.le_refl _
    | cons l rest ih => exact Int.le_trans (Int.le_max_left _ _) (ih _)
  have hband0 : 0 ≤ Loops.band cg'.slot sizes := by
    have h := fold_ge sizes (2 * cg'.slot)
    change 2 * cg'.slot ≤ Loops.band cg'.slot sizes at h
    omega
  have hlen : (sizes.length : Int) ≤ 2 * (sizes.length : Int) := by omega
  have hs := Int.mul_le_mul_of_nonneg_right hlen hband0
  change 2 * (sizes.length : Int) * Loops.band cg'.slot sizes ≤ node.h at hsize
  have hh := (regionRunFrameDims hrun hu hb).2
  have hcap : (sizes.length : Int) * Loops.band cg'.slot sizes ≤
      (frameRect P cg' run u).h := by omega
  have hf : frameRect default cg' run u = frameRect P cg' run u := rfl
  unfold loopFootprintExt
  simp only [hf]
  change (frameRect P cg' run u).y +
      max (frameRect P cg' run u).h ((sizes.length : Int) * Loops.band cg'.slot sizes) ≤ _
  rw [Int.max_eq_left hcap]
  exact Int.le_trans hbottom (hsep hlt ho hl)

theorem componentRunR_loopFootprint_miss_plain_other_rank {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run))
    {u v : Nat} {nu nv : Node} (hu : cg'.nodes[u]? = some nu) (hv : cg'.nodes[v]? = some nv)
    (hbu : nu.border = 0) (hbv : nv.border = 0)
    (hrank : (rk run.proper.rank u).toNat ≠ (rk run.proper.rank v).toNat)
    (hreserve : ∀ (s : Nat) (above : List Nat),
      (rk run.proper.rank u).toNat < s → run.layers[s]? = some above →
      (loopFootprintExt cg' run labels u).y + (loopFootprintExt cg' run labels u).h ≤
        run.top.getD s 0) :
    ¬ (loopFootprintExt cg' run labels u).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  obtain ⟨hband, hsep⟩ := componentRunR_plain_rank_bands hrun
  obtain ⟨layerU, hlookupU, _, hloU, _⟩ := hband hu hbu
  obtain ⟨layerV, hlookupV, _, hloV, hhiV⟩ := hband hv hbv
  have hvlen : v < run.proper.nodes.length :=
    componentRunR_original_nodes_covered hrun v (List.getElem?_eq_some_iff.mp hv).1
  have hframeV := plain_frame_eq_run_box (P := P) hv hbv hvlen
  have hframeY : (loopFootprintExt cg' run labels u).y = (frameRect P cg' run u).y := rfl
  rw [hframeV] at hloV hhiV
  unfold Rect.meetsInterior
  rcases Nat.lt_or_gt_of_ne hrank with hlt | hgt
  · have hreserve' := hreserve _ _ hlt hlookupV
    omega
  · have habove := hsep hgt hlookupV hlookupU
    omega

end Elegant.Layered.PipelineImpl

import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ForwardLane
import Elegant.Layered.LaneMetadata
import Elegant.Layered.RunStageChainKeys

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RouteImpl

private theorem endpoint_gap_order {indices : List Nat} {gap : Nat → Nat}
    {first last i : Nat} (hf : indices.head? = some first)
    (hl : indices.getLast? = some last)
    (horder : indices.Pairwise (fun a b => gap a < gap b)) (hi : i ∈ indices) :
    (i = first ∨ gap first < gap i) ∧ (i = last ∨ gap i < gap last) := by
  constructor
  · obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hf
    rw [hrest] at horder hi
    rcases List.mem_cons.mp hi with he | hm
    · exact Or.inl he
    · exact Or.inr ((List.pairwise_cons.mp horder).1 _ hm)
  · obtain ⟨before, hbefore⟩ := List.getLast?_eq_some_iff.mp hl
    rw [hbefore] at horder hi
    rcases List.mem_append.mp hi with hm | he
    · exact Or.inr (horder.rel_of_mem_append hm (by simp))
    · exact Or.inl (List.mem_singleton.mp he)

private theorem pairsAll_of_members {R : Point → Point → Prop} :
    ∀ points : List Point,
      (∀ a ∈ points, ∀ b ∈ points, R a b) → pairsAll R points
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, h =>
    ⟨h a (by simp) b (by simp), pairsAll_of_members (b :: rest) fun c hc d hd =>
      h c (List.mem_cons_of_mem a hc) d (List.mem_cons_of_mem a hd)⟩

private theorem dedup_interval_miss {points : List Point} {rect : Rect} {lo hi : Int}
    (hside : rect.y + rect.h ≤ lo ∨ hi ≤ rect.y)
    (hin : ∀ pt ∈ points, lo ≤ pt.y ∧ pt.y ≤ hi) :
    ¬ Polyline.hitsRect (dedup points) rect := by
  apply Polyline.not_hits_of_allMiss
  rw [allSegsMiss_iff]
  apply pairsAll_dedup
  apply pairsAll_of_members
  intro a ha b hb
  have hA := hin a ha
  have hB := hin b hb
  rcases hside with hside | hside
  · apply miss_below
    omega
  · apply miss_above
    omega

set_option maxHeartbeats 1000000 in
theorem componentRun_plain_endpoint_miss
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hP : P.Valid) (hd : (cg.edges.map (·.decl)).Nodup) (hs : CgShape cg)
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {rt : EdgeRoute} (hrt : rt ∈ run.routes) {first last v : Nat}
    (hf : (RouteImpl.edgesOf run.proper rt.original).head? = some first)
    (hl : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last)
    (hplain : (cg.nodes.getD v default).border = 0)
    (hend : v = (RouteImpl.edgeAt run.proper first).tail ∨
      v = (RouteImpl.edgeAt run.proper last).head) :
    ¬ Polyline.hitsRect rt.points (frameRect P cg run v) := by
  obtain ⟨_, _, _, q, _, _, _, _, _, hproxy, hdrop, hroute, _, hcoords, _, hpoints⟩ :=
    componentRun_spec hrun
  obtain ⟨ho, hrouteOf⟩ := routePointsWithLanes_mem hpoints hrt
  let indices := edgesOf run.proper rt.original
  let gap := gapOf run.proper
  let tail := fun i => (edgeAt run.proper i).tail
  let head := fun i => (edgeAt run.proper i).head
  let heights := run.layers.map (RouteImpl.layerHeight run.proper)
  let top := fun k => run.top.getD k 0
  let height := fun k => heights.getD k 0
  let y := yAt run.ys
  let bottom := fun j => y j + nodeH run.proper j
  let start := fun i => (pieceStart run.proper run.ys run.lanes.routing i).y
  let rect := boxRect run.proper run.xs run.ys v
  have hfirst : first ∈ indices := List.mem_of_head? hf
  have hlast : last ∈ indices := List.mem_of_getLast? hl
  have hiFirst := RouteImpl.mem_edgesOf hfirst
  have hiLast := RouteImpl.mem_edgesOf hlast
  have hlayers := (routeWithLanes_geometry hroute).1
  obtain ⟨_, hsizes, _, hcover, hedges⟩ := layersOk_spec hlayers
  have hv : v < run.proper.nodes.length := by
    rcases hend with he | he
    · rw [he]; exact (hedges first hiFirst).1
    · rw [he]; exact (hedges last hiLast).2.1
  rw [plain_frame_eq_boxRect P cg run v hv (by rw [hplain]; decide)]
  have hoGraph : rt.original < cg.edges.length := by
    simpa only [componentRun_proper_chains_length hrun] using ho
  obtain ⟨edge, hedge⟩ : ∃ e, cg.edges[rt.original]? = some e :=
    ⟨_, List.getElem?_eq_getElem hoGraph⟩
  have hnonloop : edge.tail ≠ edge.head := by
    intro he
    rw [selfLoop_edgesOf_empty hrun hedge he] at hf
    simp at hf
  obtain ⟨a, b, ha, hb, ht, hh⟩ := componentRun_chain_endpoints hP hd hs hrun hedge hnonloop
  have haf : first = a := Option.some.inj (hf.symm.trans ha)
  have hbl : last = b := Option.some.inj (hl.symm.trans hb)
  rw [← haf] at ht
  rw [← hbl] at hh
  obtain ⟨_, _, hn, _, _⟩ := componentRun_normalized_source hrun
  have hbounds := RankImpl.wellformed_spec (normalize_node_rank_alignment hn).2 edge
    (List.mem_of_getElem? hedge)
  have hvGraph : v < cg.nodes.length := by
    rcases hend with he | he
    · rw [he, ht]; exact hbounds.1
    · rw [he, hh]; exact hbounds.2.1
  obtain ⟨node, hnode⟩ : ∃ n, cg.nodes[v]? = some n :=
    ⟨_, List.getElem?_eq_getElem hvGraph⟩
  have hbNode : node.border = 0 := by
    simpa only [List.getD_eq_getElem?_getD, hnode, Option.getD_some] using hplain
  obtain ⟨out, _, hout, _, hborder, _, _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnode hbNode
  have hkind : frameKind run.proper v = 0 := by
    simp only [frameKind, hout, hborder, ite_self]
  have hshape := (componentRun_facts hP hd hs hrun).1
  have horder : indices.Pairwise (fun a b => gap a < gap b) :=
    chain_pairwise gap (fun _ _ h => chain_gap_lt hlayers h) indices (hshape rt.original)
  have hgate {i : Nat} (hi : i ∈ indices) := endpoint_gap_order hf hl horder hi
  have hrank : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]
    exact (proxyWidths_rel hproxy).2.1
  have hnodes : run.proper.nodes = q.nodes := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hheight (l : List Nat) : RouteImpl.layerHeight run.proper l =
      CoordsImpl.layerHeight run.coordinateProper l := by
    change RouteImpl.layerHeight run.proper l = RouteImpl.layerHeight run.coordinateProper l
    have he : RouteImpl.layerHeight run.proper l = RouteImpl.layerHeight q l := by
      simp only [RouteImpl.layerHeight, RouteImpl.nodeH, hnodes]
    exact he.trans (layerHeight_proxy hproxy l)
  have hnodeBand (j : Nat) (hj : j < run.proper.nodes.length) :
      let k := (rk run.proper.rank j).toNat
      top k ≤ y j ∧ bottom j ≤ top k + height k := by
    obtain ⟨l, hlayer, hlo, hhi⟩ :=
      componentRunGen_node_band_plain hrun (List.getElem?_eq_getElem hj)
    rw [← hrank] at hlayer hlo hhi
    have he := (heights_getD (p := run.proper) hlayer).trans (hheight l)
    refine ⟨hlo, ?_⟩
    rw [show bottom j = yAt run.ys j + nodeH run.proper j from rfl,
      show top (rk run.proper.rank j).toNat =
        run.top.getD (rk run.proper.rank j).toNat 0 from rfl,
      show height (rk run.proper.rank j).toNat =
        (run.layers.map (RouteImpl.layerHeight run.proper)).getD
          (rk run.proper.rank j).toNat 0 from rfl,
      he]
    simp only [yAt]
    exact hhi
  have hband (k j : Nat) (hkj : k < j) (hj : j < run.layers.length) :
      top k + height k ≤ top j := by
    have hk : k < run.layers.length := by omega
    have hkLayer : run.layers[k]? = some run.layers[k] := List.getElem?_eq_getElem hk
    have hjLayer : run.layers[j]? = some run.layers[j] := List.getElem?_eq_getElem hj
    have he := (heights_getD (p := run.proper) hkLayer).trans (hheight run.layers[k])
    have hsep := CoordsImpl.rankAxis_bands_disjoint hcoords k j _ _ hkj hkLayer hjLayer
    simpa only [height, heights, he] using hsep
  have hheightNN (k : Nat) (hk : k < run.layers.length) : 0 ≤ height k := by
    change 0 ≤ (run.layers.map (RouteImpl.layerHeight run.proper)).getD k 0
    rw [heights_getD (List.getElem?_eq_getElem hk)]
    exact RouteImpl.layerHeight_nonneg _ _
  have hgapHead (i : Nat) (hi : i < run.proper.edges.length) :
      (rk run.proper.rank (head i)).toNat = gap i + 1 := by
    change (rk run.proper.rank (edgeAt run.proper i).head).toNat =
      (rk run.proper.rank (edgeAt run.proper i).tail).toNat + 1
    have hr := (hedges i hi).2.2
    obtain ⟨_, _, _, hnn⟩ := hcover _ (hedges i hi).1
    omega
  have heBand (i : Nat) (hi : i < run.proper.edges.length) :
      bottom (tail i) ≤ top (gap i) + height (gap i) ∧ top (gap i + 1) ≤ y (head i) := by
    refine ⟨(hnodeBand _ (hedges i hi).1).2, ?_⟩
    rw [← hgapHead i hi]
    exact (hnodeBand _ (hedges i hi).2.1).1
  have hgapValid (i : Nat) (hi : i < run.proper.edges.length) :
      gap i + 1 < run.layers.length := forward_gap_valid hroute hi
  have hchannel {i : Nat} (hi : i ∈ indices) {z : Int}
      (hz : top (gap i) + height (gap i) ≤ z ∧ z ≤ top (gap i + 1)) :
      bottom (tail first) ≤ z ∧ z ≤ y (head last) := by
    rcases hgate hi with ⟨hlo, hhi⟩
    have hib := hgapValid i (RouteImpl.mem_edgesOf hi)
    constructor
    · have hfirstBand := (heBand first hiFirst).1
      rcases hlo with rfl | hlo
      · exact Int.le_trans hfirstBand hz.1
      · have hsep := hband _ _ hlo (by omega)
        have hnn := hheightNN (gap i) (by omega)
        omega
    · have hlastBand := (heBand last hiLast).2
      rcases hhi with rfl | hhi
      · exact Int.le_trans hz.2 hlastBand
      · have hsep := hband (gap i + 1) (gap last + 1) (by omega) (hgapValid last hiLast)
        have hnn := hheightNN (gap i + 1) hib
        omega
  have hgen : componentRunGen P (sizeProperPorts P) (fun _ _ ys ts => .ok (ys, ts))
      [] cg labels orderOptions = .ok run := by
    rw [← componentRun_eq_gen]
    exact hrun
  obtain ⟨_, hgap, hslot, hhalf⟩ := hP
  have hhalfGap := CoordsImpl.half_slot_le_rankGapAt hgap hhalf run.proper run.layers
  have hstep := fun k hk =>
    componentRunGen_rank_step_lower (runHooksShift_plain P cg labels) hgen (k := k) hk
  obtain ⟨base, _, _, hlas⟩ := routeWithLanes_spec hroute
  cases hfind : run.lanes.runs.find? (fun lane => lane.original == rt.original) with
  | none =>
    have hrev : (cg.edges.map (·.reversed)).getD rt.original false = false := by
      apply Bool.eq_false_iff.mpr
      intro hr
      have hne : (edgesOf run.proper rt.original).isEmpty = false := by
        exact List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hfirst)
      obtain ⟨lane, hm, hor⟩ := plannedLane_exists (slot := P.slot) (p := run.proper) (base := base)
        (x := run.xs) (widths := cg.edges.map fun e =>
          (stackSize cg.slot (routeLabels labels e.decl)).width) ho hr hne
      have hmem : lane ∈ run.lanes.runs := by rw [hlas]; exact hm
      exact (List.find?_eq_none.mp hfind lane hmem) (by simp only [hor, beq_self_eq_true])
    have hstart (i : Nat) (hi : i < run.proper.edges.length) :
        y (tail i) ≤ start i ∧ start i ≤ bottom (tail i) := by
      have hnn : 0 ≤ nodeH run.proper (tail i) := (hsizes _ (hedges i hi).1).2
      have hle : y (tail i) ≤ bottom (tail i) := by
        change y (tail i) ≤ y (tail i) + nodeH run.proper (tail i)
        omega
      change y (tail i) ≤ (if frameKind run.proper (tail i) = -2 then y (tail i)
          else bottom (tail i)) ∧
        (if frameKind run.proper (tail i) = -2 then y (tail i) else bottom (tail i)) ≤ bottom (tail i)
      by_cases he : frameKind run.proper (tail i) = -2
      · simpa only [ite_eq_left he] using And.intro (Int.le_refl (y (tail i))) hle
      · simpa only [ite_eq_right he] using And.intro hle (Int.le_refl (bottom (tail i)))
    have hpiece (i : Nat) (hi : i ∈ indices) {piece : List Point}
        (hp : pieceOf run.proper P.slot run.ys run.top heights run.lanes.routing i = .ok piece) :
        ∀ pt ∈ piece, start first ≤ pt.y ∧ pt.y ≤ y (head last) := by
      have hib := RouteImpl.mem_edgesOf hi
      have ⟨hlo, hhi⟩ := hgate hi
      have hstartFirst := (hstart first hiFirst).2
      have hstartOrder : start first ≤ start i := by
        rcases hlo with rfl | hlo
        · exact Int.le_refl _
        · have hsep := hband _ _ hlo (by have := hgapValid i hib; omega)
          exact Int.le_trans hstartFirst (Int.le_trans (heBand first hiFirst).1
            (Int.le_trans hsep (Int.le_trans (hnodeBand _ (hedges i hib).1).1 (hstart i hib).1)))
      have hendOrder : y (head i) ≤ y (head last) := by
        rcases hhi with rfl | hhi
        · exact Int.le_refl _
        · have hheadBand := (hnodeBand _ (hedges i hib).2.1).2
          rw [hgapHead i hib] at hheadBand
          have hsep := hband (gap i + 1) (gap last + 1) (by omega) (hgapValid last hiLast)
          have hnn : 0 ≤ nodeH run.proper (head i) := (hsizes _ (hedges i hib).2.1).2
          have hle : y (head i) ≤ bottom (head i) := by
            change y (head i) ≤ y (head i) + nodeH run.proper (head i)
            omega
          exact Int.le_trans hle (Int.le_trans hheadBand (Int.le_trans hsep (heBand last hiLast).2))
      have hlocal : start i ≤ y (head i) := by
        have hsep := hband (gap i) (gap i + 1) (by omega) (hgapValid i hib)
        exact Int.le_trans (hstart i hib).2
          (Int.le_trans (heBand i hib).1 (Int.le_trans hsep (heBand i hib).2))
      have hstartIn := And.intro hstartOrder (Int.le_trans hlocal hendOrder)
      have hendIn := And.intro (Int.le_trans hstartOrder hlocal) hendOrder
      rcases pieceOf_cases hp with ⟨rfl, _⟩ | ⟨rfl, hturn⟩
      · intro pt hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · exact hstartIn
        · exact hstartIn
        · exact hendIn
      · have hrevI : (cg.edges.map (·.reversed)).getD (edgeAt run.proper i).original false = false := by
          rw [(PipelineImpl.mem_edgesOf.mp hi).2]
          exact hrev
        have hm := forward_mid_bounds hroute hslot (hhalfGap (gap i)) hib hrevI hturn
          (hstep (gap i) (hgapValid i hib))
        have hmid := hchannel hi hm
        have hmidIn := And.intro (Int.le_trans hstartFirst hmid.1) hmid.2
        intro pt hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl
        · exact hstartIn
        · exact hstartIn
        · exact hmidIn
        · exact hmidIn
        · exact hendIn
    simp only [laneRouteOf, hfind, routeOf] at hrouteOf
    split at hrouteOf
    · simp at hrouteOf
    · next pieces hp =>
      have hpts := congrArg EdgeRoute.points (Except.ok.inj hrouteOf).symm
      rw [hpts]
      apply dedup_interval_miss (rect := rect) (lo := start first) (hi := y (head last))
      · rcases hend with he | he
        · left
          change v = tail first at he
          have hnot : frameKind run.proper (tail first) ≠ -2 := by
            rw [← he, hkind]
            decide
          change bottom v ≤ start first
          rw [he]
          change bottom (tail first) ≤
            (if frameKind run.proper (tail first) = -2 then y (tail first) else bottom (tail first))
          simpa only [ite_eq_right hnot] using (Int.le_refl (bottom (tail first)))
        · right
          change y (head last) ≤ y v
          simpa only [he] using (Int.le_refl (y (head last)))
      · intro pt hpt
        obtain ⟨piece, hmem, hpt⟩ := List.mem_flatten.mp hpt
        obtain ⟨i, hi, hpc⟩ := mapOk_mem _ _ _ hp piece hmem
        exact hpiece i hi hpc pt hpt
  | some lane =>
    have hm := List.mem_of_find?_eq_some hfind
    have hor : lane.original = rt.original := by
      simpa only [beq_iff_eq] using List.find?_some hfind
    have hplanned : lane ∈ plannedLanes P.slot run.proper base run.xs
        (cg.edges.map (·.reversed))
        (cg.edges.map fun e => (stackSize cg.slot (routeLabels labels e.decl)).width) := by
      rw [hlas] at hm
      exact hm
    obtain ⟨_, _, hsource, htarget, hsg, htg, _⟩ := plannedLane_endpoints hplanned
      (by rw [hor]; exact hf) (by rw [hor]; exact hl)
    have hmids := laneRun_mid_bounds hroute hslot hhalfGap hstep hm
    rw [hsg, htg] at hmids
    have hport : tailPortY run.proper run.ys (tail first) ≤ bottom (tail first) :=
      tailPortY_le_bottom (hsizes _ (hedges first hiFirst).1).2
    obtain ⟨hcsLo, hcsHi⟩ := hchannel hlast hmids.1
    obtain ⟨hctLo, hctHi⟩ := hchannel hfirst hmids.2
    have hcs := And.intro (Int.le_trans hport hcsLo) hcsHi
    have hct := And.intro (Int.le_trans hport hctLo) hctHi
    have hspan := Int.le_trans hcs.1 hcs.2
    simp only [laneRouteOf, hfind] at hrouteOf
    split at hrouteOf
    · have hpts := congrArg EdgeRoute.points (Except.ok.inj hrouteOf).symm
      rw [hpts]
      show ¬ Polyline.hitsRect
        (dedup (reversedPoints P.slot run.proper run.ys run.top
          (List.map (RouteImpl.layerHeight run.proper) run.layers) run.lanes.routing lane))
        (boxRect run.proper run.xs run.ys v)
      apply dedup_interval_miss (rect := rect)
        (lo := tailPortY run.proper run.ys (tail first)) (hi := y (head last))
      · rcases hend with he | he
        · left
          change v = tail first at he
          have hnot : frameKind run.proper (tail first) ≠ -2 := by
            rw [← he, hkind]
            decide
          change bottom v ≤ tailPortY run.proper run.ys (tail first)
          rw [he]
          simpa only [tailPortY, ite_eq_right hnot] using (Int.le_refl (bottom (tail first)))
        · right
          change y (head last) ≤ y v
          simpa only [he] using (Int.le_refl (y (head last)))
      · intro pt hpt
        simp only [reversedPoints, hsource, htarget, hsg, htg,
          List.mem_cons, List.not_mem_nil, or_false] at hpt
        rcases hpt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hspan, Int.le_refl _⟩
        · exact hcs
        · exact hcs
        · exact hct
        · exact hct
        · exact ⟨Int.le_refl _, hspan⟩
        · exact ⟨Int.le_refl _, hspan⟩
    · simp at hrouteOf

end Elegant.Layered.PipelineImpl

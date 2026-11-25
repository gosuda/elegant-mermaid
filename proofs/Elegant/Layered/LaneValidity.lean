import Elegant.Layered.LaneMetadata
import Elegant.Layered.ForwardLane

set_option autoImplicit false

namespace Elegant.Layered.RouteImpl

theorem reversed_runtime_clearance {slot gap : Int} {rankGap : Nat → Int} {p : Proper}
    {layers : List (List Nat)} {x y top : List Int} {reversed : List Bool}
    {widths : List Int} {lr : LaneRouting} {run : ReversedLane} {rt : EdgeRoute}
    (hr : routeWithLanes slot p layers x reversed widths = .ok lr)
    (hF : CoordFacts p layers x y top lr.routing gap rankGap slot)
    (hf : lr.runs.find? (fun run => run.original == rt.original) = some run)
    (he : laneRouteOf slot p y top (layers.map (layerHeight p)) lr rt.original = .ok rt)
    {v : Nat} (hv : v < p.nodes.length) (hvpos : 0 < nodeH p v) (hvs : v ≠ run.sourceNode)
    (hvt : v ≠ run.targetNode) :
    ¬ Polyline.hitsRect rt.points (boxRect p x y v) := by
  have hm := List.mem_of_find?_eq_some hf
  have hstep (k : Nat) (hk : k + 1 < layers.length) :
      top.getD k 0 + (layers.map (layerHeight p)).getD k 0 + rankGap k +
        slot * (lr.routing.gaps.getD k default).slots ≤ top.getD (k + 1) 0 := by
    have hlt : k < layers.length := by omega
    have hl := List.getElem?_eq_getElem hlt
    have hb := hF.band_step k layers[k] hl hk
    rw [heights_getD hl]
    omega
  obtain ⟨hcs, hct⟩ := laneRun_mid_bounds hr hF.slot_pos hF.half_slot_le hstep hm
  obtain ⟨hs, ht, hsr, htr, htg, hsx0, hsx1, htx0, htx1, _, htrun⟩ := laneRun_node_facts hr hm
  exact laneRouteOf_reverse_avoids hf he (geo_ok_withLanes hr hF) hs ht hv hvs hvt
    hsr htr htg ⟨hsx0, hsx1⟩ ⟨htx0, htx1⟩ hcs hct hvpos htrun (laneRun_right_bound hr hm hv)

theorem forward_runtime_clearance {slot gap : Int} {rankGap : Nat → Int} {p : Proper}
    {layers : List (List Nat)} {x y top : List Int} {reversed : List Bool}
    {widths : List Int} {lr : LaneRouting} {rt : EdgeRoute}
    (hP : ProperShape p)
    (hr : routeWithLanes slot p layers x reversed widths = .ok lr)
    (hF : CoordFacts p layers x y top lr.routing gap rankGap slot)
    (hf : lr.runs.find? (fun run => run.original == rt.original) = none)
    (he : laneRouteOf slot p y top (layers.map (layerHeight p)) lr rt.original = .ok rt)
    (hrev : reversed.getD rt.original false = false)
    {i₀ i₁ : Nat} (h0 : (edgesOf p rt.original).head? = some i₀)
    (h1 : (edgesOf p rt.original).getLast? = some i₁)
    {v : Nat} (hv : v < p.nodes.length) (hreal : IsReal p v) (hvpos : 0 < nodeH p v)
    (hv0 : v ≠ (edgeAt p i₀).tail) (hv1 : v ≠ (edgeAt p i₁).head) :
    ¬ Polyline.hitsRect rt.points (boxRect p x y v) := by
  have hne := chain_ne hreal (edgesOf p rt.original) (hP _)
    (fun i' hi' => by
      rw [h0] at hi'
      have e := Option.some.inj hi'
      rw [← e]
      exact Ne.symm hv0)
    (fun i' hi' => by
      rw [h1] at hi'
      have e := Option.some.inj hi'
      rw [← e]
      exact Ne.symm hv1)
  obtain ⟨base, hb, _, hlr⟩ := routeWithLanes_spec hr
  have hG := geo_ok_withLanes hr hF
  have hl := (route_spec hb).1
  have hedge := (layersOk_spec hl).2.2.2.2
  simp only [laneRouteOf, hf] at he
  unfold routeOf at he
  split at he
  · simp at he
  · next pcs hpcs =>
    simp only [Except.ok.injEq] at he
    have hpts := congrArg EdgeRoute.points he
    rw [← hpts]
    dsimp only
    apply Polyline.not_hits_of_allMiss
    rw [allSegsMiss_iff]
    apply pairsAll_dedup
    refine pairsAll_flatten_of (fun P Q => Polyline.segMisses P Q (boxRect p x y v))
      (pieceStart p y lr.routing) (pieceEnd p y lr.routing) (ChainLink p) ?_
      (edgesOf p rt.original) pcs ?_ (hP rt.original)
    · intro i j hij
      obtain ⟨hi, hj, hhead, nd, hnd, hdum⟩ := hij
      have hd : (edgeAt p j).tail < p.nodes.length := (hedge j hj).1
      have hvd : v ≠ (edgeAt p j).tail := by
        intro hvd
        have := hreal nd (by rw [hvd]; exact hnd)
        rw [this] at hdum
        exact absurd hdum (by decide)
      have pi := port_ranges hb hi
      have pj := port_ranges hb hj
      have hs : lr.routing.sourceX = base.sourceX := by rw [hlr]; rfl
      have ht : lr.routing.targetX = base.targetX := by rw [hlr]; rfl
      rw [hhead] at pi
      have hnt : (routeGeo p layers x y top).bd (edgeAt p j).tail ≠ -2 := by
        show frameKind p (edgeAt p j).tail ≠ -2
        rw [frameKind_of_chain ⟨nd, hnd, hdum⟩]
        decide
      have key := junction_miss (G := routeGeo p layers x y top) hG hd hv hvd hnt hvpos
        (tx := base.targetX.getD i 0) (sx := base.sourceX.getD j 0)
        ⟨pi.2.2.1, pi.2.2.2⟩ ⟨pj.1, pj.2.1⟩
      have hfk : frameKind p (edgeAt p j).tail = 0 := frameKind_of_chain ⟨nd, hnd, hdum⟩
      have hps : pieceStart p y lr.routing j =
          ⟨base.sourceX.getD j 0, (routeGeo p layers x y top).yv (edgeAt p j).tail +
            (routeGeo p layers x y top).hv (edgeAt p j).tail⟩ := by
        simp [pieceStart, routeGeo, hfk, hs]
      have hpe : pieceEnd p y lr.routing i =
          ⟨base.targetX.getD i 0, (routeGeo p layers x y top).yv (edgeAt p j).tail⟩ := by
        simp [pieceEnd, routeGeo, hhead, ht]
      rw [hps, hpe, boxRect]
      exact key
    · exact Zipped.imp _ _ (fun i hi pc hpc =>
        ⟨(pieceOf_basic hpc).1, (pieceOf_basic hpc).2.1,
          forward_piece_pairs hr hF hv hvpos (mem_edgesOf hi)
            (by
              have hoi : (edgeAt p i).original = rt.original := by
                have key := (List.mem_filter.mp hi).2
                simpa only [beq_iff_eq] using key
              rw [hoi]; exact hrev)
            (hne i hi).1 (hne i hi).2 hpc⟩) (mapOk_zipped _ _ _ hpcs)

end Elegant.Layered.RouteImpl

namespace Elegant.Layered

theorem route_avoids_nodes {slot gap : Int} {rankGap : Nat → Int} {p : Proper}
    {layers : List (List Nat)} {x y top : List Int} {reversed : List Bool}
    {widths : List Int} {lr : RouteImpl.LaneRouting} {routes : List EdgeRoute}
    (hP : ProperShape p)
    (hr : RouteImpl.routeWithLanes slot p layers x reversed widths = .ok lr)
    (h : RouteImpl.routePointsWithLanes slot p layers x y top lr = .ok routes)
    (hF : CoordFacts p layers x y top lr.routing gap rankGap slot) :
    ∀ rt ∈ routes, ∀ i₀ i₁, (edgesOf p rt.original).head? = some i₀ →
      (edgesOf p rt.original).getLast? = some i₁ →
      ∀ v, v < p.nodes.length → IsReal p v → v ≠ (edgeAt p i₀).tail → v ≠ (edgeAt p i₁).head →
        ¬ Polyline.hitsRect rt.points (boxRect p x y v) := by
  intro rt hrt i₀ i₁ h0 h1 v hv hreal hv0 hv1
  refine Classical.byCases (fun hvpos : 0 < RouteImpl.nodeH p v => ?_) (fun hvpos hh => hvpos hh.2.1)
  obtain ⟨ho, he⟩ := RouteImpl.routePointsWithLanes_mem h hrt
  cases hf : lr.runs.find? (fun run => run.original == rt.original) with
  | some run =>
    have hm := List.mem_of_find?_eq_some hf
    have hor : run.original = rt.original := by
      simpa only [beq_iff_eq] using List.find?_some hf
    obtain ⟨base, hb, _, hlr⟩ := RouteImpl.routeWithLanes_spec hr
    have hmem : run ∈ RouteImpl.plannedLanes slot p base x reversed widths := by
      rw [hlr] at hm; exact hm
    have hends := RouteImpl.plannedLane_endpoints hmem
      (by rw [hor]; exact h0) (by rw [hor]; exact h1)
    exact RouteImpl.reversed_runtime_clearance hr hF hf he hv hvpos
      (by rw [hends.2.2.1]; exact hv1)
      (by rw [hends.2.2.2.1]; exact hv0)
  | none =>
    have hrev : reversed.getD rt.original false = false := by
      apply Classical.byContradiction
      intro hn
      have ht : reversed.getD rt.original false = true := by
        cases he : reversed.getD rt.original false <;> simp_all
      have hne : (edgesOf p rt.original).isEmpty = false := by
        cases he : edgesOf p rt.original <;> simp_all
      obtain ⟨base, hb, _, hlr⟩ := RouteImpl.routeWithLanes_spec hr
      obtain ⟨run, hm, hor⟩ := RouteImpl.plannedLane_exists
        (base := base) (x := x) (widths := widths) ho ht hne
      have hm' : run ∈ lr.runs := by rw [hlr]; exact hm
      have hn := List.find?_eq_none.mp hf run hm'
      exact hn (by simp only [hor, beq_self_eq_true])
    exact RouteImpl.forward_runtime_clearance hP hr hF hf he hrev h0 h1 hv hreal hvpos hv0 hv1

end Elegant.Layered

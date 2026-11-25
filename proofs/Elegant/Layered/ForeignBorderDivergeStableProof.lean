import Elegant.Layered.ForeignBorderEdgesNoncrossingProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

 /-!
 # Divergent sibling blocks keep their order across layers.

 Target: `foreignBorderDivergeStableSeparated_holds` below: in an executed
 `componentRun`, two side-border markers whose cluster paths are divergent
 keep the same relative order on every pair of layers they share, provided
 their divergent heads are separated (both in `Sibling.clusterIds` with the
 same `Sibling.parentOf`). In words: separated sibling cluster blocks keep
 one left-to-right order on every layer.

 Proof idea: every `order` output is one `siblingNormalise` application, which
 reorders each layer with a single global sibling-number function
 (`siblingNumber` over `siblingOrders`): keyed blocks are placed in sorted
 number order on every layer (`place`), so two blocks whose divergent heads
 receive distinct numbers keep their relative order on every layer
 (`Sibling.sibLevel_order`, generalized here to arbitrary path tails). The
 numbers separate the heads by `OrderImpl.siblingNumber_ne` once both heads
 sit in `Sibling.clusterIds` with the same `parentOf`.

 Verdict on the unconditional `ForeignBorderDivergeStable` (defined in
 `ForeignBorderEdgesNoncrossingProof`): it is OPEN, neither proved nor
 refuted. Its earlier committed proof rested on the over-general residual
 `DivergeHeadsSeparated` (now deleted): quantifying over arbitrary `Proper`
 values, that residual is false (`[5, 3]` vs `[7]` witness), and it is false
 on executed runs too: demoting an intermediate group via `fixedSizes`
 removes its exact markers, so divergent heads can be absent from
 `Sibling.clusterIds`. The replayed-number residual `DivergeNumsDistinct`
 (also deleted) is likewise false on executed runs. What remains proved here
 is the separated case with no residual; the tie mechanism is proved as
 `siblingNumber_tie_of_absent` in `DivergeHeadsSeparatedProof`.

 Probe evidence: `wip/Probe/DivergeStableTProbe.lean` (14 adversarial samples,
 84 executed runs, 88512 divergent quads) and the rerun
 `wip/Probe/DivergeCollisionProbe.lean` (3 samples, 18 runs) report zero
 order violations. `wip/Probe/FixedTieTProbe.lean` (6 samples, 36 runs,
 dense criss-cross) and `wip/Probe/DivergeFanProbe.lean` (fanned zigzag end
 pins, 24 runs) likewise report zero flips with non-vacuous quads (800 and
 3968 per run), while block order follows the sweep pre-order and varies
 across seeds yet stays uniform within every run. The rerun
 `wip/Probe/DivergeNestProbe.lean` covers nested and one-sided demotions.
 On every demoted run the divergent heads tie in `siblingNumber`
 (both absent from `clusterIds`, verified equal numbers on the true replayed
 order): ties occur, flips do not, and the cross-layer tie-break is unproved.
 -/


/-- Distinct divergent heads force distinct full paths. -/
theorem diverge_paths_ne {P : List Nat} {A B : Nat} {r1 r2 : List Nat}
    (hAB : A ≠ B) : P ++ A :: r1 = P ++ B :: r2 → False := by
  induction P generalizing r1 r2 with
  | nil => intro h; exact hAB (Option.some.inj (congrArg List.head? h))
  | cons _ _ ih => intro h; exact ih (Option.some.inj (congrArg List.tail? h))

/-- General-tail sibling order: two nodes whose node paths diverge keep their
relative order in one `siblingLayer` application when their divergent heads
are ordered by `num`. -/
theorem siblingLayer_pair_general {p : Proper} {num : Nat → Nat}
    {layer : List Nat} {P : List Nat} {A B u v : Nat} {ru rv : List Nat}
    (hu : u ∈ layer) (hv : v ∈ layer)
    (hpu : OrderImpl.nodePath p u = P ++ A :: ru)
    (hpv : OrderImpl.nodePath p v = P ++ B :: rv)
    (hAB : A ≠ B) (hnum : num A < num B) :
    [u, v].Sublist (OrderImpl.siblingLayer p num layer) := by
  have hfuel : P.length < OrderImpl.sibFuel p layer := by
    have hmax :=
      (OrderImpl.fold_max_lower (fun v => (OrderImpl.nodePath p v).length) layer 0).2 u hu
    simp only [hpu, List.length_append, List.length_cons] at hmax
    unfold OrderImpl.sibFuel
    omega
  exact OrderImpl.Sibling.sibLevel_order num P (OrderImpl.sibFuel p layer)
    (OrderImpl.nodePath p) layer u v A B ru rv hfuel hu hv hpu hpv hAB hnum

/-- One `siblingNormalise` pre-layer pair keeps divergent marker order:
both output layers place the two blocks in `num` order. -/
theorem normalise_pair_stable {p : Proper} {Y : List (List Nat)}
    {num : Nat → Nat} {k1 k2 : Nat}
    {l1 l2 : List Nat}
    (e1 : OrderImpl.siblingLayer p num (Y.getD k1 []) = l1)
    (e2 : OrderImpl.siblingLayer p num (Y.getD k2 []) = l2)
    {a b a' b' : Nat} {na nb na' nb' : ProperNode}
    (hna : p.nodes[a]? = some na) (hnb : p.nodes[b]? = some nb)
    (hna' : p.nodes[a']? = some na') (hnb' : p.nodes[b']? = some nb')
    (hda : na.dummy = false) (hdb : nb.dummy = false)
    (hda' : na'.dummy = false) (hdb' : nb'.dummy = false)
    {P : List Nat} {A B : Nat} {r1 r2 : List Nat}
    (hpa : na.node.clusterPath = P ++ A :: r1)
    (hpb : nb.node.clusterPath = P ++ B :: r2)
    (hpa' : na'.node.clusterPath = P ++ A :: r1)
    (hpb' : nb'.node.clusterPath = P ++ B :: r2)
    (hAB : A ≠ B) (hnum : num A ≠ num B)
    (hnd1 : l1.Nodup) (hnd2 : l2.Nodup)
    {i j i' j' : Nat}
    (hi1 : l1[i]? = some a) (hj1 : l1[j]? = some b)
    (hi2 : l2[i']? = some a') (hj2 : l2[j']? = some b') :
    (i < j ↔ i' < j') := by
  have memA : a ∈ Y.getD k1 [] := by
    have ha : a ∈ l1 := List.mem_of_getElem? hi1
    rw [← e1] at ha
    exact (OrderImpl.siblingLayer_perm p num _).mem_iff.mp ha
  have memB : b ∈ Y.getD k1 [] := by
    have hb : b ∈ l1 := List.mem_of_getElem? hj1
    rw [← e1] at hb
    exact (OrderImpl.siblingLayer_perm p num _).mem_iff.mp hb
  have memA' : a' ∈ Y.getD k2 [] := by
    have ha : a' ∈ l2 := List.mem_of_getElem? hi2
    rw [← e2] at ha
    exact (OrderImpl.siblingLayer_perm p num _).mem_iff.mp ha
  have memB' : b' ∈ Y.getD k2 [] := by
    have hb : b' ∈ l2 := List.mem_of_getElem? hj2
    rw [← e2] at hb
    exact (OrderImpl.siblingLayer_perm p num _).mem_iff.mp hb
  have npa : OrderImpl.nodePath p a = P ++ A :: r1 :=
    (OrderImpl.nodePath_of_node hna hda).trans hpa
  have npb : OrderImpl.nodePath p b = P ++ B :: r2 :=
    (OrderImpl.nodePath_of_node hnb hdb).trans hpb
  have npa' : OrderImpl.nodePath p a' = P ++ A :: r1 :=
    (OrderImpl.nodePath_of_node hna' hda').trans hpa'
  have npb' : OrderImpl.nodePath p b' = P ++ B :: r2 :=
    (OrderImpl.nodePath_of_node hnb' hdb').trans hpb'
  have hab : a ≠ b := by
    intro h
    subst h
    have hnn : na = nb := Option.some.inj (hna.symm.trans hnb)
    rw [hnn] at hpa
    exact diverge_paths_ne hAB (hpa.symm.trans hpb)
  have hab' : a' ≠ b' := by
    intro h
    subst h
    have hnn : na' = nb' := Option.some.inj (hna'.symm.trans hnb')
    rw [hnn] at hpa'
    exact diverge_paths_ne hAB (hpa'.symm.trans hpb')
  rcases Nat.lt_or_gt_of_ne hnum with hlt | hgt
  · have s1 : [a, b].Sublist l1 := by
      rw [← e1]
      exact siblingLayer_pair_general memA memB npa npb hAB hlt
    have s2 : [a', b'].Sublist l2 := by
      rw [← e2]
      exact siblingLayer_pair_general memA' memB' npa' npb' hAB hlt
    have g1 := OrderImpl.index_lt_of_pair_sublist hnd1 s1 hab hi1 hj1
    have g2 := OrderImpl.index_lt_of_pair_sublist hnd2 s2 hab' hi2 hj2
    exact ⟨fun _ => g2, fun _ => g1⟩
  · have s1 : [b, a].Sublist l1 := by
      rw [← e1]
      exact siblingLayer_pair_general memB memA npb npa (Ne.symm hAB) hgt
    have s2 : [b', a'].Sublist l2 := by
      rw [← e2]
      exact siblingLayer_pair_general memB' memA' npb' npa' (Ne.symm hAB) hgt
    have g1 := OrderImpl.index_lt_of_pair_sublist hnd1 s1 (Ne.symm hab) hj1 hi1
    have g2 := OrderImpl.index_lt_of_pair_sublist hnd2 s2 (Ne.symm hab') hj2 hi2
    exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

theorem siblingNormalise_map_form (p : Proper) (L : List (List Nat))
    (hne : (OrderImpl.Sibling.clusterIds p).isEmpty = false) :
    OrderImpl.siblingNormalise p L = L.map (OrderImpl.siblingLayer p
      (OrderImpl.Sibling.siblingNumber p
        (OrderImpl.Sibling.siblingOrders p (OrderImpl.posOf p L)))) := by
  unfold OrderImpl.siblingNormalise
  simp [hne]

/-- The seed choice is one `siblingNormalise` map. -/
theorem seedBest_siblingForm (p : Proper) (start : OrderStart)
    (hne : (OrderImpl.Sibling.clusterIds p).isEmpty = false) :
    ∃ Y : List (List Nat), OrderImpl.seedBest p start = Y.map (OrderImpl.siblingLayer p
      (OrderImpl.Sibling.siblingNumber p
        (OrderImpl.Sibling.siblingOrders p (OrderImpl.posOf p Y)))) := by
  unfold OrderImpl.seedBest
  dsimp only
  split
  · exact ⟨OrderImpl.seedBase p start, by
      unfold OrderImpl.seedLayers
      exact siblingNormalise_map_form p _ hne⟩
  · exact ⟨OrderImpl.initBase p, by
      unfold OrderImpl.initOrder
      exact siblingNormalise_map_form p _ hne⟩

/-- Every `runKey` result is one `siblingNormalise` map. -/
theorem runKey_siblingForm (p : Proper) (key : OrderKey)
    (limit stallLimit : Nat)
    (hne : (OrderImpl.Sibling.clusterIds p).isEmpty = false) :
    ∀ (fuel sweep : Nat) (best : List (List Nat)) (score stall : Nat),
      (∃ Y : List (List Nat), best = Y.map (OrderImpl.siblingLayer p
        (OrderImpl.Sibling.siblingNumber p
          (OrderImpl.Sibling.siblingOrders p (OrderImpl.posOf p Y))))) →
      ∃ Y : List (List Nat), (OrderImpl.runKey p key limit stallLimit fuel sweep best score stall).layers
        = Y.map (OrderImpl.siblingLayer p (OrderImpl.Sibling.siblingNumber p
          (OrderImpl.Sibling.siblingOrders p (OrderImpl.posOf p Y)))) := by
  intro fuel
  induction fuel with
  | zero => intro sweep best score stall h; exact h
  | succ fuel ih =>
    intro sweep best score stall h
    have htr : ∃ Y : List (List Nat), OrderImpl.siblingNormalise p
          (OrderImpl.transpose p (OrderImpl.sweepLayers p sweep best key))
          = Y.map (OrderImpl.siblingLayer p (OrderImpl.Sibling.siblingNumber p
            (OrderImpl.Sibling.siblingOrders p (OrderImpl.posOf p Y)))) := by
      exact ⟨_, siblingNormalise_map_form p _ hne⟩
    unfold OrderImpl.runKey
    dsimp only
    by_cases himp : OrderImpl.crossCount p (OrderImpl.siblingNormalise p
        (OrderImpl.transpose p (OrderImpl.sweepLayers p sweep best key))) < score
    · simp only [himp, decide_true, ite_true]
      split
      · exact htr
      · split
        · exact htr
        · exact ih _ _ _ _ htr
    · simp only [himp, decide_false, Bool.false_eq_true, ite_false]
      split
      · exact h
      · split
        · exact h
        · exact ih _ _ _ _ h

/-- Every `order` output is one `siblingNormalise` map. -/
theorem order_siblingForm (p : Proper) (opts : OrderOptions)
    (L : List (List Nat)) (h : OrderImpl.order p opts = .ok L)
    (hne : (OrderImpl.Sibling.clusterIds p).isEmpty = false) :
    ∃ Y : List (List Nat), L = Y.map (OrderImpl.siblingLayer p (OrderImpl.Sibling.siblingNumber p
      (OrderImpl.Sibling.siblingOrders p (OrderImpl.posOf p Y)))) := by
  obtain ⟨result, hr, rfl⟩ := OrderImpl.ok_layers h
  unfold OrderImpl.orderWithBudget at hr
  split at hr
  · split at hr
    · simp only [Except.ok.injEq] at hr
      subst hr
      exact runKey_siblingForm p opts.key OrderImpl.sweepMax OrderImpl.sweepStall hne
        OrderImpl.sweepMax 0 (OrderImpl.seedBest p opts.start)
        (OrderImpl.crossCount p (OrderImpl.seedBest p opts.start)) 0
        (seedBest_siblingForm p opts.start hne)
    · simp at hr
  · simp at hr
 /-- Divergent sibling blocks keep their order on every layer pair, when their
 divergent heads are separated (both in `Sibling.clusterIds` with the same
 `Sibling.parentOf`). This bakes the narrowest true premise into the statement:
 a single fact about the ordering phase, strictly narrower than the stability
 goal (numeric separation only: no layers, no positions). -/
 def ForeignBorderDivergeStableSeparated : Prop :=
   ∀ {P : Params} {inp : Input} {o : Options}
     {lines : List (List Measure.Line)} {graph : Graph},
     measuredGraph P inp o lines = .ok graph →
     ∀ {comp : List Nat}, comp ∈ components graph →
     ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
       {orderOptions : OrderOptions},
     componentRun P (componentCandidate graph comp candidate) labels
       orderOptions = .ok run →
     ∀ {l1 l2 : List Nat}, l1 ∈ run.layers → l2 ∈ run.layers →
     ∀ {a b a' b' : Nat} {na nb na' nb' : ProperNode},
       run.coordinateProper.nodes[a]? = some na →
       run.coordinateProper.nodes[b]? = some nb →
       (na.node.border = -1 ∨ na.node.border = 1) →
       (nb.node.border = -1 ∨ nb.node.border = 1) →
       run.coordinateProper.nodes[a']? = some na' →
       run.coordinateProper.nodes[b']? = some nb' →
       (na'.node.border = -1 ∨ na'.node.border = 1) →
       (nb'.node.border = -1 ∨ nb'.node.border = 1) →
       na.node.clusterPath = na'.node.clusterPath →
       nb.node.clusterPath = nb'.node.clusterPath →
       Divergent na.node.clusterPath nb.node.clusterPath →
       (∀ {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat},
         na.node.clusterPath = Pa ++ A :: r1 →
         nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
         A ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
         B ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
         OrderImpl.Sibling.parentOf run.coordinateProper A =
           OrderImpl.Sibling.parentOf run.coordinateProper B) →
       ∀ {i j i' j' : Nat}, l1[i]? = some a → l1[j]? = some b →
         l2[i']? = some a' → l2[j']? = some b' →
         (i < j ↔ i' < j')

/-- Separated divergent sibling blocks keep their order on every layer pair:
no residual hypotheses. -/
theorem foreignBorderDivergeStableSeparated_holds :
    ForeignBorderDivergeStableSeparated := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions hrun
    l1 l2 hmem1 hmem2 a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hpathA hpathB
  intro hdiv hseps i j i' j' hi1 hj1 hi2 hj2
  obtain ⟨Pa, A, B, r1, r2, hA, hB, hAB⟩ := hdiv
  have hpa' : na'.node.clusterPath = Pa ++ A :: r1 := by
    rw [← hpathA]; exact hA
  have hpb' : nb'.node.clusterPath = Pa ++ B :: r2 := by
    rw [← hpathB]; exact hB
  have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  have hda : na.dummy = false :=
    dummy_false_of_border hwf hna hb1
  have hdb : nb.dummy = false :=
    dummy_false_of_border hwf hnb hb2
  have hda' : na'.dummy = false :=
    dummy_false_of_border hwf hna' hb1'
  have hdb' : nb'.dummy = false :=
    dummy_false_of_border hwf hnb' hb2'
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have horder' : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    unfold OrderImpl.order
    rw [horder]
    dsimp only
    rw [hlayers]
  obtain ⟨hmA, hmB, hpar⟩ := hseps hA hB hAB
  have hL := (OrderImpl.order_valid_layering _ _ _ horder').2
  have hnd1 : l1.Nodup := OrderImpl.layering_mem_nodup hL hmem1
  have hnd2 : l2.Nodup := OrderImpl.layering_mem_nodup hL hmem2

  have hne : (OrderImpl.Sibling.clusterIds run.coordinateProper).isEmpty = false := by
    cases hl : OrderImpl.Sibling.clusterIds run.coordinateProper with
    | nil => simp [hl] at hmA
    | cons _ _ => rfl
  obtain ⟨Y, hform⟩ := order_siblingForm run.coordinateProper orderOptions
    run.layers horder' hne
  have hnum : (OrderImpl.Sibling.siblingNumber run.coordinateProper
      (OrderImpl.Sibling.siblingOrders run.coordinateProper
        (OrderImpl.posOf run.coordinateProper Y))) A ≠
      (OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y))) B :=
    OrderImpl.siblingNumber_ne run.coordinateProper
      (OrderImpl.posOf run.coordinateProper Y) hmA hmB hAB hpar
  rw [hform] at hmem1 hmem2
  obtain ⟨Y1, hY1, e1mem⟩ := List.mem_map.mp hmem1
  obtain ⟨Y2, hY2, e2mem⟩ := List.mem_map.mp hmem2
  obtain ⟨k1, hk1⟩ := List.mem_iff_getElem?.mp hY1
  obtain ⟨k2, hk2⟩ := List.mem_iff_getElem?.mp hY2
  have hg1 : Y.getD k1 [] = Y1 := by simp [List.getD_eq_getElem?_getD, hk1]
  have hg2 : Y.getD k2 [] = Y2 := by simp [List.getD_eq_getElem?_getD, hk2]
  have e1 : OrderImpl.siblingLayer run.coordinateProper
      (OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k1 []) = l1 := by
    rw [hg1]; exact e1mem
  have e2 : OrderImpl.siblingLayer run.coordinateProper
      (OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k2 []) = l2 := by
    rw [hg2]; exact e2mem
  exact normalise_pair_stable e1 e2 hna hnb hna' hnb' hda hdb hda' hdb'
    hA hB hpa' hpb' hAB hnum hnd1 hnd2 hi1 hj1 hi2 hj2

end Elegant.Layered.PipelineImpl

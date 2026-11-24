import Elegant.Layered.ExactLoopEnvelopeRightProof
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExactLoopEnvelopeReserveProof
import Elegant.Layered.StrictMemberFrameProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem selectedAt {α : Type} (xs : List α) (keep : α → Bool)
    {i : Nat} {x : α} (hx : xs[i]? = some x) :
    (xs.zipIdx.filterMap (fun q => if keep q.1 then some q.2 else none)).contains i =
      keep x := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  constructor
  · intro hm
    obtain ⟨⟨y, j⟩, hj, he⟩ := List.mem_filterMap.mp hm
    change (if keep y then some j else none) = some i at he
    split at he
    · rename_i hy
      have hji := Option.some.inj he
      subst j
      have hyx : y = x := Option.some.inj
        ((List.mk_mem_zipIdx_iff_getElem?.mp hj).symm.trans hx)
      exact hyx ▸ hy
    · cases he
  · intro hk
    exact List.mem_filterMap.mpr ⟨(x, i), List.mem_zipIdx_iff_getElem?.mpr hx, by simp [hk]⟩

private theorem nonproxyRecord {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : ProperNode} (hn : run.coordinateProper.nodes[i]? = some node)
    (hb : ¬ (node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[i]? = some node ∧ run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 i node hn hb
  rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  exact ⟨hnode, by simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]⟩

private theorem coordinateRealNonproxy {P : Params} {exact : List Nat} {source : Proper}
    {i : Nat} {node : ProperNode}
    (hn : (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW).nodes[i]? = some node)
    (hd : node.dummy = false) (hb : ¬ (node.node.border = -2 ∨ node.node.border = 2)) :
    (coordinateGraphX P exact source).nodes[i]? = some node := by
  have htest : (node.node.border == -2 || node.node.border == 2) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    rcases Bool.or_eq_true_iff.mp h with hleft | hright
    · exact hb (Or.inl (beq_iff_eq.mp hleft))
    · exact hb (Or.inr (beq_iff_eq.mp hright))
  have hclear : clearF node = node := by simp [clearF, htest]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, clearProxyExtents_nodes, hn,
    Option.map_some, Nat.zero_add, hclear, hd, Bool.false_eq_true, ↓reduceIte]

private theorem coordinatePlainOwner {P : Params} {exact : List Nat} {source : Proper}
    {t : Nat} {owner : Node} (hn : source.nodes[t]? = some ⟨owner, false, none, false⟩)
    (hb : owner.border = 0) :
    ∃ actual : ProperNode, (coordinateGraphX P exact source).nodes[t]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = owner.clusterPath := by
  obtain ⟨actual, hsize, hd, hborder, hpath⟩ :
      ∃ actual : ProperNode, (sizeProperPortsX P exact source).nodes[t]? = some actual ∧
        actual.dummy = false ∧ actual.node.border = 0 ∧ actual.node.clusterPath = owner.clusterPath := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hn, Option.map_some]
    split <;> exact ⟨_, rfl, rfl, hb, rfl⟩
  have ht := (List.getElem?_eq_some_iff.mp hsize).1
  have htitle : (titleReservations (sizeProperPortsX P exact source)).nodes[t]? = some actual := by
    rw [titleReservations_nodes, List.getElem?_append_left (by simpa only [List.length_map] using ht)]
    simp [List.getElem?_map, hsize, titleF, hborder]
  obtain ⟨_, hprefix, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW).nodes[t]? = some actual := by
    rw [hprefix, List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  exact ⟨actual, coordinateRealNonproxy hplaced hd (by rw [hborder]; decide), hd, hborder, hpath⟩

private theorem plainMemberPath {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate t : Nat} {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hplain : owner.border = 0) (hpath : owner.clusterPath ≠ []) :
    ∃ box, inp.boxes[owner.decl]? = some box ∧
      owner.clusterPath = Compound.path inp.boxes box := by
  obtain ⟨key, _, hs⟩ := componentCandidate_nonempty_path_source howner hpath
  have hi : key < execution.graph0.nodes.length := by
    rw [← exactGraph_length execution.graph_eq]
    exact (List.getElem?_eq_some_iff.mp hs).1
  have hsource := List.getElem?_eq_getElem hi
  obtain ⟨actual, ha, hb, hp, hd⟩ := exactGraph_node_key execution.graph_eq hsource
  have he := Option.some.inj (ha.symm.trans hs)
  subst actual
  obtain ⟨nodes, edges, titles, hprepared, hlength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
  have hrecord := (congrArg (fun g : Graph => g.nodes[key]?) hprepared).symm.trans hsource
  have hzero : (execution.graph0.nodes[key]'hi).border = 0 := hb.symm.trans hplain
  have hk : key < nodes.length := by
    by_cases hk : key < nodes.length
    · exact hk
    · have hbot := (Compound.prepare_bottom_of_index _ _ _ _ key
        (by dsimp only; omega) hrecord).1
      omega
  have hboxIndex : key < inp.boxes.length := by omega
  have hbox := List.getElem?_eq_getElem hboxIndex
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hbox
  obtain ⟨hdecl, hpath'⟩ :=
    prepare_plain_path_origin _ _ _ _ hmetadata hrecord hzero hchangedBox
  exact ⟨_, by rwa [hd, hdecl], hp.trans (hpath'.trans hpathMap)⟩

private def loopRankNeed (cg : Graph) (labels : List MeasuredLabel) (p : Proper)
    (ys top heights : List Int) (q : Node × Nat) : Int :=
  let sizes := loopSizes cg.edges labels q.2 cg.slot
  let r := (rk p.rank q.2).toNat
  ys.getD q.2 0 + max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes) -
    top.getD r 0 - heights.getD r 0

private def loopRankExtraStep (cg : Graph) (exact : List Nat) (labels : List MeasuredLabel)
    (p : Proper) (ys top heights acc : List Int) (q : Node × Nat) : List Int :=
  if !exact.contains q.1.decl then acc
  else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
  else
    let r := (rk p.rank q.2).toNat
    acc.set r (max (acc.getD r 0) (loopRankNeed cg labels p ys top heights q))

private theorem setMax_mono (acc : List Int) (i r : Nat) (need : Int) :
    acc.getD r 0 ≤ (acc.set i (max (acc.getD i 0) need)).getD r 0 := by
  by_cases h : i = r
  · subst r
    by_cases hi : i < acc.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hi, Option.getD_some]
      exact Int.le_max_left _ _
    · simpa only [List.set_eq_of_length_le (Nat.le_of_not_gt hi)] using
        Int.le_refl (acc.getD i 0)
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, Int.le_refl]

private theorem loopRankExtra_bounds (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int)
    (rows : List (Node × Nat)) (acc : List Int) (r : Nat) :
    let out := rows.foldl (loopRankExtraStep cg exact labels p ys top heights) acc
    out.length = acc.length ∧ acc.getD r 0 ≤ out.getD r 0 ∧
      ∀ q ∈ rows, exact.contains q.1.decl = true →
        (loopSizes cg.edges labels q.2 cg.slot).isEmpty = false →
        (rk p.rank q.2).toNat = r → r < acc.length →
        loopRankNeed cg labels p ys top heights q ≤ out.getD r 0 := by
  induction rows generalizing acc with
  | nil => simp
  | cons x xs ih =>
    let next := loopRankExtraStep cg exact labels p ys top heights acc x
    have hstep : next.length = acc.length ∧ acc.getD r 0 ≤ next.getD r 0 := by
      unfold next loopRankExtraStep
      split
      · exact ⟨rfl, Int.le_refl _⟩
      · split
        · exact ⟨rfl, Int.le_refl _⟩
        · exact ⟨List.length_set, setMax_mono _ _ _ _⟩
    obtain ⟨hlen, hmono, hcover⟩ := ih next
    change (xs.foldl _ next).length = acc.length ∧
      acc.getD r 0 ≤ (xs.foldl _ next).getD r 0 ∧ _
    refine ⟨hlen.trans hstep.1, Int.le_trans hstep.2 hmono, ?_⟩
    intro q hq hex hsome hr hlt
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      have hnext : next.getD r 0 =
          max (acc.getD r 0) (loopRankNeed cg labels p ys top heights x) := by
        simp only [next, loopRankExtraStep, hex, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, hsome, hr, List.getD_eq_getElem?_getD, List.getElem?_set_self hlt,
          Option.getD_some]
      apply Int.le_trans (Int.le_max_right _ _)
      rw [← hnext]
      exact hmono
    · exact hcover q hq hex hsome hr (by rwa [hstep.1])

private def rankPrefix (sum : Int) : List Int → List Int
  | [] => []
  | x :: xs => sum :: rankPrefix (sum + x) xs

private theorem rankPrefix_fold (xs : List Int) (sum : Int) (acc : List Int) :
    (xs.foldl (fun a x => (a.1 + x, a.2 ++ [a.1])) (sum, acc)).2 =
      acc ++ rankPrefix sum xs := by
  induction xs generalizing sum acc with
  | nil => simp only [List.foldl_nil, rankPrefix, List.append_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [rankPrefix, List.append_assoc]

private theorem rankPrefix_lower (xs : List Int) (hn : ∀ x ∈ xs, 0 ≤ x)
    (sum : Int) {i : Nat} (hi : i < xs.length) :
    sum ≤ (rankPrefix sum xs).getD i 0 := by
  induction xs generalizing sum i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => exact Int.le_refl _
    | succ i =>
      have hi' : i < xs.length := by simp only [List.length_cons] at hi; omega
      have h := ih (fun y hy => hn y (List.mem_cons_of_mem _ hy)) (sum + x) hi'
      have hx := hn x List.mem_cons_self
      change sum ≤ (rankPrefix (sum + x) xs).getD i 0
      omega

private theorem rankPrefix_gain (xs : List Int) (hn : ∀ x ∈ xs, 0 ≤ x)
    (sum : Int) {r s : Nat} (hrs : r < s) (hs : s < xs.length) :
    (rankPrefix sum xs).getD r 0 + xs.getD r 0 ≤ (rankPrefix sum xs).getD s 0 := by
  induction xs generalizing sum r s with
  | nil => simp at hs
  | cons x xs ih =>
    have htail : ∀ y ∈ xs, 0 ≤ y := fun y hy => hn y (List.mem_cons_of_mem _ hy)
    cases s with
    | zero => omega
    | succ s =>
      have hs' : s < xs.length := by simp only [List.length_cons] at hs; omega
      cases r with
      | zero => exact rankPrefix_lower xs htail (sum + x) hs'
      | succ r => exact ih htail (sum + x) (Nat.lt_of_succ_lt_succ hrs) hs'

set_option maxHeartbeats 1400000 in
private theorem loopReservedBandStrict
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {r s : Nat} {lo hi : List Nat} (hrs : r < s)
    (hl : run.layers[r]? = some lo) (hh : run.layers[s]? = some hi) :
    run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper lo < run.top.getD s 0 ∧
    ∀ {t : Nat} {node : Node}, cg.nodes[t]? = some node →
      t < run.coordinateProper.nodes.length →
      (rk run.coordinateProper.rank t).toNat = r →
      (exactDecls exactIds inp).contains node.decl = true →
      (loopSizes cg.edges labels t cg.slot).isEmpty = false →
      run.ys.getD t 0 + ((loopSizes cg.edges labels t cg.slot).length : Int) *
        Loops.band cg.slot (loopSizes cg.edges labels t cg.slot) < run.top.getD s 0 := by
  have hrunG := hrun
  rw [componentRunX_eq_gen] at hrunG
  obtain ⟨_, _, _, _, yPre, topPre, ysPre, _, _, _, _, _, _, _, _, _, hry, hysPre,
    hreserve, _, _, _⟩ := componentRunGen_spec hrunG
  let heights := run.layers.map (CoordsImpl.layerHeight run.coordinateProper)
  let base := List.replicate topPre.length (0 : Int)
  let extra := cg.nodes.zipIdx.foldl (loopRankExtraStep cg (exactDecls exactIds inp)
    labels run.coordinateProper ysPre topPre heights) base
  let shifts := rankPrefix 0 extra
  have hbounds (i : Nat) := loopRankExtra_bounds cg (exactDecls exactIds inp)
    labels run.coordinateProper ysPre topPre heights cg.nodes.zipIdx base i
  have hlen : extra.length = topPre.length := by
    simpa only [extra, base, List.length_replicate] using (hbounds r).1
  have hnn (i : Nat) : 0 ≤ extra.getD i 0 := by
    have hi := (hbounds i).2.1
    have hz : base.getD i 0 = 0 := by
      by_cases hb : i < topPre.length <;>
        simp [base, List.getD_eq_getElem?_getD, hb]
    change base.getD i 0 ≤ extra.getD i 0 at hi
    rwa [hz] at hi
  have hmemNN (x : Int) (hx : x ∈ extra) : 0 ≤ x := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    simpa only [List.getD_eq_getElem?_getD, hi, Option.getD_some] using hnn i
  have hshifts : (extra.foldl (fun a x => (a.1 + x, a.2 ++ [a.1]))
      (0, ([] : List Int))).2 = shifts := by
    simp only [rankPrefix_fold, List.nil_append, shifts]
  unfold reserveExactRanks at hreserve
  obtain ⟨topNew, htop, hreserve⟩ := bind_ok hreserve
  obtain ⟨ysNew, hys, hreserve⟩ := bind_ok hreserve
  have hpair := Except.ok.inj hreserve
  rw [show topNew = run.top from congrArg Prod.snd hpair] at htop
  rw [show ysNew = run.ys from congrArg Prod.fst hpair] at hys
  change topPre.zipIdx.mapM (fun q => Measure.checkedI32
    (q.1 + (extra.foldl (fun a x => (a.1 + x, a.2 ++ [a.1]))
      (0, ([] : List Int))).2.getD q.2 0)) = .ok run.top at htop
  change ysPre.zipIdx.mapM (fun q => Measure.checkedI32
    (q.1 + (extra.foldl (fun a x => (a.1 + x, a.2 ++ [a.1]))
      (0, ([] : List Int))).2.getD (rk run.coordinateProper.rank q.2).toNat 0)) = .ok run.ys at hys
  rw [hshifts] at htop hys
  have hTop (i : Nat) (hi : i < topPre.length) :
      run.top.getD i 0 = topPre.getD i 0 + shifts.getD i 0 := by
    have hi' := List.getElem?_eq_getElem hi
    obtain ⟨a, ha, haGet⟩ := (mapM_getElem? _ _ _ htop).2 i (topPre[i], i)
      (by simp only [List.getElem?_zipIdx, hi', Option.map_some, Nat.zero_add])
    simpa only [List.getD_eq_getElem?_getD, hi', haGet, Option.getD_some] using
      Measure.checkedI32_ok ha
  have hY (i : Nat) (hi : i < ysPre.length) :
      run.ys.getD i 0 = ysPre.getD i 0 + shifts.getD (rk run.coordinateProper.rank i).toNat 0 := by
    have hi' := List.getElem?_eq_getElem hi
    obtain ⟨a, ha, haGet⟩ := (mapM_getElem? _ _ _ hys).2 i (ysPre[i], i)
      (by simp only [List.getElem?_zipIdx, hi', Option.map_some, Nat.zero_add])
    simpa only [List.getD_eq_getElem?_getD, hi', haGet, Option.getD_some] using
      Measure.checkedI32_ok ha
  have htopLen := (CoordsImpl.rankCoordsWith_length hry).2
  have hs : s < topPre.length := htopLen ▸ (List.getElem?_eq_some_iff.mp hh).1
  have hr := Nat.lt_trans hrs hs
  have hgain : shifts.getD r 0 + extra.getD r 0 ≤ shifts.getD s 0 :=
    rankPrefix_gain extra hmemNN 0 hrs (by rwa [hlen])
  have hgap := rankAxis_band_top_strict hry r s lo hi hrs hl hh
  rw [hTop s hs]
  constructor
  · rw [hTop r hr]
    have := hnn r
    omega
  · intro t node ht htLen htRank hselected hsize
    have hyLen : ysPre.length = run.coordinateProper.nodes.length := by
      rw [← hysPre]
      unfold proxyYs
      rw [List.length_map, List.length_zipIdx]
      exact (CoordsImpl.rankCoordsWith_length hry).1
    rw [hY t (by rwa [hyLen]), htRank]
    have hcover := (hbounds r).2.2 (node, t) (List.mem_zipIdx_iff_getElem?.mpr ht)
      hselected hsize htRank (by simpa only [base, List.length_replicate] using hr)
    change loopRankNeed cg labels run.coordinateProper ysPre topPre heights (node, t) ≤
      extra.getD r 0 at hcover
    have hheight : heights.getD r 0 = CoordsImpl.layerHeight run.coordinateProper lo := by
      simp only [heights, List.getD_eq_getElem?_getD, List.getElem?_map, hl, Option.map_some,
        Option.getD_some]
    simp only [loopRankNeed, htRank, hheight] at hcover
    have hmax := Int.le_max_right node.h
      (((loopSizes cg.edges labels t cg.slot).length : Int) *
        Loops.band cg.slot (loopSizes cg.edges labels t cg.slot))
    omega

private theorem plainReserveBeforeSide {P : Params} {exact : List Nat} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {t side : Nat} {owner marker : ProperNode}
    (ht : run.coordinateProper.nodes[t]? = some owner) (ht0 : owner.node.border = 0)
    (hm : run.coordinateProper.nodes[side]? = some marker)
    (hm1 : marker.node.border = 1)
    {layer : List Nat} (hl : layer ∈ run.layers) {i j : Nat}
    (hi : layer[i]? = some t) (hj : layer[j]? = some side) (hij : i < j) :
    let rect := Labels.rectAt run.proper run.xs run.ys
    (rect t).x + (rect t).w + (owner.node.loopExtent : Int) ≤ (rect side).x := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hpad, hshape, hsizes, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
  have hn : i + 1 < layer.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  let next := layer[i + 1]
  have hnext : layer[i + 1]? = some next := List.getElem?_eq_getElem hn
  have hnCoord := CoordsImpl.layers_mem_lt hshape hl hnext
  have hnextNode := List.getElem?_eq_getElem hnCoord
  have hnoTitle : CoordsImpl.ownTitleAnchor run.coordinateProper t next = false := by
    simp [CoordsImpl.ownTitleAnchor, ht, hnextNode, ht0]
  have hgap := CoordsImpl.clusterGap_ge_min (ng := P.nodeGap) (cp := P.clusterPad)
    _ _ _ hnoTitle
  have hpos : 1 ≤ min P.nodeGap P.clusterPad := by omega
  let half (v : Nat) := Int.fdiv (CoordsImpl.nodeW run.coordinateProper v) 2
  have hadj := CoordsImpl.cluster_balance_separated hcross layer hl i t next hi hnext
  change half t + half next + CoordsImpl.clusterGap P.nodeGap P.clusterPad
      run.coordinateProper t next ≤
    run.coordinateXs.getD next 0 - run.coordinateXs.getD t 0 at hadj
  have hspan : half t + half side + 1 ≤
      run.coordinateXs.getD side 0 - run.coordinateXs.getD t 0 := by
    by_cases heq : i + 1 = j
    · have he : next = side := Option.some.inj (hnext.symm.trans (by rwa [heq]))
      rw [he] at hadj hgap
      omega
    · have htail := CoordsImpl.cluster_zero_pairs_separated hcross layer hl
        (i + 1) j next side (by omega) hnext hj
      change half next + half side ≤
        run.coordinateXs.getD side 0 - run.coordinateXs.getD next 0 at htail
      have hwidth := CoordsImpl.nodeW_nonneg hsizes next
      have hhalf : 0 ≤ half next := Int.fdiv_nonneg hwidth (by decide)
      omega
  obtain ⟨htProper, hxt⟩ := nonproxyRecord hrun ht (by rw [ht0]; decide)
  obtain ⟨hmProper, hxm⟩ := nonproxyRecord hrun hm (by rw [hm1]; decide)
  have htW : CoordsImpl.nodeW run.coordinateProper t =
      owner.node.w + 2 * (owner.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, ht]
  have hmW : CoordsImpl.nodeW run.coordinateProper side =
      marker.node.w + 2 * (marker.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hm]
  change (Labels.rectAt run.proper run.xs run.ys t).x +
    (Labels.rectAt run.proper run.xs run.ys t).w + (owner.node.loopExtent : Int) ≤
      (Labels.rectAt run.proper run.xs run.ys side).x
  have hfdiv (x : Int) : Int.fdiv x 2 = x / 2 :=
    Int.fdiv_eq_ediv_of_nonneg x (by decide)
  have hshift (w : Int) (extent : Nat) :
      (w + 2 * (extent : Int)) / 2 = w / 2 + (extent : Int) :=
    Int.add_mul_ediv_left w (extent : Int) (by decide)
  simp only [half, htW, hmW, hfdiv, hshift] at hspan
  rw [← hxt, ← hxm] at hspan
  simp only [rectAt_eq, RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, htProper,
    hmProper, hfdiv]
  have hround : owner.node.w ≤ 2 * (owner.node.w / 2) + 1 := by omega
  have hmExtent : 0 ≤ (marker.node.loopExtent : Int) := Int.natCast_nonneg _
  omega

/-- A nonexact plain owner reserves the complete vertical loop stack in its frame. -/
theorem exactNonforwardPlainAncestor_nonexact_height
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t : Nat} {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hplain : owner.border = 0) (hnotExact : run.exact.contains t = false)
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t) :
    (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured t).h =
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).h := by
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨edge, hmem, ht, hh⟩ := hloop
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  have hself := ht.trans hh.symm
  rw [← ht] at howner hnotExact ⊢
  have hborder : (cg.nodes.getD edge.tail default).border ≠ -2 := by
    simp [cg, List.getD_eq_getElem?_getD, howner, hplain]
  have hstack := XLEM_plainReserve_holds exactIds inp o res execution comp candidate
    run orderOptions cg k edge hcomp rfl hrun hk hself hborder hnotExact
  exact Int.max_eq_left hstack

set_option maxHeartbeats 2400000 in
/-- Every ancestor frame strictly contains the full loop footprint of a plain
owner in an admitted exact component run. -/
theorem exactNonforwardPlainAncestor_strict
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner ancestor : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hplain : owner.border = 0)
    (hancestor : (componentCandidate execution.graph comp candidate).nodes[pos]? = some ancestor)
    (hgroup : ancestor.border = -2) (hanc : ancestor.decl ∈ owner.clusterPath)
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).StrictInside
      (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured t) := by
  let cg := componentCandidate execution.graph comp candidate
  let P := execution.params
  let exactDecl := exactDecls exactIds inp
  let rect := Labels.rectAt run.proper run.xs run.ys
  let frame := frameRect P cg run pos
  let foot := loopFootprintExt cg run execution.measured t
  have hownerPath : owner.clusterPath ≠ [] := by
    intro h
    rw [h] at hanc
    exact List.not_mem_nil hanc
  obtain ⟨box, hbox, hpath⟩ := plainMemberPath execution howner hplain hownerPath
  obtain ⟨groupBox, hgroupBox, hgroupPath⟩ :=
    X_cg_group_box execution.graph0_eq execution.graph_eq hancestor hgroup
  have hpref : ancestor.clusterPath <+: owner.clusterPath := by
    rw [hpath] at hanc
    rw [hgroupPath, hpath]
    exact Compound.path_ancestor_prefix (inputModel inp o) hwf hgroupBox hbox hanc
  obtain ⟨rr, source, bottom, hrr, hcoord, hkeys, hready, hrecords, hranks, htitle, hbottom⟩ :=
    X_group_bottom_source execution.graph0_eq execution.graph_eq hcomp hrun hancestor hgroup
  obtain ⟨botNode, hbot, hb2, hbPath, _, hbottomFind⟩ :=
    X_bottom_constraint_source execution.graph0_eq execution.graph_eq hkeys hrecords
      hancestor hgroup hbottom
  have hinside := List.contains_iff_mem.mpr hanc
  have hinterval := ranked_compound_member_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hancestor) hgroup hbottomFind
    (List.mk_mem_zipIdx_iff_getElem?.mpr howner) hplain hinside
  let titled := titleReservations (sizeProperPortsX P exactDecl source)
  let top : ProperNode × Nat := (titleF ⟨ancestor, false, none, false⟩, pos)
  have htPath : top.1.node.clusterPath = ancestor.clusterPath := (titleF_keys _).2.2.1
  have htBorder : top.1.node.border = -2 := (titleF_keys _).2.1.trans hgroup
  have hfind : (titled.nodes.zipIdx.find? fun q =>
      q.1.node.border == 2 && q.1.node.clusterPath == top.1.node.clusterPath) = some bottom := by
    rw [htPath]
    exact hbottom
  have hrank (i : Nat) (hi : i < cg.nodes.length) :
      rk titled.rank i = rk rr.ranks i ∧ rk run.coordinateProper.rank i = rk rr.ranks i := by
    have hrankRun : RankImpl.rank (Compound.rankingGraph cg) = .ok rr.ranks := by
      unfold RankImpl.rank
      rw [show rankWithBudget (Compound.rankingGraph cg) = .ok rr from hrr]
    obtain ⟨_, _, hshape, _⟩ := RankImpl.rank_spec hrankRun
    have hir : i < rr.ranks.length := by rw [hshape.1]; exact hi
    have hr := List.getElem?_eq_getElem hir
    have hs := hranks i rr.ranks[i] hr
    have ht : titled.rank[i]? = some rr.ranks[i] := by
      change (source.rank ++ _)[i]? = some rr.ranks[i]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hs).1]
      exact hs
    obtain ⟨_, hprefix⟩ := (coordinateGraphX_anchor_prefix P exactDecl source).2
    have hc : run.coordinateProper.rank[i]? = some rr.ranks[i] := by
      rw [← hcoord, hprefix, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hs).1]
      exact hs
    simp only [rk, List.getD_eq_getElem?_getD, hr, ht, hc, Option.getD_some, and_self]
  have hgRank := hrank pos (List.getElem?_eq_some_iff.mp hancestor).1
  have hoRank := hrank t (List.getElem?_eq_some_iff.mp howner).1
  have hbRank := hrank bottom.2 (List.getElem?_eq_some_iff.mp hbot).1
  let r := (rk rr.ranks t).toNat
  have hnn := rankWithBudget_rk_nonneg hrr t
  have hrEq : (r : Int) = rk rr.ranks t := Int.toNat_of_nonneg hnn
  obtain ⟨l, m, hl, hm, hlRank, hmRank⟩ :=
    addClusterBorders_rank_pair titled P.clusterBorderW hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitle) htBorder hfind
      (rank := r)
      (by dsimp only [top, r] at *; omega)
      (by dsimp only [r] at *; omega)
  let left := OrderImpl.borderLeft top P.clusterBorderW
  let right := OrderImpl.borderRight top P.clusterBorderW
  have hlNP : ¬ (left.node.border = -2 ∨ left.node.border = 2) := by
    change ¬ ((-1 : Int) = -2 ∨ (-1 : Int) = 2)
    decide
  have hmNP : ¬ (right.node.border = -2 ∨ right.node.border = 2) := by
    change ¬ ((1 : Int) = -2 ∨ (1 : Int) = 2)
    decide
  have hlC : run.coordinateProper.nodes[l]? = some left := by
    rw [← hcoord]
    exact coordinateRealNonproxy hl rfl hlNP
  have hmC : run.coordinateProper.nodes[m]? = some right := by
    rw [← hcoord]
    exact coordinateRealNonproxy hm rfl hmNP
  obtain ⟨actual, htC, hreal, ht0, haPath⟩ :=
    coordinatePlainOwner (P := P) (exact := exactDecl) (hrecords _ _ howner) hplain
  rw [hcoord] at htC
  have sideRank {i : Nat}
      (hsideRank : (OrderImpl.addClusterBorders titled P.clusterBorderW).rank[i]? =
        some (r : Int)) :
      OrderImpl.lay run.coordinateProper i = OrderImpl.lay run.coordinateProper t := by
    have h : rk run.coordinateProper.rank i = (r : Int) := by
      rw [← hcoord]
      change rk (OrderImpl.addClusterBorders titled P.clusterBorderW).rank i = _
      simp only [rk, List.getD_eq_getElem?_getD, hsideRank, Option.getD_some]
    unfold OrderImpl.lay
    rw [h, hrEq, hoRank.2]
  have hlNe : l ≠ t := by
    intro h
    rw [h] at hlC
    have hb := congrArg (fun n : ProperNode => n.node.border)
      (Option.some.inj (hlC.symm.trans htC))
    change (-1 : Int) = actual.node.border at hb
    omega
  have hmNe : m ≠ t := by
    intro h
    rw [h] at hmC
    have hb := congrArg (fun n : ProperNode => n.node.border)
      (Option.some.inj (hmC.symm.trans htC))
    change (1 : Int) = actual.node.border at hb
    omega
  obtain ⟨_, _, _, routed, _, _, _, ⟨ord, hord, hlayers⟩, _, hproxy, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hwellBordered : OrderImpl.BordersWellFormed run.coordinateProper := by
    rw [← hcoord]
    exact materializeDummyPaths_bordersWellFormed (clearProxyExtents_bordersWellFormed
      (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hprefix : top.1.node.clusterPath <+: actual.node.clusterPath := by
    rw [htPath, haPath]
    exact hpref
  have hbracket := ExecutedBorderOrder.bracket run.coordinateProper orderOptions ord
    hord hwellBordered l t m left actual right hlC htC hmC (sideRank hlRank) (sideRank hmRank)
    rfl rfl rfl hreal rfl hprefix hprefix hlNe hmNe
  obtain ⟨li, ti, mi, hli, hti, hmi, hlt, htm⟩ := hbracket.positions
  rw [hlayers] at hli hti hmi
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨hlF, _⟩ := nonproxyRecord hrun hlC hlNP
  obtain ⟨hmF, _⟩ := nonproxyRecord hrun hmC hmNP
  have htNP : ¬ (actual.node.border = -2 ∨ actual.node.border = 2) := by rw [ht0]; decide
  have hleftSep := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
    hcomp hrun hlayer hlt hli hti hlC htC hlNP htNP
  change (rect l).x + (rect l).w ≤ (rect t).x at hleftSep
  have hrightSep := plainReserveBeforeSide hrun htC ht0 hmC rfl hlayer hti hmi htm
  change (rect t).x + (rect t).w + (actual.node.loopExtent : Int) ≤ (rect m).x at hrightSep
  have hgGet : cg.nodes.getD pos default = ancestor := by
    simp only [cg, List.getD_eq_getElem?_getD, hancestor, Option.getD_some]
  have hgBorder : (cg.nodes.getD pos default).border = -2 := by rw [hgGet]; exact hgroup
  have hsidePath : top.1.node.clusterPath =
      Compound.path inp.boxes groupBox ++ [(cg.nodes.getD pos default).decl] := by
    rw [hgGet, htPath, hgroupPath]
  have hleftIn := frameRect_side_marker_contained (P := P) (cg := cg) (run := run)
    hgBorder (List.mk_mem_zipIdx_iff_getElem?.mpr hlF) (Or.inl rfl) hsidePath
  have hrightIn := frameRect_side_marker_contained (P := P) (cg := cg) (run := run)
    hgBorder (List.mk_mem_zipIdx_iff_getElem?.mpr hmF) (Or.inr rfl) hsidePath
  have hborderW : 0 < P.clusterBorderW :=
    Int.lt_of_lt_of_le (by decide : (0 : Int) < 1)
      (checkedParams_clusterBorderW_ge_one execution.checked)
  have hlw : 0 < (rect l).w := by
    change 0 < RouteImpl.nodeW run.proper l
    simp only [RouteImpl.nodeW, hlF, left, OrderImpl.borderLeft]
    exact hborderW
  have hmw : 0 < (rect m).w := by
    change 0 < RouteImpl.nodeW run.proper m
    simp only [RouteImpl.nodeW, hmF, right, OrderImpl.borderRight]
    exact hborderW
  have hnodes : run.proper.nodes = routed.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hproxyIn {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node)
      (hb : node.border = -2 ∨ node.border = 2) (hp : node.clusterPath = ancestor.clusterPath) :
      frame.y ≤ (rect i).y ∧ (rect i).y + (rect i).h ≤ frame.y + frame.h := by
    let original : ProperNode := ⟨node, false, none, false⟩
    let coord := clearF (titleF original)
    have hc : run.coordinateProper.nodes[i]? = some coord := by
      rw [← hcoord]
      exact X_coordinateGraph_marker_record (hrecords i node hn) hb rfl
    have hcBorder : coord.node.border = node.border :=
      (clearF_keys _).2.1.trans (titleF_keys _).2.1
    obtain ⟨_, _, _, _, hfinal, _, _, _⟩ :=
      proxyWidths_proxy_interval hproxy hc (by rw [hcBorder]; exact hb)
    rw [← hnodes] at hfinal
    have hcPath : coord.node.clusterPath = ancestor.clusterPath :=
      (clearF_keys _).2.2.1.trans ((titleF_keys _).2.2.1.trans hp)
    exact frameRect_member_vertical (P := P) (cg := cg) (run := run) hgBorder
      (List.mk_mem_zipIdx_iff_getElem?.mpr hfinal) (by
        change coord.node.clusterPath.contains _ = true
        rw [hcPath, hgGet, hgroupPath]
        simp)
  have htopIn := hproxyIn hancestor (Or.inl hgroup) rfl
  have hbottomIn := hproxyIn hbot (Or.inr hb2) hbPath
  have hgLen := componentRunX_original_nodes_covered hrun pos (List.getElem?_eq_some_iff.mp hancestor).1
  have htLen := componentRunX_original_nodes_covered hrun t (List.getElem?_eq_some_iff.mp howner).1
  have hbLen := componentRunX_original_nodes_covered hrun bottom.2 (List.getElem?_eq_some_iff.mp hbot).1
  obtain ⟨gLayer, hgLayer, _, _, hgBot⟩ := componentRunX_node_rank_band hrun hgLen
  obtain ⟨tLayer, htLayer, _, htTop, htBot⟩ := componentRunX_node_rank_band hrun htLen
  obtain ⟨bLayer, hbLayer, _, hbTop, _⟩ := componentRunX_node_rank_band hrun hbLen
  have htRank := X_proper_rank_eq_local hrun t
  have hposRank := X_proper_rank_eq_local hrun pos
  have hbottomRank := X_proper_rank_eq_local hrun bottom.2
  have hgt : (rk run.proper.rank pos).toNat < (rk run.proper.rank t).toNat := by
    rw [hposRank, htRank, hgRank.2, hoRank.2]
    dsimp only at hinterval
    have hgRankNN := rankWithBudget_rk_nonneg hrr pos
    omega
  have htb : (rk run.proper.rank t).toNat < (rk run.proper.rank bottom.2).toNat := by
    rw [htRank, hbottomRank, hoRank.2, hbRank.2]
    dsimp only at hinterval
    omega
  have hbefore := (loopReservedBandStrict hrun hgt hgLayer htLayer).1
  obtain ⟨hafter, hstack⟩ := loopReservedBandStrict hrun htb htLayer hbLayer
  have hownerGet : cg.nodes.getD t default = owner := by
    simp only [cg, List.getD_eq_getElem?_getD, howner, Option.getD_some]
  have hnotGroup : (cg.nodes.getD t default).border ≠ -2 := by rw [hownerGet, hplain]; decide
  have hownerFrame : frameRect P cg run t = rect t :=
    plain_frame_eq_boxRect P cg run t htLen hnotGroup
  have hfootX : foot.x = (rect t).x + (rect t).w := by
    change (frameRect P cg run t).x + (frameRect P cg run t).w = _
    rw [hownerFrame]
  have hfootY : foot.y = (rect t).y := by
    change (frameRect P cg run t).y = _
    rw [hownerFrame]
  have htComp : t < comp.length := by
    obtain ⟨key, hk, _⟩ := componentCandidate_nonempty_path_source howner hownerPath
    exact (List.getElem?_eq_some_iff.mp hk).1
  have hfootW : foot.w ≤ (actual.node.loopExtent : Int) := by
    have hwidth := XLEMR_cg_node_extent execution hcomp rfl hrun htComp howner
      (by rw [hownerGet]; exact hplain) htC
    have hEq : foot.w = (if run.exact.contains t then
        Loops.exactExtent cg.slot (loopSizes cg.edges execution.measured t cg.slot)
      else Loops.extent cg.slot (loopSizes cg.edges execution.measured t cg.slot)) := by
      change (if run.exact.contains t then Loops.exactExtent else Loops.extent) cg.slot _ = _
      cases run.exact.contains t <;> rfl
    rw [hEq]
    exact hwidth
  have hnodeSize := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.1
  have hposH : 0 ≤ (rect pos).h := (hnodeSize pos hgLen).2
  have hbotH : 0 ≤ (rect bottom.2).h := (hnodeSize bottom.2 hbLen).2
  have hownW : 0 ≤ (rect t).w := by
    rw [← hownerFrame]
    exact (frameRect_dims_nonneg P cg run t (componentRunX_dims_nonneg hrun) htLen).1
  change (rect pos).y + (rect pos).h ≤ _ at hgBot
  change _ ≤ (rect t).y at htTop
  change (rect t).y + (rect t).h ≤ _ at htBot
  change _ ≤ (rect bottom.2).y at hbTop
  change frame.StrictInside foot
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfootX]
    have hleftEdge := Int.lt_add_of_pos_right (rect l).x hlw
    exact Int.lt_of_lt_of_le
      (Int.lt_of_le_of_lt hleftIn.1 (Int.lt_of_lt_of_le hleftEdge hleftSep))
      (Int.le_add_of_nonneg_right hownW)
  · rw [hfootX]
    have hreserve : (rect t).x + (rect t).w + foot.w ≤ (rect m).x :=
      Int.le_trans (Int.add_le_add_left hfootW _) hrightSep
    have hrightEdge := Int.lt_add_of_pos_right (rect m).x hmw
    exact Int.lt_of_lt_of_le (Int.lt_of_le_of_lt hreserve hrightEdge) hrightIn.2.1
  · rw [hfootY]
    have h := htopIn.1
    omega
  · have h := hbottomIn.2
    cases hex : run.exact.contains t with
    | false =>
      have hh : foot.h = (rect t).h := by
        rw [← hownerFrame]
        exact exactNonforwardPlainAncestor_nonexact_height execution hcomp hrun
          howner hplain hex hloop
      rw [hfootY, hh]
      omega
    | true =>
      let sizes := loopSizes cg.edges execution.measured t cg.slot
      obtain ⟨edge, he, ht, hh⟩ := hloop
      have hsize : (stackSize cg.slot (routeLabels execution.measured edge.decl)) ∈ sizes := by
        unfold sizes loopSizes loopEdges
        exact List.mem_map.mpr ⟨edge, List.mem_filter.mpr ⟨he, by simp [ht, hh]⟩, rfl⟩
      have hSome : sizes.isEmpty = false := Bool.eq_false_iff.mpr fun he => by
        rw [List.isEmpty_iff.mp he] at hsize
        exact List.not_mem_nil hsize
      have hrunG := hrun
      rw [componentRunX_eq_gen] at hrunG
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hindices⟩ :=
        componentRunGen_spec hrunG
      have hselected : run.exact.contains t = (exactDecls exactIds inp).contains owner.decl := by
        rw [hindices]
        exact selectedAt cg.nodes (fun n => (exactDecls exactIds inp).contains n.decl) howner
      have hsel : (exactDecls exactIds inp).contains owner.decl = true := hselected.symm.trans hex
      have hStackBound := hstack howner (List.getElem?_eq_some_iff.mp htC).1
        (congrArg Int.toNat htRank.symm) hsel hSome
      have hfootH : foot.h = max (rect t).h ((sizes.length : Int) * Loops.band cg.slot sizes) := by
        change max (frameRect P cg run t).h _ = _
        rw [hownerFrame]
      change (rect t).y + (sizes.length : Int) * Loops.band cg.slot sizes < _ at hStackBound
      rw [hfootY, hfootH]
      omega

end Elegant.Layered.PipelineImpl

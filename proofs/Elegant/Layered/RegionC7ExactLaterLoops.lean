import Elegant.Layered.RegionFlatC7Selected

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private def exactLoopStackHeight (cg : Graph) (labels : List MeasuredLabel) (v : Nat) : Int :=
  let sizes := loopSizes cg.edges labels v cg.slot
  (sizes.length : Int) * Loops.band cg.slot sizes

private def exactLoopRankNeed (cg : Graph) (labels : List MeasuredLabel) (p : Proper)
    (ys top heights : List Int) (q : Node × Nat) : Int :=
  let r := (p.rank.getD q.2 0).toNat
  ys.getD q.2 0 + max q.1.h (exactLoopStackHeight cg labels q.2) -
    top.getD r 0 - heights.getD r 0

private def exactLoopRankStep (cg : Graph) (exact : List Nat) (labels : List MeasuredLabel)
    (p : Proper) (ys top heights : List Int) (acc : List Int) (q : Node × Nat) : List Int :=
  if !exact.contains q.1.decl then acc
  else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
  else
    let r := (p.rank.getD q.2 0).toNat
    acc.set r (max (acc.getD r 0) (exactLoopRankNeed cg labels p ys top heights q))

private theorem exactLoopRankStep_order (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights acc : List Int)
    (q : Node × Nat) :
    (exactLoopRankStep cg exact labels p ys top heights acc q).length = acc.length ∧
    ∀ i, acc.getD i 0 ≤ (exactLoopRankStep cg exact labels p ys top heights acc q).getD i 0 := by
  by_cases hx : (!exact.contains q.1.decl) = true
  · rw [exactLoopRankStep, ite_eq_left hx]
    exact ⟨rfl, fun _ => Int.le_refl _⟩
  · by_cases hl : (loopSizes cg.edges labels q.2 cg.slot).isEmpty = true
    · rw [exactLoopRankStep, ite_eq_right hx, ite_eq_left hl]
      exact ⟨rfl, fun _ => Int.le_refl _⟩
    · simp only [exactLoopRankStep, ite_eq_right hx, ite_eq_right hl]
      refine ⟨List.length_set, ?_⟩
      intro i
      let r := (p.rank.getD q.2 0).toNat
      change acc.getD i 0 ≤
        (acc.set r (max (acc.getD r 0) (exactLoopRankNeed cg labels p ys top heights q))).getD i 0
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
      by_cases he : r = i
      · subst i
        by_cases hr : r < acc.length
        · rw [ite_eq_left rfl, ite_eq_left hr, Option.getD_some]
          simp only [← List.getD_eq_getElem?_getD]
          exact Int.le_max_left _ _
        · have hnone : acc[r]? = none :=
            List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hr)
          rw [ite_eq_left rfl, ite_eq_right hr, hnone, Option.getD_none]
          exact Int.le_refl _
      · simp only [ite_eq_right he]
        exact Int.le_refl _

private theorem exactLoopRankFold_order (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int)
    (jobs : List (Node × Nat)) (acc : List Int) :
    let out := jobs.foldl (exactLoopRankStep cg exact labels p ys top heights) acc
    out.length = acc.length ∧ ∀ i, acc.getD i 0 ≤ out.getD i 0 := by
  induction jobs generalizing acc with
  | nil => exact ⟨rfl, fun _ => Int.le_refl _⟩
  | cons q rest ih =>
    let next := exactLoopRankStep cg exact labels p ys top heights acc q
    obtain ⟨hlen, hmono⟩ := exactLoopRankStep_order cg exact labels p ys top heights acc q
    obtain ⟨hlen', hmono'⟩ := ih next
    exact ⟨hlen'.trans hlen, fun i => Int.le_trans (hmono i) (hmono' i)⟩

private theorem exactLoopRankFold_owner (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int)
    {u : Nat} {node : Node} (hu : cg.nodes[u]? = some node)
    (hexact : exact.contains node.decl = true)
    (hloop : (loopSizes cg.edges labels u cg.slot).isEmpty = false)
    (hr : (rk p.rank u).toNat < top.length) :
    let r := (rk p.rank u).toNat
    exactLoopRankNeed cg labels p ys top heights (node, u) ≤
      (cg.nodes.zipIdx.foldl (exactLoopRankStep cg exact labels p ys top heights)
        (List.replicate top.length 0)).getD r 0 := by
  have hjob : (node, u) ∈ cg.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hu
  obtain ⟨before, after, hsplit⟩ := List.append_of_mem hjob
  let initial := List.replicate top.length (0 : Int)
  let step := exactLoopRankStep cg exact labels p ys top heights
  let prior := before.foldl step initial
  let r := (rk p.rank u).toNat
  have hprior : prior.length = top.length :=
    (exactLoopRankFold_order cg exact labels p ys top heights before initial).1.trans
      List.length_replicate
  have hstep : step prior (node, u) =
      prior.set r (max (prior.getD r 0) (exactLoopRankNeed cg labels p ys top heights (node, u))) := by
    have hmem : node.decl ∈ exact := List.contains_iff_mem.mp hexact
    simp [step, exactLoopRankStep, hmem, hloop, r, rk]
  have hidx : r < prior.length := hprior.symm ▸ hr
  have hhere : exactLoopRankNeed cg labels p ys top heights (node, u) ≤
      (step prior (node, u)).getD r 0 := by
    simp only [hstep, List.getD_eq_getElem?_getD, List.getElem?_set_self hidx, Option.getD_some]
    exact Int.le_max_right _ _
  change exactLoopRankNeed cg labels p ys top heights (node, u) ≤
    (cg.nodes.zipIdx.foldl step initial).getD r 0
  rw [hsplit, List.foldl_append, List.foldl_cons]
  exact Int.le_trans hhere
    ((exactLoopRankFold_order cg exact labels p ys top heights after (step prior (node, u))).2 r)

private def exactLoopRankPrefix (s : Int) : List Int → List Int
  | [] => []
  | e :: es => s :: exactLoopRankPrefix (s + e) es

private theorem exactLoopRankPrefix_fold (es : List Int) (s : Int) (out : List Int) :
    (es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2 =
      out ++ exactLoopRankPrefix s es := by
  induction es generalizing s out with
  | nil => simp only [List.foldl_nil, exactLoopRankPrefix, List.append_nil]
  | cons e rest ih =>
    simp only [List.foldl_cons, exactLoopRankPrefix]
    rw [ih]
    simp [List.append_assoc]

private theorem exactLoopRankPrefix_bounds (es : List Int) (s : Int)
    (hnonneg : ∀ i, 0 ≤ es.getD i 0) :
    (∀ j, j < es.length → s ≤ (exactLoopRankPrefix s es).getD j 0) ∧
    (∀ i j, i < j → j < es.length →
      (exactLoopRankPrefix s es).getD i 0 + es.getD i 0 ≤
        (exactLoopRankPrefix s es).getD j 0) := by
  induction es generalizing s with
  | nil => simp
  | cons e rest ih =>
    have he : 0 ≤ e := hnonneg 0
    obtain ⟨hbase, hgap⟩ := ih (s + e) (fun i => hnonneg (i + 1))
    constructor
    · intro j hj
      cases j with
      | zero => exact Int.le_refl _
      | succ j =>
        simp only [exactLoopRankPrefix, List.getD_cons_succ]
        exact Int.le_trans (by omega) (hbase j (Nat.lt_of_succ_lt_succ hj))
    · intro i j hij hj
      cases j with
      | zero => omega
      | succ j =>
        cases i with
        | zero => exact hbase j (Nat.lt_of_succ_lt_succ hj)
        | succ i => exact hgap i j (Nat.lt_of_succ_lt_succ hij) (Nat.lt_of_succ_lt_succ hj)

private theorem exactLoop_checked_shift_at {values shifts : List Int} {out : List Int}
    {rank : Nat → Nat} {i : Nat} (hi : i < values.length)
    (h : values.zipIdx.mapM (fun q => Measure.checkedI32 (q.1 + shifts.getD (rank q.2) 0)) =
      .ok out) :
    out.getD i 0 = values.getD i 0 + shifts.getD (rank i) 0 := by
  have hi' : values[i]? = some values[i] := List.getElem?_eq_getElem hi
  have hindex : (values.zipIdx)[i]? = some (values[i], i) := by
    simp only [List.getElem?_zipIdx, hi', Option.map_some, Nat.zero_add]
  obtain ⟨_, hval, hget⟩ := (mapM_getElem? _ _ _ h).2 i _ hindex
  simpa only [List.getD_eq_getElem?_getD, hget, hi', Option.getD_some] using
    (Measure.checkedI32_ok hval)

private theorem reserveExactRanks_exactLoop_bottom {cg : Graph} {exact : List Nat}
    {labels : List MeasuredLabel} {p : Proper} {layers : List (List Nat)}
    {ys top ys' top' : List Int}
    (hreserve : reserveExactRanks cg exact labels p layers ys top = .ok (ys', top'))
    {u s : Nat} {node : Node} {ownerLayer : List Nat}
    (hu : cg.nodes[u]? = some node) (hexact : exact.contains node.decl = true)
    (hloop : (loopSizes cg.edges labels u cg.slot).isEmpty = false)
    (hy : u < ys.length) (hs : s < top.length) (hrs : (rk p.rank u).toNat < s)
    (hrow : layers[(rk p.rank u).toNat]? = some ownerLayer)
    (hbase : top.getD (rk p.rank u).toNat 0 + CoordsImpl.layerHeight p ownerLayer ≤
      top.getD s 0) :
    ys'.getD u 0 + exactLoopStackHeight cg labels u ≤ top'.getD s 0 := by
  let heights := layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH p v)) 0
  let zero := List.replicate top.length (0 : Int)
  let extra := cg.nodes.zipIdx.foldl (exactLoopRankStep cg exact labels p ys top heights) zero
  let shifts := (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2
  let r := (rk p.rank u).toNat
  change ((do
    let topNew ← top.zipIdx.mapM fun (q : Int × Nat) =>
      Measure.checkedI32 (q.1 + shifts.getD q.2 0)
    let ysNew ← ys.zipIdx.mapM fun (q : Int × Nat) =>
      Measure.checkedI32 (q.1 + shifts.getD (p.rank.getD q.2 0).toNat 0)
    pure (ysNew, topNew)) : Except LayoutError (List Int × List Int)) =
      .ok (ys', top') at hreserve
  obtain ⟨topNew, htopMap, hreserve⟩ := bind_ok hreserve
  obtain ⟨ysNew, hysMap, hdone⟩ := bind_ok hreserve
  have hresult : (ysNew, topNew) = (ys', top') := Except.ok.inj hdone
  have ht := exactLoop_checked_shift_at (rank := id) hs htopMap
  have hv := exactLoop_checked_shift_at (rank := fun v => (p.rank.getD v 0).toNat) hy hysMap
  have htop : topNew = top' := congrArg Prod.snd hresult
  have hys : ysNew = ys' := congrArg Prod.fst hresult
  rw [htop] at ht
  rw [hys] at hv
  change top'.getD s 0 = top.getD s 0 + shifts.getD s 0 at ht
  change ys'.getD u 0 = ys.getD u 0 + shifts.getD r 0 at hv
  have hheights : heights.getD r 0 = CoordsImpl.layerHeight p ownerLayer := by
    rw [List.getD_eq_getElem?_getD]
    change ((layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH p v)) 0)[r]?).getD 0 = _
    rw [List.getElem?_map, hrow, Option.map_some, Option.getD_some]
    rfl
  have hneed := exactLoopRankFold_owner cg exact labels p ys top heights hu hexact hloop
    (Nat.lt_trans hrs hs)
  change ys.getD u 0 + max node.h (exactLoopStackHeight cg labels u) -
    top.getD r 0 - heights.getD r 0 ≤ extra.getD r 0 at hneed
  rw [hheights] at hneed
  have hstep := exactLoopRankFold_order cg exact labels p ys top heights cg.nodes.zipIdx zero
  have hextraLen : extra.length = top.length := hstep.1.trans List.length_replicate
  have hzero (n i : Nat) : 0 ≤ (List.replicate n (0 : Int)).getD i 0 := by
    induction n generalizing i with
    | zero => exact Int.le_refl _
    | succ n ih =>
      cases i with
      | zero => exact Int.le_refl _
      | succ j => exact ih j
  have hextra : ∀ i, 0 ≤ extra.getD i 0 := fun i => Int.le_trans (hzero top.length i) (hstep.2 i)
  have hprefix : shifts = exactLoopRankPrefix 0 extra := by
    simpa only [shifts, List.nil_append] using exactLoopRankPrefix_fold extra 0 []
  have hshift := (exactLoopRankPrefix_bounds extra 0 hextra).2 r s hrs
    (hextraLen.symm ▸ hs)
  rw [← hprefix] at hshift
  have hstack := Int.le_max_right node.h (exactLoopStackHeight cg labels u)
  change top.getD r 0 + CoordsImpl.layerHeight p ownerLayer ≤ top.getD s 0 at hbase
  omega

/-- The complete extended footprint of a plain, exact self-loop owner ends before
any later executed rank begins, including zero-size owner frames. -/
theorem componentRunR_exactPlainLoop_rank_cap {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions = .ok (cg', run))
    {u k : Nat} {node : Node} {edge : Edge} (hu : cg'.nodes[u]? = some node)
    (hplain : node.border = 0) (hexact : run.exact.contains u = true)
    (hk : cg'.edges[k]? = some edge) (htail : edge.tail = u) (hloop : edge.tail = edge.head) :
    ∀ s above, (rk run.proper.rank u).toNat < s → run.layers[s]? = some above →
      (loopFootprintExt cg' run labels u).y + (loopFootprintExt cg' run labels u).h ≤
        run.top.getD s 0 := by
  intro s above hrs hs
  obtain ⟨hband, hsep⟩ := componentRunR_plain_rank_bands hrun
  obtain ⟨ownerLayer, hrow, _, _, hframeBand⟩ := hband hu hplain
  have hframeCap := Int.le_trans hframeBand (hsep hrs hrow hs)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, _, ⟨y, top⟩, ysMid, stages⟩ :=
    componentRunR_stages hrun
  have hdecl : (exactDecls exactIds inp).contains node.decl = true := by
    rw [List.contains_iff_mem, stages.hExact, List.mem_filterMap] at hexact
    obtain ⟨⟨n, j⟩, hm, hget⟩ := hexact
    have hj : cg'.nodes[j]? = some n := List.mem_zipIdx_iff_getElem?.mp hm
    change (if (exactDecls exactIds inp).contains n.decl then some j else none) = some u at hget
    split at hget
    · next hn =>
        have he : j = u := Option.some.inj hget
        subst j
        have hnode := Option.some.inj (hj.symm.trans hu)
        simpa only [hnode] using hn
    · cases hget
  have hhead : edge.head = u := hloop.symm.trans htail
  have hmem : edge ∈ loopEdges cg'.edges u :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? hk, by simp [htail, hhead]⟩
  have hsize : (loopSizes cg'.edges labels u cg'.slot).isEmpty = false :=
    List.isEmpty_eq_false_iff_exists_mem.mpr
      ⟨stackSize cg'.slot (routeLabels labels edge.decl), List.mem_map.mpr ⟨edge, hmem, rfl⟩⟩
  have hrank : run.proper.rank = placed.rank := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel stages.hProxy).2.1
  have hlen : run.proper.nodes.length = placed.nodes.length := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
    exact (proxyWidths_rel stages.hProxy).2.2.1
  have huLen := componentRunR_original_nodes_covered hrun u (List.getElem?_eq_some_iff.mp hu).1
  have hysLen : ysMid.length = placed.nodes.length := by
    rw [← stages.hYsMid]
    simpa only [proxyYs, List.length_map, List.length_zipIdx] using
      (CoordsImpl.rankCoordsWith_length stages.hYt).1
  have htopLen := (CoordsImpl.rankCoordsWith_length stages.hYt).2
  have hsTop : s < top.length := htopLen.symm ▸ (List.getElem?_eq_some_iff.mp hs).1
  have huY : u < ysMid.length := by omega
  rw [hrank] at hrow hrs
  have hpre := CoordsImpl.rankAxis_bands_disjoint stages.hYt _ _ _ _ hrs hrow hs
  have hstackCap := reserveExactRanks_exactLoop_bottom stages.hReserve hu hdecl hsize huY hsTop
    hrs hrow hpre
  have hframeY : (frameRect default cg' run u).y = run.ys.getD u 0 := by
    unfold frameRect
    rw [List.getD_eq_getElem?_getD, hu]
    simp [hplain, nodeRect]
  change (frameRect default cg' run u).y + (frameRect default cg' run u).h ≤
    run.top.getD s 0 at hframeCap
  change (frameRect default cg' run u).y + max (frameRect default cg' run u).h
    (exactLoopStackHeight cg' labels u) ≤ run.top.getD s 0
  rw [hframeY] at hframeCap ⊢
  omega

theorem componentRunR_exactPlainLoop_miss_later_plain {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions = .ok (cg', run))
    {u v k : Nat} {nu nv : Node} {edge : Edge}
    (hu : cg'.nodes[u]? = some nu) (hv : cg'.nodes[v]? = some nv)
    (hbu : nu.border = 0) (hbv : nv.border = 0)
    (hexact : run.exact.contains u = true) (hk : cg'.edges[k]? = some edge)
    (htail : edge.tail = u) (hloop : edge.tail = edge.head)
    (horder : (rk run.proper.rank u).toNat < (rk run.proper.rank v).toNat) :
    ¬ (loopFootprintExt cg' run labels u).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) :=
  componentRunR_loopFootprint_miss_plain_other_rank hrun hu hv hbu hbv
    (Nat.ne_of_lt horder) (componentRunR_exactPlainLoop_rank_cap hrun hu hbu hexact hk htail hloop)

theorem r7Selected_exactLaterPlainLoop_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (pair : R7_SelectedRoutePair execution l b) {nu nv : Node}
    (hu : pair.cg.nodes[pair.edge.tail]? = some nu) (hv : pair.cg.nodes[pair.target]? = some nv)
    (hbu : nu.border = 0) (hbv : nv.border = 0)
    (hexact : pair.run.exact.contains pair.edge.tail = true) (hloop : pair.edge.tail = pair.edge.head)
    (horder : (rk pair.run.proper.rank pair.edge.tail).toNat <
      (rk pair.run.proper.rank pair.target).toNat) :
    R7_OverlapRowsXGap pair.rect (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  have hfoot := componentRunR_exactPlainLoop_miss_later_plain pair.run_eq hu hv hbu hbv hexact
    pair.edge_eq rfl hloop horder
  have hcgSlot := r7ComponentRun_slot_of_scene execution (comp := pair.part.1)
    (candidate := pair.candidate) pair.run_eq
  have hpos := componentRunR_slot_pos pair.run_eq
  have hs : 0 ≤ pair.cg.slot := by omega
  have hn := SceneExecutionR.measured_nonnegR execution
  have henv := pair.envelope_eq
  unfold labelEnvelope at henv
  obtain ⟨_, _, hrest⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (pair.edge.tail == pair.edge.head) = true := by simp [hloop]
  simp only [hb, hexact] at hrest
  have hcont := X_loopExactEnvelope_containedExt hs hn pair.edge_eq hloop
    (Option.some.inj hrest).symm hexact
  have hclear := Elegant.Layered.loop_branch_clear (v := pair.target) (r := pair.rect)
    pair.edge_eq hloop pair.envelope_eq hs hn (List.of_mem_zip pair.stack).2
    (Elegant.Layered.not_meetsInterior_of_contained hcont hfoot)
  unfold R7_OverlapRowsXGap
  intro hy hw₁ hw₂
  unfold Rect.meetsInterior at hclear
  omega

def R7_SelectedExactLaterPlainLoop {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box}
    (pair : R7_SelectedRoutePair execution l b) : Prop :=
  pair.edge.tail = pair.edge.head ∧
  pair.run.exact.contains pair.edge.tail = true ∧
  (rk pair.run.proper.rank pair.edge.tail).toNat < (rk pair.run.proper.rank pair.target).toNat ∧
  ∃ nu nv : Node, pair.cg.nodes[pair.edge.tail]? = some nu ∧
    pair.cg.nodes[pair.target]? = some nv ∧ nu.border = 0 ∧ nv.border = 0

end Elegant.Layered.PipelineImpl

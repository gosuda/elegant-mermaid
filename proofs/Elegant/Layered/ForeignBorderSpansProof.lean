import Elegant.Layered.ForeignSpansFacts

set_option autoImplicit false

/-!
# The group-vs-group foreign-span seam

This module discharges the open seam `ForeignBorderSpansSeparated`
(`Elegant/Layered/ForeignSpansFacts.lean`): for one executed component run, the
hulls of two distinct, mutually unrelated group declarations separate either on
`x` through the border-marker hulls or on `y` through the member hulls.

The assembly is proved from the executed-pipeline facts that already exist
(`componentRun_spec`, `componentRun_nonproxy_ordered_intervals`,
`rankAxis_node_in_band`, `rankAxis_bands_disjoint`, `proxyYs_getD`,
`pc_frame_flat`, `crossCoordsClusterWith_spec`, and the `boundsOf` hull lemmas
of `ForeignSpansFacts`) plus three named residual premises, one per pipeline
phase:

* `ForeignClusterRankSpans` (rank assignment): the member ranks of a group
  declaration lie inside a closed interval, and that declaration carries a
  left and a right border marker at every integer rank of the interval.
* `ForeignBorderLayerOrder` (the layer order feeding cluster separation): on
  each layer, the border markers of two distinct declarations do not interleave.
* `ForeignBorderChainXAligned` (cross-coordinate placement): the same-side
  markers of one declaration share one closed `x`-interval.

The nonnegativity ingredients are proved outright: every rank-axis band top
and every cross-coordinate centre of an executed run is nonnegative
(`fbs_run_top_nonneg`, `fbs_coordinate_centers_nonneg`).
-/

namespace Elegant.Layered.PipelineImpl

open CoordsImpl

/-! ## Residual premises, one pipeline phase each -/

/-- Rank-assignment residual: for two executed group declarations, each
declaration has a closed rank interval containing the ranks of all of its
member nodes (any node of the run whose cluster path contains the
declaration), and at every integer rank of the interval the coordinate graph
carries a left (`border = -1`) and a right (`border = 1`) border marker of that
declaration.  This is the executed `Compound.constraints`/`addClusterBorders`
rank content: constraint edges confine members between the title and bottom
proxies, and the border-chain fold emits a marker pair at each covered rank. -/
def ForeignClusterRankSpans : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
    ∃ (tU bU tW bW : Int),
      tU ≤ bU ∧ tW ≤ bW ∧
      (∀ v, v < run.proper.nodes.length →
        (run.proper.nodes.getD v default).node.clusterPath.contains
            uNode.decl = true →
        tU ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ bU) ∧
      (∀ v, v < run.proper.nodes.length →
        (run.proper.nodes.getD v default).node.clusterPath.contains
            wNode.decl = true →
        tW ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ bW) ∧
      (∀ r : Int, tU ≤ r → r ≤ bU →
        ∃ (mL mR : Nat) (nL nR : ProperNode),
          run.coordinateProper.nodes[mL]? = some nL ∧ nL.node.border = -1 ∧
            nL.node.clusterPath.getLast? = some uNode.decl ∧
            rk run.coordinateProper.rank mL = r ∧
            run.coordinateProper.nodes[mR]? = some nR ∧ nR.node.border = 1 ∧
            nR.node.clusterPath.getLast? = some uNode.decl ∧
            rk run.coordinateProper.rank mR = r) ∧
      (∀ r : Int, tW ≤ r → r ≤ bW →
        ∃ (mL mR : Nat) (nL nR : ProperNode),
          run.coordinateProper.nodes[mL]? = some nL ∧ nL.node.border = -1 ∧
            nL.node.clusterPath.getLast? = some wNode.decl ∧
            rk run.coordinateProper.rank mL = r ∧
            run.coordinateProper.nodes[mR]? = some nR ∧ nR.node.border = 1 ∧
            nR.node.clusterPath.getLast? = some wNode.decl ∧
            rk run.coordinateProper.rank mR = r)

/-- Cluster-separation-input residual (the layer order the cross-coordinate
pass consumes): on any layer of an executed run, the border markers of two
unrelated group declarations (neither lies on the cluster path of the other)
occupy disjoint position blocks — either every marker of
the first declaration precedes every marker of the second in the layer order,
or conversely.  This is the executed cluster-block contiguity of the ordering
phase; the pairwise separation itself is already proved
(`componentRun_nonproxy_ordered_intervals`). -/
def ForeignBorderLayerOrder : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 →
    uNode.decl ≠ wNode.decl →
    wNode.clusterPath.contains uNode.decl = false →
    uNode.clusterPath.contains wNode.decl = false →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    (∀ (i j a b : Nat) (na nb : ProperNode),
        layer[i]? = some a → layer[j]? = some b →
        run.coordinateProper.nodes[a]? = some na →
        run.coordinateProper.nodes[b]? = some nb →
        (na.node.border = -1 ∨ na.node.border = 1) →
        na.node.clusterPath.getLast? = some uNode.decl →
        (nb.node.border = -1 ∨ nb.node.border = 1) →
        nb.node.clusterPath.getLast? = some wNode.decl →
        i < j) ∨
    (∀ (i j a b : Nat) (na nb : ProperNode),
        layer[i]? = some a → layer[j]? = some b →
        run.coordinateProper.nodes[a]? = some na →
        run.coordinateProper.nodes[b]? = some nb →
        (na.node.border = -1 ∨ na.node.border = 1) →
        na.node.clusterPath.getLast? = some uNode.decl →
        (nb.node.border = -1 ∨ nb.node.border = 1) →
        nb.node.clusterPath.getLast? = some wNode.decl →
        j < i)

/-- Cross-coordinate-placement residual: in an executed run, two border
markers of one declaration and one side share the same closed `x`-interval.
This is the executed Brandes-Köpf border-chain alignment (`BorderChainUps` is
the named executed-pipeline premise that `borderChainBlock_of_ups` reduces
`BorderChainBlock` to); the statement is only about the final `x`-coordinates
of border-marker nodes. -/
def ForeignBorderChainXAligned : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {a b : Nat} {na nb : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      na.node.border = nb.node.border →
      na.node.clusterPath.getLast? = nb.node.clusterPath.getLast? →
      RouteImpl.leftOf run.proper run.xs a = RouteImpl.leftOf run.proper run.xs b ∧
        RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a =
          RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b

/-! ### Rect edges in `leftOf`/`nodeW`/`ys` terms -/

theorem fbs_rect_left (p : Proper) (xs ys : List Int) (a : Nat) :
    (Labels.rectAt p xs ys a).x = RouteImpl.leftOf p xs a := rfl

theorem fbs_rect_right (p : Proper) (xs ys : List Int) (a : Nat) :
    (Labels.rectAt p xs ys a).x + (Labels.rectAt p xs ys a).w =
      RouteImpl.leftOf p xs a + RouteImpl.nodeW p a := rfl

theorem fbs_rect_top (p : Proper) (xs ys : List Int) (a : Nat) :
    (Labels.rectAt p xs ys a).y = ys.getD a 0 := rfl

theorem fbs_rect_bottom (p : Proper) (xs ys : List Int) (a : Nat) :
    (Labels.rectAt p xs ys a).y + (Labels.rectAt p xs ys a).h =
      ys.getD a 0 + RouteImpl.nodeH p a := rfl

/-! ### Membership in the two hull inputs -/

theorem fbs_groupBorderRects_mem {cg : Graph} {run : Run} {decl : Nat} {a : Nat}
    {na : ProperNode} (hna : run.proper.nodes[a]? = some na)
    (hb : na.node.border = -1 ∨ na.node.border = 1)
    (ho : na.node.clusterPath.getLast? = some decl) :
    Labels.rectAt run.proper run.xs run.ys a ∈ groupBorderRects cg run decl := by
  apply List.mem_filterMap.mpr
  refine ⟨(na, a), List.mk_mem_zipIdx_iff_getElem?.mpr hna, ?_⟩
  rcases hb with hb | hb <;> simp [hb, ho]

theorem fbs_groupBorderRects_spec {cg : Graph} {run : Run} {decl : Nat} {r : Rect}
    (hmem : r ∈ groupBorderRects cg run decl) :
    ∃ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na ∧
      (na.node.border = -1 ∨ na.node.border = 1) ∧
      na.node.clusterPath.getLast? = some decl ∧
      r = Labels.rectAt run.proper run.xs run.ys a := by
  unfold groupBorderRects at hmem
  obtain ⟨q, hq, hsome⟩ := List.mem_filterMap.mp hmem
  have hna : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  split at hsome
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨h1 | h1, howner⟩
    · exact ⟨q.2, q.1, hna, Or.inl h1, howner, Option.some.inj hsome.symm⟩
    · exact ⟨q.2, q.1, hna, Or.inr h1, howner, Option.some.inj hsome.symm⟩
  · exact absurd hsome (by simp)

theorem fbs_groupMemberRects_mem {cg : Graph} {run : Run} {decl : Nat} {a : Nat}
    {na : ProperNode} (hna : run.proper.nodes[a]? = some na)
    (hc : na.node.clusterPath.contains decl = true) :
    Labels.rectAt run.proper run.xs run.ys a ∈ groupMemberRects cg run decl := by
  apply List.mem_filterMap.mpr
  refine ⟨(na, a), List.mk_mem_zipIdx_iff_getElem?.mpr hna, ?_⟩
  simp only [hc, ↓reduceIte]

theorem fbs_groupMemberRects_spec {cg : Graph} {run : Run} {decl : Nat} {r : Rect}
    (hmem : r ∈ groupMemberRects cg run decl) :
    ∃ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na ∧
      na.node.clusterPath.contains decl = true ∧
      r = Labels.rectAt run.proper run.xs run.ys a := by
  unfold groupMemberRects at hmem
  obtain ⟨q, hq, hsome⟩ := List.mem_filterMap.mp hmem
  have hna : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  split at hsome
  · rename_i hcond
    exact ⟨q.2, q.1, hna, hcond, Option.some.inj hsome.symm⟩
  · exact absurd hsome (by simp)

/-- Cluster-path membership phrased through `getD` matches the record form. -/
theorem fbs_contains_bridge {run : Run} {decl v : Nat} {na : ProperNode}
    (hnv : run.proper.nodes[v]? = some na)
    (hcv : na.node.clusterPath.contains decl = true) :
    (run.proper.nodes.getD v default).node.clusterPath.contains decl = true := by
  rw [List.getD_eq_getElem?_getD, hnv]
  exact hcv

/-- Cluster-path membership in `getD` form gives a record with the same
membership. -/
theorem fbs_contains_bridge' {run : Run} {decl v : Nat}
    (hcv : (run.proper.nodes.getD v default).node.clusterPath.contains decl = true) :
    ∃ na : ProperNode, run.proper.nodes[v]? = some na ∧
      na.node.clusterPath.contains decl = true := by
  by_cases hv : v < run.proper.nodes.length
  · refine ⟨run.proper.nodes[v], List.getElem?_eq_getElem hv, ?_⟩
    have hgd : run.proper.nodes.getD v default = run.proper.nodes[v] := by
      simp [List.getD_eq_getElem?_getD, hv]
    rw [← hgd]
    exact hcv
  · cases hv2 : run.proper.nodes[v]? with
    | none =>
      rw [List.getD_eq_getElem?_getD, hv2] at hcv
      exact absurd (show false = true from hcv) (by decide)
    | some nv =>
      rw [List.getD_eq_getElem?_getD, hv2, Option.getD_some] at hcv
      exact ⟨nv, rfl, hcv⟩

/-! ### The coordinate-graph record behind a run node -/

/-- Every node record of `run.proper` has a coordinate-graph record with the
same border and height; when the border is plain the whole record (in
particular the cluster path) is preserved. -/
theorem fbs_coordinate_record {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp) :
    ∃ nvc : ProperNode, run.coordinateProper.nodes[v]? = some nvc ∧
      nvc.node.border = nvp.node.border ∧ nvc.node.h = nvp.node.h ∧
      (¬(nvc.node.border = -2 ∨ nvc.node.border = 2) →
        nvc.node.clusterPath = nvp.node.clusterPath) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hrec).1
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hcadr : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
    List.getElem?_eq_getElem hvC
  obtain ⟨nd', hnd', -, hb', hh'⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 v _ hcadr
  have hnd2 : run.proper.nodes[v]? = some nd' := by rw [← hdrop]; exact hnd'
  have hnde : nd' = nvp := Option.some.inj (hnd2.symm.trans hrec)
  rw [hnde] at hb' hh'
  refine ⟨run.coordinateProper.nodes[v], hcadr, hb'.symm, hh'.symm, ?_⟩
  intro hnp
  obtain ⟨hfull, -⟩ := componentRun_nonproxy_record hrun hcadr hnp
  have := Option.some.inj (hrec.symm.trans hfull)
  rw [← this]

/-! ### Nonnegative rank-axis band tops -/

theorem fbs_topsFrom01_nonneg :
    ∀ (hs ss : List Int) (t : Int), 0 ≤ t → (∀ x ∈ hs, 0 ≤ x) → (∀ x ∈ ss, 0 ≤ x) →
      ∀ x ∈ CoordsImpl.topsFrom 0 1 t hs ss, 0 ≤ x := by
  intro hs
  induction hs with
  | nil =>
    intro ss _ _ _ _ x hx
    simp only [CoordsImpl.topsFrom] at hx
    cases hx
  | cons h hs' ih =>
    intro ss t ht hh hss x hx
    cases ss with
    | nil =>
      cases hs' with
      | nil =>
        simp only [CoordsImpl.topsFrom, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ht
        · cases hx
      | cons h2 hs'' =>
        simp only [CoordsImpl.topsFrom] at hx
        cases hx
    | cons s ss' =>
      simp only [CoordsImpl.topsFrom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ht
      · refine ih ss' _ ?_ (fun y hy => hh y (List.mem_cons_of_mem _ hy))
          (fun y hy => hss y (List.mem_cons_of_mem _ hy)) x hx
        have h1 := hh h (List.mem_cons_self ..)
        have h2 := hss s (List.mem_cons_self ..)
        omega

theorem fbs_run_top_nonneg {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) :
    ∀ k : Nat, 0 ≤ run.top.getD k 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hry, _, _⟩ := componentRun_spec hrun
  obtain ⟨hg, hslot, _, hsnn, _, htop, _⟩ := CoordsImpl.rankCoordsWith_spec hry
  have hheights : ∀ x ∈ run.layers.map (CoordsImpl.layerHeight run.coordinateProper),
      0 ≤ x := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
    exact CoordsImpl.layerHeight_nonneg _ _
  have hsteps : ∀ x ∈ CoordsImpl.rankSteps P.rankGap P.slot run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)), 0 ≤ x :=
    CoordsImpl.rankSteps_nonneg (by omega) (by omega) _ _ _ hsnn
  intro k
  rw [htop, List.getD_eq_getElem?_getD]
  cases hk : (CoordsImpl.topsFrom 0 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots))))[k]? with
  | none => exact Int.le_refl 0
  | some t =>
    exact fbs_topsFrom01_nonneg _ _ _ (Int.le_refl 0) hheights hsteps t
      (List.mem_of_getElem? hk)

/-! ### Nonnegative cross-coordinate centres -/

theorem fbs_foldl_min_le_of_mem {f : Nat → Int} : ∀ {L : List Nat} {v : Nat}, v ∈ L →
    ∀ (init : Int), L.foldl (fun m x => min m (f x)) init ≤ f v := by
  intro L
  induction L with
  | nil => intro v hv; cases hv
  | cons a as ih =>
    intro v hv init
    rcases List.mem_cons.mp hv with rfl | hm
    · have hle : ∀ (L : List Nat) (m : Int), L.foldl (fun x y => min x (f y)) m ≤ m := by
        intro L
        induction L with
        | nil => intro m; exact Int.le_refl m
        | cons b bs ihb =>
            intro m
            simp only [List.foldl_cons]
            exact Int.le_trans (ihb (min m (f b))) (Int.min_le_left _ _)
      simp only [List.foldl_cons]
      exact Int.le_trans (hle as (min init (f v))) (Int.min_le_right _ _)
    · simp only [List.foldl_cons]
      exact ih hm _

theorem fbs_cluster_pass_nonneg {ng cp : Int} {q : Proper} {layers : List (List Nat)}
    {marked : Array Bool} {k : Nat} {x : Array Int}
    (h : clusterPass ng cp q layers marked k = .ok x) :
    x.size = q.nodes.length ∧ ∀ v, v < x.size → 0 ≤ x[v]! := by
  have hn : (clusterCtx ng cp q layers marked k).n = q.nodes.length := rfl
  unfold clusterPass runPass at h
  split at h
  · simp at h
  · rename_i st _
    dsimp only at h
    split at h
    · simp at h
    · have hinj : (List.range (clusterCtx ng cp q layers marked k).n).toArray.map
          (fun v => finalX st (offsetsOf (clusterCtx ng cp q layers marked k) st)
              (k % 2 == 1) v -
            lowest (clusterCtx ng cp q layers marked k) st
              (offsetsOf (clusterCtx ng cp q layers marked k) st) (k % 2 == 1)) = x := by
        exact Except.ok.inj h
      subst hinj
      refine ⟨by simp [Array.size_map, hn], ?_⟩
      intro v hv
      have hvn : v < (clusterCtx ng cp q layers marked k).n := by
        simpa [Array.size_map] using hv
      have h1 : v < (List.range (clusterCtx ng cp q layers marked k).n).toArray.size := by
        simpa using hvn
      have h2 : v < (List.range (clusterCtx ng cp q layers marked k).n).length := by
        simpa using h1
      have h5 : v < ((List.range (clusterCtx ng cp q layers marked k).n).toArray.map
          (fun v => finalX st (offsetsOf (clusterCtx ng cp q layers marked k) st)
              (k % 2 == 1) v -
            lowest (clusterCtx ng cp q layers marked k) st
              (offsetsOf (clusterCtx ng cp q layers marked k) st) (k % 2 == 1))).size := by
        simpa [Array.size_map] using h1
      rw [getElem!_pos _ v h5, Array.getElem_map _ h5, List.getElem_toArray h1,
        List.getElem_range h2]
      have hlow : lowest (clusterCtx ng cp q layers marked k) st
          (offsetsOf (clusterCtx ng cp q layers marked k) st) (k % 2 == 1) ≤
          finalX st (offsetsOf (clusterCtx ng cp q layers marked k) st) (k % 2 == 1) v :=
        fbs_foldl_min_le_of_mem (List.mem_range.mpr hvn) _
      omega

theorem fbs_bal4_nonneg {a b c d : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) : 0 ≤ bal4 a b c d := by
  simp only [bal4, sort4]
  exact Int.fdiv_nonneg (by omega) (by decide)

theorem fbs_balanceOffsets_nonneg (x0 x1 x2 x3 : Array Int) :
    0 ≤ (balanceOffsets x0 x1 x2 x3).o0 ∧ 0 ≤ (balanceOffsets x0 x1 x2 x3).o1 ∧
      0 ≤ (balanceOffsets x0 x1 x2 x3).o2 ∧ 0 ≤ (balanceOffsets x0 x1 x2 x3).o3 := by
  unfold balanceOffsets
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Every cross-coordinate centre of an executed run is nonnegative: each of
the four Brandes-Köpf passes is normalized by its lowest placement, the
balancing offsets are nonnegative, and `bal4` averages four nonnegative
values. -/
theorem fbs_coordinate_centers_nonneg {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) :
    ∀ v : Nat, 0 ≤ run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨-, -, -, -, hcase⟩ := crossCoordsClusterWith_spec hcross
  rcases hcase with ⟨-, hxs⟩ | ⟨x0, x1, x2, x3, hpass, hxs⟩
  · rw [hxs]
    intro v
    simp
  · rw [hxs]
    unfold crossClusterPasses at hpass
    split at hpass
    · simp at hpass
    · next _ _ =>
      split at hpass
      · simp at hpass
      · dsimp only at hpass
        split at hpass
        · simp at hpass
        · next y0 h0 =>
          split at hpass
          · simp at hpass
          · next y1 h1 =>
            split at hpass
            · simp at hpass
            · next y2 h2 =>
              split at hpass
              · simp at hpass
              · next y3 h3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hpass
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hpass
                have hsz0 : y0.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h0).1
                have hsz1 : y1.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h1).1
                have hsz2 : y2.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h2).1
                have hsz3 : y3.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h3).1
                have hnn0 := (fbs_cluster_pass_nonneg h0).2
                have hnn1 := (fbs_cluster_pass_nonneg h1).2
                have hnn2 := (fbs_cluster_pass_nonneg h2).2
                have hnn3 := (fbs_cluster_pass_nonneg h3).2
                obtain ⟨o0, o1, o2, o3⟩ := fbs_balanceOffsets_nonneg y0 y1 y2 y3
                intro v
                by_cases hv : v < run.coordinateProper.nodes.length
                · rw [balanceValues_getD _ _ _ _ _ hv]
                  exact fbs_bal4_nonneg (by have := hnn0 v (by omega); omega)
                    (by have := hnn1 v (by omega); omega)
                    (by have := hnn2 v (by omega); omega)
                    (by have := hnn3 v (by omega); omega)
                · have hlen : (balanceValues run.coordinateProper.nodes.length y0 y1 y2
                        y3).length = run.coordinateProper.nodes.length := by
                    simp [balanceValues]
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
                  exact Int.le_refl 0

/-! ### Every node rect lies inside its rank band -/

theorem fbs_run_node_band {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) :
    ∀ v, v < run.proper.nodes.length →
      run.top.getD (rk run.proper.rank v).toNat 0 ≤ run.ys.getD v 0 ∧
        run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤
          run.top.getD (rk run.proper.rank v).toNat 0 +
            CoordsImpl.layerHeight run.coordinateProper
              (run.layers.getD (rk run.coordinateProper.rank v).toNat []) := by
  obtain ⟨_, _, _, _, _, _, hcoord, _, _, hproxy, hdrop, hroute, _, hry, hys, _⟩ :=
    componentRun_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  have hflat : ∀ (v : Nat) (nvc : ProperNode), run.coordinateProper.nodes[v]? = some nvc →
      (nvc.node.border = -2 ∨ nvc.node.border = 2) → nvc.node.h = 0 := by
    intro v nvc hrec hb
    exact pc_frame_flat (by rw [hcoord]; exact hrec) hb
  obtain ⟨_, _, _, _, _, _, hy⟩ := CoordsImpl.rankCoordsWith_spec hry
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    rw [hy]; simp
  intro v hv
  obtain ⟨nvp, hrec⟩ : ∃ nvp : ProperNode, run.proper.nodes[v]? = some nvp :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hvY : v < run.coordinateYs.length := by omega
  obtain ⟨nvc, hnc, hborderEq, hhEq, -⟩ := fbs_coordinate_record hrun hrec
  obtain ⟨lv, hly, hvIn, hrknn⟩ := hcov v hv
  rw [hrankEq] at hrknn
  have hrkC : rk run.coordinateProper.rank v =
      ((rk run.coordinateProper.rank v).toNat : Int) := by omega
  have hlyC : run.layers[(rk run.coordinateProper.rank v).toNat]? = some lv := by
    rw [← hrankEq]; exact hly
  have hlyD : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = lv := by
    rw [List.getD_eq_getElem?_getD, hlyC]
    rfl
  have hnodeH : RouteImpl.nodeH run.proper v = nvc.node.h := by
    simp only [RouteImpl.nodeH, hrec, ← hhEq]
  rw [hrankEq, ← hys, proxyYs_getD run.coordinateProper run.layers run.top
    run.coordinateYs hnc hvY]
  by_cases hb2 : nvc.node.border = -2 ∨ nvc.node.border = 2
  · have hnvcH : nvc.node.h = 0 := hflat v nvc hnc hb2
    have hlh : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lv :=
      CoordsImpl.layerHeight_nonneg _ _
    rcases hb2 with hb | hb
    · have hbeqT : (nvc.node.border == -2) = true := by rw [hb]; simp
      simp only [hbeqT, ↓reduceIte]
      rw [hlyD, hnodeH, hnvcH]
      constructor <;> omega
    · have hbeqF : (nvc.node.border == -2) = false := by rw [hb]; simp
      have hbeqT : (nvc.node.border == 2) = true := by rw [hb]; simp
      simp only [hbeqF, ↓reduceIte, hbeqT, ↓reduceIte]
      rw [hlyD, hnodeH, hnvcH]
      constructor <;> omega
  · obtain ⟨hrecFull, -⟩ := componentRun_nonproxy_record hrun hnc hb2
    have hnvp : nvp = nvc := Option.some.inj (hrec.symm.trans hrecFull)
    have hf1 : (nvc.node.border == -2) = false := by
      cases hc : nvc.node.border == -2 with
      | true => exact absurd (Or.inl (beq_iff_eq.mp hc)) hb2
      | false => rfl
    have hf2 : (nvc.node.border == 2) = false := by
      cases hc : nvc.node.border == 2 with
      | true => exact absurd (Or.inr (beq_iff_eq.mp hc)) hb2
      | false => rfl
    simp only [hf1, hf2]
    rw [hnodeH, hlyD]
    have hnH2 : CoordsImpl.nodeH run.coordinateProper v = nvc.node.h := by
      simp only [CoordsImpl.nodeH, hnc]
    have hband := rankAxis_node_in_band hry hlyC hvIn hvC hrkC
    rw [hnH2] at hband
    exact hband

/-! ### The group node itself is a member of its declaration -/

theorem fbs_group_node_member {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run)
    {u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hgroup : uNode.border = -2) :
    ∃ na : ProperNode, run.proper.nodes[u]? = some na ∧
      na.node.clusterPath.contains uNode.decl = true ∧
      Labels.rectAt run.proper run.xs run.ys u ∈ groupMemberRects
        (componentCandidate graph comp candidate) run uNode.decl := by
  obtain ⟨_, labeled, _bottom, _, hc, _, _, hrecords, _, _, _⟩ :=
    componentRun_group_bottom_source hgraph hcomp hrun hu hgroup
  have hlab : labeled.nodes[u]? = some ⟨uNode, false, none, false⟩ := hrecords u uNode hu
  have hcoordU : run.coordinateProper.nodes[u]? =
      some (clearF (titleF ⟨uNode, false, none, false⟩)) := by
    rw [← hc]; exact coordinateGraph_marker_record hlab (Or.inl hgroup) rfl
  have hb2 : (clearF (titleF ⟨uNode, false, none, false⟩)).node.border = -2 :=
    (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hgroup)
  obtain ⟨_owner, _span, _, _, hrecU, _, _, _⟩ :=
    componentRun_proxy_interval hrun hcoordU (Or.inl hb2)
  have hkeys : (clearF (titleF ⟨uNode, false, none, false⟩)).node.clusterPath =
      uNode.clusterPath := by
    rw [(clearF_keys _).2.2.1, (titleF_keys _).2.2.1]
  have hpathU : (run.proper.nodes.getD u default).node.clusterPath =
      uNode.clusterPath := by
    rw [List.getD_eq_getElem?_getD, hrecU]
    exact hkeys
  obtain ⟨_declEq, _original, hsource⟩ := componentCandidate_nonplain_source hu (by omega)
  obtain ⟨-, _box, -, -, hpathShape⟩ := measuredGraph_group_origin hgraph hsource hgroup
  have hcontains : (run.proper.nodes.getD u default).node.clusterPath.contains
      uNode.decl = true := by
    rw [hpathU, hpathShape]
    simp
  obtain ⟨na, hna, hcn⟩ := fbs_contains_bridge' hcontains
  exact ⟨na, hna, hcn, fbs_groupMemberRects_mem hna hcn⟩

/-! ### The `y` alternative: separated member rank ranges -/

theorem fbs_member_hulls_y_separated {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hry : rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)) = .ok (run.coordinateYs, run.top))
    {du dw : Nat}
    (hbelow : ∀ v, v < run.proper.nodes.length →
        (run.proper.nodes.getD v default).node.clusterPath.contains du = true →
        ∀ v', v' < run.proper.nodes.length →
          (run.proper.nodes.getD v' default).node.clusterPath.contains dw = true →
          rk run.proper.rank v < rk run.proper.rank v')
    (_hneU : groupMemberRects cg run du ≠ [])
    (hneW : groupMemberRects cg run dw ≠ []) :
    (boundsOf (groupMemberRects cg run du) []).bottom ≤
      (boundsOf (groupMemberRects cg run dw) []).minY := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  have hband := fbs_run_node_band hrun
  have htopnn := fbs_run_top_nonneg hrun
  have hpair : ∀ r ∈ groupMemberRects cg run du, ∀ r' ∈ groupMemberRects cg run dw,
      r.y + r.h ≤ r'.y := by
    intro r hr r' hr'
    obtain ⟨v, _na, hnvr, hcv, rfl⟩ := fbs_groupMemberRects_spec hr
    obtain ⟨v', _na', hnvr', hcv', rfl⟩ := fbs_groupMemberRects_spec hr'
    have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnvr).1
    have hvR' : v' < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnvr').1
    rw [fbs_rect_bottom, fbs_rect_top]
    obtain ⟨-, hupper⟩ := hband v hvR
    obtain ⟨lv, hly, -, hrknn⟩ := hcov v hvR
    obtain ⟨lv', hly', -, hrknn'⟩ := hcov v' hvR'
    have hlyD : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = lv := by
      rw [List.getD_eq_getElem?_getD, ← hrankEq, hly]
      rfl
    rw [hlyD] at hupper
    have hlt := hbelow v hvR (fbs_contains_bridge hnvr hcv) v' hvR'
      (fbs_contains_bridge hnvr' hcv')
    have hbands := rankAxis_bands_disjoint hry (rk run.proper.rank v).toNat
      (rk run.proper.rank v').toNat lv lv' (by omega) hly hly'
    obtain ⟨hlower', -⟩ := hband v' hvR'
    omega
  have hminYnonneg : 0 ≤ (boundsOf (groupMemberRects cg run dw) []).minY := by
    refine boundsOf_minY_ge_of_all hneW ?_
    intro r hr
    obtain ⟨v, _na, hnvr, -, rfl⟩ := fbs_groupMemberRects_spec hr
    have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnvr).1
    obtain ⟨hlower, -⟩ := hband v hvR
    rw [fbs_rect_top]
    have := htopnn (rk run.proper.rank v).toNat
    omega
  refine boundsOf_bottom_le_of_all hminYnonneg ?_
  intro r hr
  exact boundsOf_minY_ge_of_all hneW (fun r' hr' => hpair r hr r' hr')

/-! ### The `x` alternative: separated marker blocks on a shared layer -/

/-- If every marker of declaration `dl` at a shared rank is `leftOf`-separated
from every marker of declaration `dr` at that rank, then the whole border hull
of `dl` lies left of the whole border hull of `dr`: same-side alignment
transports each marker to its representative at the shared rank, and the
nonnegative centres plus the separation put the right declaration's hull at
nonnegative `x` (the `boundsOf` right edge is zero-initialized). -/
theorem fbs_x_hull_bound {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run)
    (halign : ForeignBorderChainXAligned)
    {dl dr : Nat}
    {pL pR qL qR : Nat} {npL npR nqL nqR : ProperNode}
    (hrecpL : run.coordinateProper.nodes[pL]? = some npL) (hbpL : npL.node.border = -1)
    (hopL : npL.node.clusterPath.getLast? = some dl)
    (hrecpR : run.coordinateProper.nodes[pR]? = some npR) (hbpR : npR.node.border = 1)
    (hopR : npR.node.clusterPath.getLast? = some dl)
    (hrecqL : run.coordinateProper.nodes[qL]? = some nqL) (hbqL : nqL.node.border = -1)
    (hopqL : nqL.node.clusterPath.getLast? = some dr)
    (hrecqR : run.coordinateProper.nodes[qR]? = some nqR) (hbqR : nqR.node.border = 1)
    (hopqR : nqR.node.clusterPath.getLast? = some dr)
    (hsep : ∀ p : Nat, p = pL ∨ p = pR → ∀ q : Nat, q = qL ∨ q = qR →
      RouteImpl.leftOf run.proper run.xs p + RouteImpl.nodeW run.proper p ≤
        RouteImpl.leftOf run.proper run.xs q) :
    (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dl) []).right ≤
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dr) []).minX
        := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hsizes := (crossCoordsClusterWith_spec hcross).2.2.2.1
  have hcenters := fbs_coordinate_centers_nonneg hrun
  have hneR : groupBorderRects (componentCandidate graph comp candidate) run dr ≠ [] := by
    intro hempty
    have hmem : Labels.rectAt run.proper run.xs run.ys qL ∈
        groupBorderRects (componentCandidate graph comp candidate) run dr :=
      fbs_groupBorderRects_mem
        (componentRun_border_record hrun hrecqL (Or.inl hbqL)).1 (Or.inl hbqL) hopqL
    rw [hempty] at hmem
    exact List.not_mem_nil hmem
  have hrepL : ∀ (a : Nat) (na : ProperNode),
      run.proper.nodes[a]? = some na → (na.node.border = -1 ∨ na.node.border = 1) →
      na.node.clusterPath.getLast? = some dl →
      ∃ (rep : Nat) (_ : ProperNode), (rep = pL ∨ rep = pR) ∧
        RouteImpl.leftOf run.proper run.xs a = RouteImpl.leftOf run.proper run.xs rep ∧
        RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a =
          RouteImpl.leftOf run.proper run.xs rep + RouteImpl.nodeW run.proper rep := by
    intro a na hna hb ho
    obtain ⟨nca, hcadr, hbca, -, hcp⟩ := fbs_coordinate_record hrun hna
    have hcp' : nca.node.clusterPath = na.node.clusterPath := by
      refine hcp ?_
      intro hcon
      rcases hcon with h | h <;> rw [h] at hbca <;> omega
    rcases hb with hb | hb
    · exact ⟨pL, npL, Or.inl rfl,
        (halign hgraph hcomp hrun (a := a) (b := pL) (na := nca) (nb := npL) hcadr hrecpL
          (Or.inl (hbca.trans hb)) (Or.inl hbpL)
          (hbca.trans (hb.trans hbpL.symm))
          (by rw [hcp']; exact ho.trans hopL.symm)).1,
        (halign hgraph hcomp hrun (a := a) (b := pL) (na := nca) (nb := npL) hcadr hrecpL
          (Or.inl (hbca.trans hb)) (Or.inl hbpL)
          (hbca.trans (hb.trans hbpL.symm))
          (by rw [hcp']; exact ho.trans hopL.symm)).2⟩
    · exact ⟨pR, npR, Or.inr rfl,
        (halign hgraph hcomp hrun (a := a) (b := pR) (na := nca) (nb := npR) hcadr hrecpR
          (Or.inr (hbca.trans hb)) (Or.inr hbpR)
          (hbca.trans (hb.trans hbpR.symm))
          (by rw [hcp']; exact ho.trans hopR.symm)).1,
        (halign hgraph hcomp hrun (a := a) (b := pR) (na := nca) (nb := npR) hcadr hrecpR
          (Or.inr (hbca.trans hb)) (Or.inr hbpR)
          (hbca.trans (hb.trans hbpR.symm))
          (by rw [hcp']; exact ho.trans hopR.symm)).2⟩
  have hrepR : ∀ (b : Nat) (nb : ProperNode),
      run.proper.nodes[b]? = some nb → (nb.node.border = -1 ∨ nb.node.border = 1) →
      nb.node.clusterPath.getLast? = some dr →
      ∃ (rep : Nat) (_ : ProperNode), (rep = qL ∨ rep = qR) ∧
        RouteImpl.leftOf run.proper run.xs b = RouteImpl.leftOf run.proper run.xs rep ∧
        RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b =
          RouteImpl.leftOf run.proper run.xs rep + RouteImpl.nodeW run.proper rep := by
    intro b nb hnb hb ho
    obtain ⟨ncb, hcbdr, hbcb, -, hcp⟩ := fbs_coordinate_record hrun hnb
    have hcp' : ncb.node.clusterPath = nb.node.clusterPath := by
      refine hcp ?_
      intro hcon
      rcases hcon with h | h <;> rw [h] at hbcb <;> omega
    rcases hb with hb | hb
    · exact ⟨qL, nqL, Or.inl rfl,
        (halign hgraph hcomp hrun (a := b) (b := qL) (na := ncb) (nb := nqL) hcbdr hrecqL
          (Or.inl (hbcb.trans hb)) (Or.inl hbqL)
          (hbcb.trans (hb.trans hbqL.symm))
          (by rw [hcp']; exact ho.trans hopqL.symm)).1,
        (halign hgraph hcomp hrun (a := b) (b := qL) (na := ncb) (nb := nqL) hcbdr hrecqL
          (Or.inl (hbcb.trans hb)) (Or.inl hbqL)
          (hbcb.trans (hb.trans hbqL.symm))
          (by rw [hcp']; exact ho.trans hopqL.symm)).2⟩
    · exact ⟨qR, nqR, Or.inr rfl,
        (halign hgraph hcomp hrun (a := b) (b := qR) (na := ncb) (nb := nqR) hcbdr hrecqR
          (Or.inr (hbcb.trans hb)) (Or.inr hbqR)
          (hbcb.trans (hb.trans hbqR.symm))
          (by rw [hcp']; exact ho.trans hopqR.symm)).1,
        (halign hgraph hcomp hrun (a := b) (b := qR) (na := ncb) (nb := nqR) hcbdr hrecqR
          (Or.inr (hbcb.trans hb)) (Or.inr hbqR)
          (hbcb.trans (hb.trans hbqR.symm))
          (by rw [hcp']; exact ho.trans hopqR.symm)).2⟩
  -- nonnegative left edges of the right declaration's markers
  have hzero : 0 ≤
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dr) []).minX
        := by
    refine boundsOf_minX_ge_of_all hneR ?_
    intro rb hrb
    obtain ⟨b, nb, hnb, hbb, hob, rfl⟩ := fbs_groupBorderRects_spec hrb
    rw [fbs_rect_left]
    obtain ⟨rep, _nrep, hrep, hle, _⟩ := hrepR b nb hnb hbb hob
    obtain ⟨hrecp, hxp⟩ := componentRun_border_record hrun hrecpL (Or.inl hbpL)
    have hnodeWp : 0 ≤ RouteImpl.nodeW run.proper pL := by
      have hw := (sizesNonneg_lookup hsizes pL npL hrecpL).1
      simp only [RouteImpl.nodeW, hrecp]
      omega
    have hfdiv : Int.fdiv (RouteImpl.nodeW run.proper pL) 2 ≤
        RouteImpl.nodeW run.proper pL := Int.fdiv_le_self 2 hnodeWp
    have hcenter : 0 ≤ run.xs.getD pL 0 := by
      rw [hxp]
      exact hcenters pL
    have hge : run.xs.getD pL 0 ≤ RouteImpl.leftOf run.proper run.xs pL +
        RouteImpl.nodeW run.proper pL := by
      simp only [RouteImpl.leftOf, RouteImpl.xAt]
      omega
    have hsep' := hsep pL (Or.inl rfl) rep hrep
    omega
  refine boundsOf_right_le_of_all hzero ?_
  intro ra hra
  obtain ⟨a, na, hna, hba, hoa, rfl⟩ := fbs_groupBorderRects_spec hra
  rw [fbs_rect_right]
  obtain ⟨rep, _nrep, hrep, _, hsum⟩ := hrepL a na hna hba hoa
  rw [hsum]
  refine boundsOf_minX_ge_of_all hneR ?_
  intro rb hrb
  obtain ⟨b, nb, hnb, hbb, hob, rfl⟩ := fbs_groupBorderRects_spec hrb
  rw [fbs_rect_left]
  obtain ⟨rep2, _nrep2, hrep2, hle2, _⟩ := hrepR b nb hnb hbb hob
  rw [hle2]
  exact hsep rep hrep rep2 hrep2

/-- Two declarations that carry markers at a common rank separate
horizontally: the layer-order residual fixes a global direction at that rank,
`componentRun_nonproxy_ordered_intervals` separates the four representative
pairs, and `fbs_x_hull_bound` transports the separation to the hulls. -/
theorem fbs_border_hulls_x_separated {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run)
    (horder : ForeignBorderLayerOrder) (halign : ForeignBorderChainXAligned)
    {u w : Nat} {uNode wNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hw : (componentCandidate graph comp candidate).nodes[w]? = some wNode)
    (hgroupU : uNode.border = -2) (hgroupW : wNode.border = -2)
    (hpathW : wNode.clusterPath.contains uNode.decl = false)
    (hpathU : uNode.clusterPath.contains wNode.decl = false)
    {du dw : Nat} (hdu : uNode.decl = du) (hdw : wNode.decl = dw)
    (hneDecl : du ≠ dw) {r : Int}
    {mUL mUR mWL mWR : Nat} {nUL nUR nWL nWR : ProperNode}
    (hUL : run.coordinateProper.nodes[mUL]? = some nUL) (hbUL : nUL.node.border = -1)
    (hoUL : nUL.node.clusterPath.getLast? = some du)
    (hrkUL : rk run.coordinateProper.rank mUL = r)
    (hUR : run.coordinateProper.nodes[mUR]? = some nUR) (hbUR : nUR.node.border = 1)
    (hoUR : nUR.node.clusterPath.getLast? = some du)
    (hrkUR : rk run.coordinateProper.rank mUR = r)
    (hWL : run.coordinateProper.nodes[mWL]? = some nWL) (hbWL : nWL.node.border = -1)
    (hoWL : nWL.node.clusterPath.getLast? = some dw)
    (hrkWL : rk run.coordinateProper.rank mWL = r)
    (hWR : run.coordinateProper.nodes[mWR]? = some nWR) (hbWR : nWR.node.border = 1)
    (hoWR : nWR.node.clusterPath.getLast? = some dw)
    (hrkWR : rk run.coordinateProper.rank mWR = r) :
    (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run du) []).right ≤
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dw) []).minX ∨
    (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dw) []).right ≤
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run du) []).minX
        := by
  subst hdu
  subst hdw
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  have hmUL : mUL < run.proper.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hUL).1; omega
  have hmUR : mUR < run.proper.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hUR).1; omega
  have hmWL : mWL < run.proper.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hWL).1; omega
  have hmWR : mWR < run.proper.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hWR).1; omega
  obtain ⟨layer, hly, hmULin, _hrknn⟩ := hcov mUL hmUL
  have hrkUL' : rk run.proper.rank mUL = r := by rw [hrankEq]; exact hrkUL
  have hlyr : run.layers[r.toNat]? = some layer := by rw [← hrkUL']; exact hly
  have hlayerMem : layer ∈ run.layers := List.mem_of_getElem? hly
  have hmURin : mUR ∈ layer := by
    obtain ⟨l2, hly2, hin, _⟩ := hcov mUR hmUR
    have hrkUR' : rk run.proper.rank mUR = r := by rw [hrankEq]; exact hrkUR
    rw [hrkUR'] at hly2
    have hl2 : l2 = layer := Option.some.inj (hly2.symm.trans hlyr)
    rw [hl2] at hin
    exact hin
  have hmWLin : mWL ∈ layer := by
    obtain ⟨l2, hly2, hin, _⟩ := hcov mWL hmWL
    have hrkWL' : rk run.proper.rank mWL = r := by rw [hrankEq]; exact hrkWL
    rw [hrkWL'] at hly2
    have hl2 : l2 = layer := Option.some.inj (hly2.symm.trans hlyr)
    rw [hl2] at hin
    exact hin
  have hmWRin : mWR ∈ layer := by
    obtain ⟨l2, hly2, hin, _⟩ := hcov mWR hmWR
    have hrkWR' : rk run.proper.rank mWR = r := by rw [hrankEq]; exact hrkWR
    rw [hrkWR'] at hly2
    have hl2 : l2 = layer := Option.some.inj (hly2.symm.trans hlyr)
    rw [hl2] at hin
    exact hin
  rcases horder hgraph hcomp hrun hu hw hgroupU hgroupW hneDecl hpathW hpathU hlayerMem
    with huFirst | hwFirst
  · refine Or.inl (fbs_x_hull_bound hgraph hcomp hrun halign hUL hbUL hoUL hUR hbUR hoUR
      hWL hbWL hoWL hWR hbWR hoWR ?_)
    intro p hp q hq
    obtain ⟨np, hprec, hbp, hop⟩ : ∃ np : ProperNode,
        run.coordinateProper.nodes[p]? = some np ∧
        (np.node.border = -1 ∨ np.node.border = 1) ∧
        np.node.clusterPath.getLast? = some uNode.decl := by
      rcases hp with rfl | rfl
      · exact ⟨nUL, hUL, Or.inl hbUL, hoUL⟩
      · exact ⟨nUR, hUR, Or.inr hbUR, hoUR⟩
    obtain ⟨nq, hqrec, hbq, hoq⟩ : ∃ nq : ProperNode,
        run.coordinateProper.nodes[q]? = some nq ∧
        (nq.node.border = -1 ∨ nq.node.border = 1) ∧
        nq.node.clusterPath.getLast? = some wNode.decl := by
      rcases hq with rfl | rfl
      · exact ⟨nWL, hWL, Or.inl hbWL, hoWL⟩
      · exact ⟨nWR, hWR, Or.inr hbWR, hoWR⟩
    obtain ⟨ip, hip⟩ := List.mem_iff_getElem?.mp (by
      rcases hp with rfl | rfl
      · exact hmULin
      · exact hmURin)
    obtain ⟨iq, hiq⟩ := List.mem_iff_getElem?.mp (by
      rcases hq with rfl | rfl
      · exact hmWLin
      · exact hmWRin)
    exact componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayerMem
      (huFirst ip iq p q np nq hip hiq hprec hqrec hbp hop hbq hoq) hip hiq hprec hqrec
      (by intro hcon; rcases hcon with h | h <;> omega)
      (by intro hcon; rcases hcon with h | h <;> omega)
  · refine Or.inr (fbs_x_hull_bound hgraph hcomp hrun halign hWL hbWL hoWL hWR hbWR hoWR
      hUL hbUL hoUL hUR hbUR hoUR ?_)
    intro p hp q hq
    obtain ⟨np, hprec, hbp, hop⟩ : ∃ np : ProperNode,
        run.coordinateProper.nodes[p]? = some np ∧
        (np.node.border = -1 ∨ np.node.border = 1) ∧
        np.node.clusterPath.getLast? = some wNode.decl := by
      rcases hp with rfl | rfl
      · exact ⟨nWL, hWL, Or.inl hbWL, hoWL⟩
      · exact ⟨nWR, hWR, Or.inr hbWR, hoWR⟩
    obtain ⟨nq, hqrec, hbq, hoq⟩ : ∃ nq : ProperNode,
        run.coordinateProper.nodes[q]? = some nq ∧
        (nq.node.border = -1 ∨ nq.node.border = 1) ∧
        nq.node.clusterPath.getLast? = some uNode.decl := by
      rcases hq with rfl | rfl
      · exact ⟨nUL, hUL, Or.inl hbUL, hoUL⟩
      · exact ⟨nUR, hUR, Or.inr hbUR, hoUR⟩
    have pin : p ∈ layer := by
      rcases hp with rfl | rfl
      · exact hmWLin
      · exact hmWRin
    have qin : q ∈ layer := by
      rcases hq with rfl | rfl
      · exact hmULin
      · exact hmURin
    obtain ⟨ip, hip⟩ := List.mem_iff_getElem?.mp pin
    obtain ⟨iq, hiq⟩ := List.mem_iff_getElem?.mp qin
    have hlt : ip < iq := hwFirst iq ip q p nq np hiq hip hqrec hprec hbq hoq hbp hop
    exact componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayerMem
      hlt hip hiq hprec hqrec
      (by intro hcon; rcases hcon with h | h <;> omega)
      (by intro hcon; rcases hcon with h | h <;> omega)
/-! ### The seam -/

set_option maxHeartbeats 3000000 in
/-- The group-vs-group foreign-span seam: from the rank-span residual (rank
assignment), the layer-order residual (cluster separation input), and the
border-chain alignment residual (cross-coordinate placement).  Disjoint member
rank ranges separate the member hulls vertically through the rank-axis band
facts; overlapping ranges give a shared marker rank, where the layer order and
the pairwise cluster separation separate the marker hulls horizontally. -/
theorem foreignBorderSpansSeparated
    (hspans : ForeignClusterRankSpans)
    (horder : ForeignBorderLayerOrder)
    (halign : ForeignBorderChainXAligned) :
    ForeignBorderSpansSeparated := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions hrun
    u w uNode wNode hu hw hgroupU hgroupW hne hpathW hpathU
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hry, -, -⟩ := componentRun_spec hrun
  obtain ⟨tU, bU, tW, bW, hUle, hWle, hUspan, hWspan, hUmark, hWmark⟩ :=
    hspans hgraph hcomp hrun hu hw hgroupU hgroupW hne
  obtain ⟨-, -, -, hmemU⟩ := fbs_group_node_member hgraph hcomp hrun hu hgroupU
  obtain ⟨-, -, -, hmemW⟩ := fbs_group_node_member hgraph hcomp hrun hw hgroupW
  have hneU : groupMemberRects (componentCandidate graph comp candidate) run
      uNode.decl ≠ [] := by
    intro he
    rw [he] at hmemU
    exact List.not_mem_nil hmemU
  have hneW : groupMemberRects (componentCandidate graph comp candidate) run
      wNode.decl ≠ [] := by
    intro he
    rw [he] at hmemW
    exact List.not_mem_nil hmemW
  by_cases hdisj : bU < tW
  · refine Or.inr (Or.inr (Or.inl ?_))
    refine fbs_member_hulls_y_separated hrun hry ?_ hneU hneW
    intro v hv hcv v' hv' hcv'
    have hu1 := hUspan v hv hcv
    have hw1 := hWspan v' hv' hcv'
    omega
  · have hov1 : tW ≤ bU := by
      by_cases h : tW ≤ bU
      · exact h
      · omega
    by_cases hdisj2 : bW < tU
    · refine Or.inr (Or.inr (Or.inr ?_))
      refine fbs_member_hulls_y_separated hrun hry ?_ hneW hneU
      intro v hv hcv v' hv' hcv'
      have hw1 := hWspan v hv hcv
      have hu1 := hUspan v' hv' hcv'
      omega
    · have hov2 : tU ≤ bW := by
        by_cases h : tU ≤ bW
        · exact h
        · omega
      by_cases hlt : tU ≤ tW
      · obtain ⟨mUL, mUR, nUL, nUR, hrecUL, hbUL, hoUL, hrkUL, hrecUR, hbUR, hoUR, hrkUR⟩ :=
          hUmark tW hlt hov1
        obtain ⟨mWL, mWR, nWL, nWR, hrecWL, hbWL, hoWL, hrkWL, hrecWR, hbWR, hoWR, hrkWR⟩ :=
          hWmark tW (Int.le_refl tW) hWle
        rcases fbs_border_hulls_x_separated hgraph hcomp hrun horder halign
          hu hw hgroupU hgroupW hpathW hpathU rfl rfl hne
          hrecUL hbUL hoUL hrkUL hrecUR hbUR hoUR hrkUR
          hrecWL hbWL hoWL hrkWL hrecWR hbWR hoWR hrkWR with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · obtain ⟨mUL, mUR, nUL, nUR, hrecUL, hbUL, hoUL, hrkUL, hrecUR, hbUR, hoUR, hrkUR⟩ :=
          hUmark tU (Int.le_refl tU) hUle
        obtain ⟨mWL, mWR, nWL, nWR, hrecWL, hbWL, hoWL, hrkWL, hrecWR, hbWR, hoWR, hrkWR⟩ :=
          hWmark tU (by omega) hov2
        rcases fbs_border_hulls_x_separated hgraph hcomp hrun horder halign
          hu hw hgroupU hgroupW hpathW hpathU rfl rfl hne
          hrecUL hbUL hoUL hrkUL hrecUR hbUR hoUR hrkUR
          hrecWL hbWL hoWL hrkWL hrecWR hbWR hoWR hrkWR with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)

end Elegant.Layered.PipelineImpl

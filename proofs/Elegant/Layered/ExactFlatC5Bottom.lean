import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.GroupBottomBoundaryProof
import Elegant.Layered.BottomClearanceExistence
import Elegant.Layered.ExecutedFrameClearanceFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact flat C5 bottom boundary (`X_BottomBoundary`).

Target (proved at the end of this file):
  `theorem x_bottomBoundary_holds (exactIds : List String) : X_BottomBoundary exactIds`
(the exact counterpart of `GroupBottomBoundaryFacts`, proved in
`GroupBottomBoundaryProof.lean`).

Route (mirrors `groupBottomBoundaryFacts_of_dummy` + `groupBottomBoundaryFacts_executed`
over the exact run):
  (1) exact rank transport (`Xb_prepared_rk`, `Xb_titled_rk`) from
      `X_cg_run_bundle` through `coordinateGraphX_anchor_prefix`;
  (2) exact member-rank bound (`Xb_origRankLe`, via the dummy bracket and the
      exact nested bound; ranks are identical in the exact run, so the bracket
      transports through `X_componentRun_ranked_source` and
      `X_proper_rank_eq_local`);
  (3) exact geometric assembly through `groupBottomBoundaryFacts_of_dummy`'s
      shape plus the reserve band lemma: `reserveExactRanks` shifts `ys` and
      `top` of one rank by the same amount, so in-band inclusion and band
      disjointness survive (`X_ReserveBands_holds`) and the proxy equality is
      preserved (`Xb_ys_eq`).
-/

/-- Bind split (copy of the private `X_bind_ok` of `ExactFlatC5Rank.lean`). -/
private theorem Xb_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
   cases x with
   | error e => simp [bind, Except.bind] at h
   | ok a => exact ⟨a, rfl, h⟩
 private theorem Xb_take_is_prefix {α : Type} (l : List α) (n : Nat) :
    l.take n <+: l :=
  ⟨l.drop n, by simp⟩

/-- A prefix is the take of its length. -/
private theorem Xb_prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
    s.take p.length = p := by
  obtain ⟨r, rfl⟩ := hp
  simp

/-- Of two prefixes of one list, the shorter is a prefix of the longer. -/
private theorem Xb_prefix_of_common_prefix {α : Type} {p q s : List α}
    (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
  obtain ⟨r₁, rfl⟩ := hp
  obtain ⟨r₂, hr⟩ := hq
  have h1 : (p ++ r₁).take p.length = p := Xb_prefix_take_eq ⟨r₁, rfl⟩
  have h2 : (q ++ r₂).take p.length = q.take p.length := by
    have hz : p.length - q.length = 0 := by omega
    simp [List.take_append, hz]
  rw [← hr] at h1
  rw [h2] at h1
  rw [← h1]
  exact Xb_take_is_prefix q p.length

/-- Mutual prefixes are equal. -/
private theorem Xb_prefix_antisymm {α : Type} {p q : List α}
    (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  have e : q.take p.length = p := Xb_prefix_take_eq h1
  have hle1 : p.length ≤ q.length := by
    obtain ⟨r, rfl⟩ := h1
    rw [List.length_append]
    exact Nat.le_add_right _ _
  have hle2 : q.length ≤ p.length := by
    obtain ⟨r, rfl⟩ := h2
    rw [List.length_append]
    exact Nat.le_add_right _ _
  have hlen : p.length = q.length := by omega
  have e2 : q.take q.length = q := by simp
  rw [← hlen] at e2
  exact e.symm.trans e2

/-- A strict prefix is strictly shorter. -/
private theorem Xb_prefix_length_lt {α : Type} {p s : List α}
    (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
  rcases Nat.lt_or_ge p.length s.length with h | h
  · exact h
  · have h2 : s <+: p :=
      Xb_prefix_of_common_prefix ⟨[], by simp⟩ hp h
    exact absurd (Xb_prefix_antisymm hp h2) hne

/-- Dropping the last element is a prefix. -/
private theorem Xb_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

/-- A cluster path ending in `d` has last element `d`. -/
private theorem Xb_cg_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp

/-- Exact prepared rank transport: executed exact coordinate ranks agree with
the ranking result on original indices (replay of `prepared_coordinate_original_rk`
through `coordinateGraphX_anchor_prefix`). -/
private theorem Xb_prepared_rk {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {rr : RankImpl.RankResult} {labeled : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      labeled.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk run.coordinateProper.rank index = rk rr.ranks index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hlabLookup := hranks index rr.ranks[index] hrrLookup
  have hlabLen : index < labeled.rank.length :=
    (List.getElem?_eq_some_iff.mp hlabLookup).1
  obtain ⟨_, _, heq⟩ := coordinateGraphX_anchor_prefix P exact labeled
  have hcoordLookup : run.coordinateProper.rank[index]? = some rr.ranks[index] := by
    rw [← hc, heq, List.getElem?_append_left hlabLen]
    exact hlabLookup
  simp only [rk, List.getD_eq_getElem?_getD, hcoordLookup, hrrLookup, Option.getD_some]

/-- Title-reservation rank prefix for exact sizing. -/
private theorem Xb_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ extra := by
  unfold titleReservations sizeProperPortsX
  exact ⟨_, rfl⟩

/-- Exact titled rank transport: executed exact title ranks agree with the
ranking result on original indices (replay of `prepared_titled_original_rk`). -/
private theorem Xb_titled_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {labeled : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      labeled.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact labeled)).rank index =
      rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact labeled)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hlabLookup := hranks index rr.ranks[index] hrrLookup
  obtain ⟨_, heq⟩ := Xb_titled_rank_prefix P exact labeled
  have htitledLookup : (titleReservations (sizeProperPortsX P exact labeled)).rank[index]? =
      some rr.ranks[index] := by
    rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hlabLookup).1]
    exact hlabLookup
  have heq2 : rk (titleReservations (sizeProperPortsX P exact labeled)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq2, ?_⟩
  rw [heq2]
  exact rankWithBudget_rk_nonneg hrr index

/-- Non-proxy exact coordinate nodes transfer to the proper run unchanged
(copy of the private `X_nonproxy_record` of `ExactFlatC2.lean`). -/
private theorem Xb_nonproxy {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- Exact coordinate record: every proper node has the same border and height
in the coordinate run, and the same cluster path when non-proxy
(copy of the private `X_fbs_coordinate_record` of `ExactFlatC2.lean`). -/
private theorem Xb_fbs {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp) :
    ∃ nvc : ProperNode, run.coordinateProper.nodes[v]? = some nvc ∧
      nvc.node.border = nvp.node.border ∧ nvc.node.h = nvp.node.h ∧
      (¬(nvc.node.border = -2 ∨ nvc.node.border = 2) →
        nvc.node.clusterPath = nvp.node.clusterPath) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
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
  obtain ⟨hfull, -⟩ := Xb_nonproxy hrun hcadr hnp
  have := Option.some.inj (hrec.symm.trans hfull)
  rw [← this]

/-- Exact bordered-graph node classification
(copy of the private `X_coordinateGraph0_lookup` of `ExactFlatC2.lean`). -/
private theorem Xb_coord0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := sizeProperPortsX_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

/-- Exact coordinate-graph node classification
(copy of the private `X_coordinateGraph_lookup` of `ExactFlatC2.lean`). -/
private theorem Xb_coord_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases Xb_coord0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3

/-- Exact proxy frames are flat: a `±2` node of `coordinateGraphX` has height 0
(copy of the private `X_pc_frame_flat` of `ExactFlatC2.lean`). -/
private theorem Xb_pc_frame_flat {P : Params} {exact : List Nat} {labeled : Proper}
    {v : Nat} {nd : ProperNode} (h : (coordinateGraphX P exact labeled).nodes[v]? = some nd)
    (hb : nd.node.border = -2 ∨ nd.node.border = 2) : nd.node.h = 0 := by
  rcases Xb_coord_lookup P exact labeled h with ⟨m, hm, _, _, _, hf⟩ | ⟨_, h1⟩ |
    ⟨i, q, hq, _, _, h1, _⟩
  · exact hf hb
  · omega
  · omega

 /-- Exact pre-reserve coordinates: unfold one `componentRunX` to expose the
 rank-axis output, the proxy `ys`, and the `reserveExactRanks` equation that
 produces the final `run.ys`/`run.top`
 (copy of the private `X_run_pre` of `ExactFlatC2.lean`). -/
 private theorem Xb_run_pre {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run) :
     ∃ (y_pre top_pre ys_pre : List Int),
       rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
         (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧
       proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧
       reserveExactRanks cg exact labels run.coordinateProper run.layers ys_pre top_pre =
         .ok (run.ys, run.top) ∧
       run.coordinateYs = y_pre := by
   unfold componentRunX at h
   obtain ⟨rr, _, h⟩ := Xb_bind_ok h
   obtain ⟨p0, hp0, h⟩ := Xb_bind_ok h
   obtain ⟨q, hq, h⟩ := Xb_bind_ok h
   obtain ⟨ord, hord, h⟩ := Xb_bind_ok h
   obtain ⟨xs, hxs, h⟩ := Xb_bind_ok h
   obtain ⟨routed, hprojection, h⟩ := Xb_bind_ok h
   obtain ⟨lanes, hr, h⟩ := Xb_bind_ok h
   obtain ⟨yt, hy, h⟩ := Xb_bind_ok h
   obtain ⟨⟨ysV, topV⟩, hres, h⟩ := Xb_bind_ok h
   obtain ⟨routes, hroutes, h⟩ := Xb_bind_ok h
   have he := Except.ok.inj h
   subst he
   cases yt with
   | mk y top =>
     exact ⟨y, top, _, hy, rfl, hres, rfl⟩

 /-- One `extra` step preserves length and nonnegativity
 (copy of the private `X_extra_step_preserves` of `ExactFlatC2.lean`). -/
 private theorem Xb_extra_step_preserves (acc : List Int) (m : Nat) (needed : Int)
     (hpos : ∀ i, 0 ≤ acc.getD i 0) :
     (acc.set m (max (acc.getD m 0) needed)).length = acc.length ∧
       ∀ i, 0 ≤ (acc.set m (max (acc.getD m 0) needed)).getD i 0 := by
   refine ⟨List.length_set, ?_⟩
   intro i
   have hset : (acc.set m (max (acc.getD m 0) needed))[i]? =
       if m = i then if m < acc.length then some (max (acc.getD m 0) needed) else none
       else acc[i]? :=
     List.getElem?_set
   rw [List.getD_eq_getElem?_getD, hset]
   by_cases heq : m = i
   · subst heq
     by_cases hlt : m < acc.length
     · have h0 : 0 ≤ acc[m] := by
         have h := hpos m
         simpa [hlt] using h
       simp [hlt]
       exact Int.le_trans h0 (Int.le_max_left _ _)
     · simp [hlt]
   · have hne : m ≠ i := heq
     simp [hne]
     exact hpos i

 /-- Generic fold preservation for length and nonnegativity
 (copy of the private `X_foldl_preserves` of `ExactFlatC2.lean`). -/
 private theorem Xb_foldl_preserves (step : List Int → Node × Nat → List Int)
     (topLen : Nat)
     (hstep : ∀ acc q, acc.length = topLen → (∀ i, 0 ≤ acc.getD i 0) →
       (step acc q).length = topLen ∧ ∀ i, 0 ≤ (step acc q).getD i 0)
     (xs : List (Node × Nat)) (acc : List Int)
     (hlen : acc.length = topLen) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
     (xs.foldl step acc).length = topLen ∧
       ∀ i, 0 ≤ (xs.foldl step acc).getD i 0 := by
   induction xs generalizing acc with
   | nil => exact ⟨hlen, hpos⟩
   | cons q xs ih =>
     simp only [List.foldl_cons]
     obtain ⟨hlen', hpos'⟩ := hstep acc q hlen hpos
     exact ih _ hlen' hpos'

 /-- The concrete `extra` step preserves length and nonnegativity (inlined `let`s)
 (copy of the private `X_extra_step_concrete` of `ExactFlatC2.lean`). -/
 private theorem Xb_extra_step_concrete (cg : Graph) (exact : List Nat)
     (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int)
     (acc : List Int) (q : Node × Nat)
     (hlen : acc.length = top.length) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
     (if !exact.contains q.1.decl then acc
       else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
       else acc.set ((p.rank.getD q.2 0).toNat)
         (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
           (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
             Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
             top.getD ((p.rank.getD q.2 0).toNat) 0 -
             heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
       ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
         else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
         else acc.set ((p.rank.getD q.2 0).toNat)
           (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
             (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
               Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
               top.getD ((p.rank.getD q.2 0).toNat) 0 -
               heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
   by_cases h1 : (!exact.contains q.1.decl) = true
   · rw [ite_eq_left h1]
     exact ⟨hlen, hpos⟩
   · rw [ite_eq_right h1]
     by_cases h2 : (loopSizes cg.edges labels q.2 cg.slot).isEmpty = true
     · rw [ite_eq_left h2]
       exact ⟨hlen, hpos⟩
     · rw [ite_eq_right h2]
       obtain ⟨hlen', hpos'⟩ := Xb_extra_step_preserves acc _ _ hpos
       exact ⟨hlen'.trans hlen, hpos'⟩

 /-- The `extra` fold preserves length and nonnegativity
 (copy of the private `X_extra_fold` of `ExactFlatC2.lean`). -/
 private theorem Xb_extra_fold (cg : Graph) (exact : List Nat)
     (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int) :
     let extra := cg.nodes.zipIdx.foldl (fun acc q =>
       if !exact.contains q.1.decl then acc
       else
         let sizes := loopSizes cg.edges labels q.2 cg.slot
         if sizes.isEmpty then acc
         else
           let rank := (p.rank.getD q.2 0).toNat
           let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
           let needed := ys.getD q.2 0 + reserved - top.getD rank 0 - heights.getD rank 0
           acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top.length (0 : Int))
     extra.length = top.length ∧ ∀ i, 0 ≤ extra.getD i 0 := by
   have hbase : (List.replicate top.length (0 : Int)).length = top.length := by simp
   have hbasePos : ∀ i, 0 ≤ (List.replicate top.length (0 : Int)).getD i 0 := by
     intro i
     by_cases h : i < top.length
     · have hg : (List.replicate top.length (0 : Int))[i]? = some 0 := by
         rw [List.getElem?_eq_getElem (by simpa using h)]
         simp
       rw [List.getD_eq_getElem?_getD, hg]
       simp
     · have hg : (List.replicate top.length (0 : Int))[i]? = none :=
         List.getElem?_eq_none_iff.mpr (by simpa using Nat.le_of_not_gt h)
       rw [List.getD_eq_getElem?_getD, hg]
       simp
   have hstep : ∀ (acc : List Int) (q : Node × Nat), acc.length = top.length →
     (∀ i, 0 ≤ acc.getD i 0) →
       (if !exact.contains q.1.decl then acc
         else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
         else acc.set ((p.rank.getD q.2 0).toNat)
           (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
             (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
               Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
               top.getD ((p.rank.getD q.2 0).toNat) 0 -
               heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
         ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
           else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
           else acc.set ((p.rank.getD q.2 0).toNat)
             (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
               (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
                 Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
                 top.getD ((p.rank.getD q.2 0).toNat) 0 -
                 heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
     intro acc q hlen hpos
     exact Xb_extra_step_concrete cg exact labels p ys top heights acc q hlen hpos
   have h := Xb_foldl_preserves (fun acc q =>
     if !exact.contains q.1.decl then acc
     else
       let sizes := loopSizes cg.edges labels q.2 cg.slot
       if sizes.isEmpty then acc
       else
         let rank := (p.rank.getD q.2 0).toNat
         let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
         let needed := ys.getD q.2 0 + reserved - top.getD rank 0 - heights.getD rank 0
         acc.set rank (max (acc.getD rank 0) needed)) top.length hstep
     cg.nodes.zipIdx (List.replicate top.length (0 : Int)) hbase hbasePos
   exact h

 /-- Prefix-sum elements stay nonnegative. -/
 private theorem Xb_shifts_nonneg_aux (es : List Int) (s : Int) (out : List Int)
     (hpos : ∀ e ∈ es, 0 ≤ e) (hs : 0 ≤ s) (hout : ∀ x ∈ out, 0 ≤ x) :
     ∀ x ∈ ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2), 0 ≤ x := by
   induction es generalizing s out with
   | nil => simpa using hout
   | cons e es ih =>
     have he : 0 ≤ e := hpos e List.mem_cons_self
     simp only [List.foldl_cons]
     apply ih
     · intro e' he'
       exact hpos e' (List.mem_cons_of_mem e he')
     · omega
     · intro x hx
       simp only [List.mem_append, List.mem_singleton] at hx
       rcases hx with hx | rfl
       · exact hout x hx
       · exact hs

 /-- The reserve prefix-sum shifts are nonnegative. -/
 private theorem Xb_shifts_nonneg (extra shifts : List Int)
     (hpos : ∀ e ∈ extra, 0 ≤ e)
     (hshifts : shifts =
       (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2) :
     ∀ i, 0 ≤ shifts.getD i 0 := by
   intro i
   subst hshifts
   by_cases hi : i < (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
       (0, ([] : List Int))).2.length
   · have hmem : ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
         (0, ([] : List Int))).2)[i]'hi ∈
         (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
           (0, ([] : List Int))).2 :=
       List.mem_of_getElem? (List.getElem?_eq_getElem hi)
     have h := Xb_shifts_nonneg_aux extra 0 [] hpos (Int.le_refl 0) (by simp) _ hmem
     rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
     simpa using h
   · have hg : ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
         (0, ([] : List Int))).2)[i]? = none :=
       List.getElem?_eq_none_iff.mpr (by omega)
     rw [List.getD_eq_getElem?_getD, hg]
     simp
 /-- Chain rank contiguity through normalize (copy of the private
 `normalize_chain_rank_positions` of `ExecutedFrameClearanceFacts.lean`). -/
 private theorem Xb_normalize_chain_positions {graph : Graph} {ranks : List Int}
     {normalized : Proper} (hnormalize : normalize graph ranks = .ok normalized)
     {index : Nat} {edge : Edge} {chain : List Nat}
     (hedge : graph.edges[index]? = some edge)
     (hchain : normalized.chains[index]? = some chain) :
     ∀ position (hposition : position < chain.length),
       rk normalized.rank (chain[position]'hposition) =
         rk normalized.rank edge.tail + (position : Int) := by
   have hindex := (List.getElem?_eq_some_iff.mp hedge).1
   have hfact := (normalize_ok hnormalize).2.2 index hindex edge hedge
   by_cases hself : edge.tail = edge.head
   · have hempty : chain = [] := by
       have h := hfact.2
       simp only [hself, ↓reduceIte] at h
       exact Option.some.inj (hchain.symm.trans h)
     intro position hposition
     simp only [hempty, List.length_nil] at hposition
     omega
   · obtain ⟨actual, hactual, _, hhead, hlast, hadjacent⟩ :
         ∃ actual, normalized.chains[index]? = some actual ∧
           2 ≤ actual.length ∧ actual.head? = some edge.tail ∧
           actual.getLast? = some edge.head ∧
           ∀ (j : Nat) (hj : j < actual.length) (hj1 : j + 1 < actual.length),
             ∃ pe ∈ normalized.edges, pe.original = index ∧ pe.decl = edge.decl ∧
               pe.tail = actual[j] ∧ pe.head = actual[j + 1] := by
       simpa only [hself, ↓reduceIte] using hfact.2
     have hactualEq : chain = actual := Option.some.inj (hchain.symm.trans hactual)
     subst actual
     intro position
     induction position with
     | zero =>
       intro hposition
       have hzero : chain[0]? = some edge.tail := by
         rw [← List.head?_eq_getElem?]
         exact hhead
       have hfirst : chain[0]'hposition = edge.tail :=
         Option.some.inj ((List.getElem?_eq_getElem hposition).symm.trans hzero)
       rw [hfirst]
       change rk normalized.rank edge.tail = rk normalized.rank edge.tail + (0 : Int)
       omega
     | succ position ih =>
       intro hposition
       have hprevious : position < chain.length := by omega
       obtain ⟨pe, hpe, _, _, htail, hnext⟩ := hadjacent position hprevious hposition
       have hstep := normalize_proper graph ranks normalized hnormalize pe hpe
       unfold Proper.span at hstep
       rw [htail, hnext] at hstep
       have hprefix := ih hprevious
       omega

 /-- Exact labeled chain rank positions (replay of
 `componentRun_labeled_chain_rank_positions` through `X_componentRun_ranked_source`). -/
 private theorem Xb_labeled_chain_positions
     {P : Params} {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
     ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
       rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
       normalize cg rr.ranks = .ok normalized ∧
       Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
       coordinateGraphX P exact labeled = run.coordinateProper ∧
       ∀ (index : Nat) (edge : Edge) (chain : List Nat),
         cg.edges[index]? = some edge → labeled.chains[index]? = some chain →
         ∀ position (hposition : position < chain.length),
           rk labeled.rank (chain[position]'hposition) =
             rk labeled.rank edge.tail + (position : Int) := by
   obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, _⟩ :=
     X_componentRun_ranked_source hrun
   refine ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, ?_⟩
   intro index edge chain hedge hchain position hposition
   have metadata := Labels.addLabelNodes_metadata hlabels
   rw [metadata.2.2.1] at hchain
   rw [metadata.2.1]
   exact Xb_normalize_chain_positions hnormalize hedge hchain position hposition

 /-- Labeled ranks stay aligned through exact normalize and label nodes
 (copy of the private `labeled_rank_aligned` of `DummyChainRankProof.lean`). -/
 private theorem Xb_labeled_rank_aligned {cg : Graph}
     {rr : RankImpl.RankResult} {normalized labeled : Proper}
     {labels : List MeasuredLabel}
     (hnormalize : normalize cg rr.ranks = .ok normalized)
     (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled) :
     labeled.nodes.length = labeled.rank.length := by
   have h1 := addLabelNodes_node_length hlabels
   have h2 := congrArg List.length (Labels.addLabelNodes_metadata hlabels).2.1
   have h3 := (normalize_node_rank_alignment hnormalize).1
   omega

 /-- Exact coordinate ranks agree with labeled ranks index-wise
 (copy of the private `coord_rank_eq` of `DummyChainRankProof.lean`). -/
 private theorem Xb_coord_rank_eq {P : Params} {exact : List Nat} {labeled : Proper} {run : Run}
     (hcoord : coordinateGraphX P exact labeled = run.coordinateProper)
     (haligned : labeled.nodes.length = labeled.rank.length)
     {x : Nat} (hx : x < labeled.nodes.length) :
     rk run.coordinateProper.rank x = rk labeled.rank x := by
   have hxr : x < labeled.rank.length := by omega
   have hlab : labeled.rank[x]? = some (labeled.rank[x]'hxr) :=
     List.getElem?_eq_getElem hxr
   obtain ⟨_, _, heq⟩ := coordinateGraphX_anchor_prefix P exact labeled
   have hcoo : run.coordinateProper.rank[x]? = some (labeled.rank[x]'hxr) := by
     rw [← hcoord, heq, List.getElem?_append_left hxr]
     exact hlab
   simp only [rk, List.getD_eq_getElem?_getD, hlab, hcoo, Option.getD_some]

 /-- Exact dummy border collapse: a dummy node of `coordinateGraphX` has border 0
 (copy of `pc_plain` in `CoordGraph.lean`). -/
 private theorem Xb_pc_plain {cg : Graph} {P : Params} {exact : List Nat} {labeled : Proper}
     (hK : NodeKeys cg labeled)
     {v : Nat} {nd : ProperNode} (h : (coordinateGraphX P exact labeled).nodes[v]? = some nd)
     (hd : nd.dummy = true) : nd.node.border = 0 := by
   rcases Xb_coord_lookup P exact labeled h with ⟨m, hm, h1, h2, _, _⟩ | ⟨h1, _⟩ |
     ⟨i, q, hq, _, h1, h2, _⟩
   · rcases hK v m hm with ⟨n, _, hmd, _, _⟩ | ⟨_, hb, _⟩
     · rw [h1] at hd; rw [hmd] at hd; exact absurd hd (by decide)
     · rw [h2, hb]
   · rw [h1] at hd; exact absurd hd (by decide)
   · obtain ⟨hs, hb⟩ := titleNodes_spec hq
     have hk := sizeProperPortsX_key P exact labeled q.2
     rw [hs] at hk
     cases hp : labeled.nodes[q.2]? with
     | none => simp [hp] at hk
     | some mp =>
       simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
       obtain ⟨hk1, hk2, _⟩ := hk
       rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
       · rw [h1, hk1, hmd] at hd; exact absurd hd (by decide)
       · rw [hk2] at hb
         rw [hb'] at hb
         exact absurd hb (by decide)

 /-- An executed exact proper dummy has the same record in the coordinate graph
 (copy of the private `proper_to_coordinate_dummy` of `DummyChainRankProof.lean`). -/
 private theorem Xb_proper_to_coord_dummy {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run)
     {i : Nat} {pn : ProperNode}
     (hp : run.proper.nodes[i]? = some pn) (hd : pn.dummy = true) :
     ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = true ∧
       cn.node.border = pn.node.border ∧ cn.node.clusterPath = pn.node.clusterPath := by
   obtain ⟨_, _, labeled, q0, hn, hl, hc, _, _, hproxy, hdrop, _, _, _⟩ :=
     componentRunX_spec hrun
   have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
   have hq0i : q0.nodes[i]? = some pn := by rw [← hnodes]; exact hp
   have hlen : q0.nodes.length = run.coordinateProper.nodes.length :=
     (proxyWidths_rel hproxy).2.2.1
   have hiC : i < run.coordinateProper.nodes.length := by
     have hi0 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0i).1
     omega
   obtain ⟨cn, hcn⟩ : ∃ cn, run.coordinateProper.nodes[i]? = some cn :=
     ⟨_, List.getElem?_eq_getElem hiC⟩
   obtain ⟨nd', hnd', hddum, _, _⟩ :=
     (proxyWidths_rel hproxy).2.2.2.2.1 i cn hcn
   have hndEq : nd' = pn := Option.some.inj (hnd'.symm.trans hq0i)
   have hcnDum : cn.dummy = true := by rw [← hddum, hndEq]; exact hd
   have hK : NodeKeys cg labeled :=
     addLabelNodes_keys _ _ _ (normalize_keys hn) hl
   have hcnL : (coordinateGraphX P exact labeled).nodes[i]? = some cn := by
     rw [hc]; exact hcn
   have hbord0 : cn.node.border = 0 := Xb_pc_plain hK hcnL hcnDum
   have hnp : ¬ (cn.node.border = -2 ∨ cn.node.border = 2) := by
     rw [hbord0]; decide
   obtain ⟨hsame, -⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 i cn hcn hnp
   have hcnEq : cn = pn := Option.some.inj (hsame.symm.trans hq0i)
   exact ⟨cn, hcn, hcnDum, by rw [hcnEq], by rw [hcnEq]⟩

 /-- Exact prepared nodes keep their labeled cluster path
 (copy of the private `prepared_path_eq` of `DummyChainRankProof.lean`). -/
 private theorem Xb_prepared_path_eq {P : Params} {exact : List Nat} {labeled : Proper}
     {j : Nat} {pn : ProperNode}
     (hlab : labeled.nodes[j]? = some pn) :
     ∃ qn, (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes[j]? =
       some qn ∧ qn.node.clusterPath = pn.node.clusterPath := by
   have hj : j < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hlab).1
   have hlen1 : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length :=
     sizeProperPortsX_length P exact labeled
   have hs1 := sizeProperPortsX_key P exact labeled j
   rw [hlab] at hs1
   obtain ⟨m1, hm1, htrip⟩ : ∃ m1, (sizeProperPortsX P exact labeled).nodes[j]? = some m1 ∧
       (m1.dummy, m1.node.border, m1.node.clusterPath) =
         (pn.dummy, pn.node.border, pn.node.clusterPath) := by
     cases hs : (sizeProperPortsX P exact labeled).nodes[j]? with
     | none => simp [hs] at hs1
     | some m1 =>
       simp only [hs, Option.map_some, Option.some.injEq] at hs1
       exact ⟨m1, rfl, hs1⟩
   have hp1 : m1.node.clusterPath = pn.node.clusterPath := by
     have h3 := congrArg (fun t : Bool × Int × List Nat => t.2.2) htrip
     simpa using h3
   have hm2 : (titleReservations (sizeProperPortsX P exact labeled)).nodes[j]? =
       some (titleF m1) := by
     have hJ : j < ((sizeProperPortsX P exact labeled).nodes.map titleF).length := by
       rw [List.length_map, hlen1]; exact hj
     rw [titleReservations_nodes, List.getElem?_append_left hJ, List.getElem?_map, hm1,
       Option.map_some]
   have hp2 : (titleF m1).node.clusterPath = pn.node.clusterPath := by
     rw [(titleF_keys m1).2.2.1]; exact hp1
   have hlen2 : (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
       (sizeProperPortsX P exact labeled).nodes.length +
         ((titleNodes (sizeProperPortsX P exact labeled)).map copyF).length := by
     rw [titleReservations_nodes, List.length_append, List.length_map, List.length_map]
   have hj2 : j < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
     omega
   obtain ⟨extra, hx, _⟩ :=
     addClusterBorders_extra (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
   have hm3 : (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[j]? =
       (titleReservations (sizeProperPortsX P exact labeled)).nodes[j]? := by
     rw [hx]; exact List.getElem?_append_left hj2
   have hm4 : (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes[j]? =
       some (clearF (titleF m1)) := by
     rw [clearProxyExtents_nodes, List.getElem?_map, hm3, hm2, Option.map_some]
   have hp4 : (clearF (titleF m1)).node.clusterPath = pn.node.clusterPath := by
     rw [(clearF_keys (titleF m1)).2.2.1]; exact hp2
   exact ⟨_, hm4, hp4⟩
 /-- Exact executed dummy chain source (replay of
 `componentRun_dummy_path_chain_source` through `Xb_labeled_chain_positions`). -/
 private theorem Xb_dummy_path_chain_source
     {P : Params} {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run)
     {v owner : Nat} {node : ProperNode}
     (hv : run.coordinateProper.nodes[v]? = some node)
     (hdummy : node.dummy = true) (howner : owner ∈ node.node.clusterPath) :
     ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper)
       (index : Nat) (edge : Edge) (chain : List Nat) (position : Nat),
       rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
       normalize cg rr.ranks = .ok normalized ∧
       Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
       coordinateGraphX P exact labeled = run.coordinateProper ∧
       cg.edges[index]? = some edge ∧ labeled.chains[index]? = some chain ∧
       chain[position]? = some v ∧ chain.head? = some edge.tail ∧
       chain.getLast? = some edge.head ∧
       rk labeled.rank v = rk labeled.rank edge.tail + (position : Int) ∧
       let prepared := clearProxyExtents (OrderImpl.addClusterBorders
         (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)
       prepared.chains.find? (fun members => members.contains v) = some chain ∧
       owner ∈ (prepared.nodes.getD (chain.headD v) default).node.clusterPath ∧
       owner ∈ (prepared.nodes.getD (chain.getLastD v) default).node.clusterPath := by
   obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, hpositions⟩ :=
     Xb_labeled_chain_positions hrun
   let prepared := clearProxyExtents (OrderImpl.addClusterBorders
     (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)
   have hmaterialized : (materializeDummyPaths prepared).nodes[v]? = some node := by
     rw [← hcoordinate] at hv
     exact hv
   obtain ⟨before, hbefore, hd, _, _, _⟩ := materialize_lookup prepared hmaterialized
   have hbeforeDummy : before.dummy = true := hd.symm.trans hdummy
   have hpath : node.node.clusterPath = OrderImpl.nodePath prepared v := by
     simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
       hbefore, Option.map_some, hbeforeDummy, ↓reduceIte, Option.some.injEq] at hmaterialized
     rw [← hmaterialized]
     simp only [Nat.zero_add]
   have hselected : node.node.clusterPath =
       match prepared.chains.find? (fun members => members.contains v) with
       | none => []
       | some chain => OrderImpl.commonPath
           ((prepared.nodes.getD (chain.headD v) default).node.clusterPath)
           ((prepared.nodes.getD (chain.getLastD v) default).node.clusterPath) := by
     rw [hpath]
     simp [OrderImpl.nodePath, List.getD_eq_getElem?_getD, hbefore, hbeforeDummy]
     rfl
   cases hfind : prepared.chains.find? (fun members => members.contains v) with
   | none =>
     simp only [hfind] at hselected
     rw [hselected] at howner
     exact False.elim (List.not_mem_nil howner)
   | some chain =>
     have hchains : prepared.chains = labeled.chains := by
       exact (OrderImpl.addClusterBorders_metadata
         (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW).2.1
     have hchainMember : chain ∈ prepared.chains := List.mem_of_find?_eq_some hfind
     rw [hchains] at hchainMember
     obtain ⟨index, hchain⟩ := List.mem_iff_getElem?.mp hchainMember
     have hnormalizedChain : normalized.chains[index]? = some chain := by
       rw [← (Labels.addLabelNodes_metadata hlabels).2.2.1]
       exact hchain
     have hindex : index < cg.edges.length := by
       have hbound := (List.getElem?_eq_some_iff.mp hnormalizedChain).1
       rw [normalize_chains_length hnormalize] at hbound
       exact hbound
     have hedge : cg.edges[index]? = some (cg.edges[index]'hindex) :=
       List.getElem?_eq_getElem hindex
     have hmember : v ∈ chain := by
       simpa only [List.contains_iff_mem] using List.find?_some hfind
     obtain ⟨position, hposition⟩ := List.mem_iff_getElem?.mp hmember
     have hpositionBound := (List.getElem?_eq_some_iff.mp hposition).1
     have hpositionValue : chain[position]'hpositionBound = v :=
       Option.some.inj ((List.getElem?_eq_getElem hpositionBound).symm.trans hposition)
     have hfact := (normalize_ok hnormalize).2.2 index hindex _ hedge
     by_cases hself : (cg.edges[index]'hindex).tail = (cg.edges[index]'hindex).head
     · have hempty : chain = [] := by
         have h := hfact.2
         simp only [hself, ↓reduceIte] at h
         exact Option.some.inj (hnormalizedChain.symm.trans h)
       rw [hempty] at hmember
       exact False.elim (List.not_mem_nil hmember)
     · obtain ⟨actual, hactual, _, hhead, hlast, _⟩ := by
         simpa only [hself, ↓reduceIte] using hfact.2
       have hactualEq : chain = actual :=
         Option.some.inj (hnormalizedChain.symm.trans hactual)
       subst actual
       have hrank := hpositions index _ chain hedge hchain position hpositionBound
       rw [hpositionValue] at hrank
       have hownerCommon := howner
       rw [hselected, hfind] at hownerCommon
       obtain ⟨hleftOwner, hrightOwner⟩ := commonPath_member_both _ _ hownerCommon
       exact ⟨rr, normalized, labeled, index, _, chain, position, hrr, hnormalize,
         hlabels, hcoordinate, hedge, hchain, hposition, hhead, hlast, hrank,
         hfind, hleftOwner, hrightOwner⟩

 /-- Every executed exact proper dummy lies on its original edge's chain between its
 endpoint ranks, and both endpoint candidate paths carry the dummy's owner
 (copy of `dummy_chain_bracket` for `componentRunX`). -/
 private theorem Xb_bracket {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run)
     {i : Nat} (hi : i < run.proper.nodes.length)
     (hdummy : (run.proper.nodes.getD i default).dummy = true)
     {owner : Nat} (howner : owner ∈ (run.proper.nodes.getD i default).node.clusterPath) :
     ∃ (index : Nat) (edge : Edge),
       cg.edges[index]? = some edge ∧
       edge.tail ≠ edge.head ∧
       edge.tail < cg.nodes.length ∧ edge.head < cg.nodes.length ∧
       rk run.coordinateProper.rank edge.tail ≤ rk run.coordinateProper.rank i ∧
       rk run.coordinateProper.rank i ≤ rk run.coordinateProper.rank edge.head ∧
       ∃ (nA nB : Node),
         cg.nodes[edge.tail]? = some nA ∧ cg.nodes[edge.head]? = some nB ∧
         nA.clusterPath.contains owner = true ∧ nB.clusterPath.contains owner = true := by
   have hp : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
     simp [List.getD_eq_getElem?_getD, hi]
   obtain ⟨cn, hcn, hcnDum, _, hcnPath⟩ := Xb_proper_to_coord_dummy hrun hp hdummy
   have hownerC : owner ∈ cn.node.clusterPath := by rw [hcnPath]; exact howner
   obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordRun, hpositions⟩ :=
     Xb_labeled_chain_positions hrun
   obtain ⟨rrC, normC, labC, index, edge, chain, position,
       hrrC, hnormC, hlabC, hcoordC, hedge, hchainC, hpos, hhead, hlast, hrankC,
       _hfind, hleftC, hrightC⟩ :=
     Xb_dummy_path_chain_source hrun hcn hcnDum hownerC
   have e1 : rr = rrC := Except.ok.inj (hrr.symm.trans hrrC)
   subst e1
   have e2 : normalized = normC := Except.ok.inj (hnormalize.symm.trans hnormC)
   subst e2
   have e3 : labeled = labC := Except.ok.inj (hlabels.symm.trans hlabC)
   subst e3
   have hindex : index < cg.edges.length := (List.getElem?_eq_some_iff.mp hedge).1
   have hwf : cg.wellformed = true := (normalize_node_rank_alignment hnormalize).2
   have hedgeMem : edge ∈ cg.edges := List.mem_of_getElem? hedge
   obtain ⟨htailLt, hheadLt, _⟩ := RankImpl.wellformed_spec hwf edge hedgeMem
   have hchainsEq : labeled.chains = normalized.chains :=
     (Labels.addLabelNodes_metadata hlabels).2.2.1
   have hfact := (normalize_ok hnormalize).2.2 index hindex edge hedge
   have hne : edge.tail ≠ edge.head := by
     intro heq
     have hif := hfact.2
     simp only [heq, ↓reduceIte] at hif
     rw [← hchainsEq] at hif
     have hempty : chain = [] := Option.some.inj (hchainC.symm.trans hif)
     rw [hempty] at hpos
     simp at hpos
   have hlastElem : chain[chain.length - 1]? = some edge.head := by
     rw [← List.getLast?_eq_getElem?]; exact hlast
   have hlastLt : chain.length - 1 < chain.length :=
     (List.getElem?_eq_some_iff.mp hlastElem).1
   have hposLen : position < chain.length := (List.getElem?_eq_some_iff.mp hpos).1
   have hlastEq : chain[chain.length - 1]'hlastLt = edge.head :=
     Option.some.inj ((List.getElem?_eq_getElem hlastLt).symm.trans hlastElem)
   have hlastRank := hpositions index edge chain hedge hchainC (chain.length - 1) hlastLt
   rw [hlastEq] at hlastRank
   have hlabLe1 : rk labeled.rank edge.tail ≤ rk labeled.rank i := by omega
   have hlabLe2 : rk labeled.rank i ≤ rk labeled.rank edge.head := by omega
   have hlenN := normalize_nodes_length_le hnormalize
   have hlenL : normalized.nodes.length = labeled.nodes.length :=
     addLabelNodes_node_length hlabels
   have htailL : edge.tail < labeled.nodes.length := by omega
   have hheadL : edge.head < labeled.nodes.length := by omega
   have haligned := Xb_labeled_rank_aligned hnormalize hlabels
   have hK : NodeKeys cg labeled :=
     addLabelNodes_keys _ _ _ (normalize_keys hnormalize) hlabels
   have hcnL : (coordinateGraphX P exact labeled).nodes[i]? = some cn := by
     rw [hcoordRun]; exact hcn
   have hiL : i < labeled.nodes.length := by
     rcases Xb_coord_lookup P exact labeled hcnL with
       ⟨m, hm, _, _, _, _⟩ | ⟨hdF, _⟩ | ⟨_, tq, htq, _, hdT, _, _⟩
     · exact (List.getElem?_eq_some_iff.mp hm).1
     · rw [hcnDum] at hdF; exact absurd hdF (by decide)
     · obtain ⟨hs, hbq⟩ := titleNodes_spec htq
       have hk := sizeProperPortsX_key P exact labeled tq.2
       rw [hs] at hk
       cases hp2 : labeled.nodes[tq.2]? with
       | none => simp [hp2] at hk
       | some mp =>
         simp only [hp2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
         obtain ⟨hk1, hk2, _⟩ := hk
         rcases hK tq.2 mp hp2 with ⟨_, _, hmd, _, _⟩ | ⟨_, hbB, _⟩
         · rw [hdT, hk1, hmd] at hcnDum; exact absurd hcnDum (by decide)
         · rw [hk2] at hbq; rw [hbB] at hbq; exact absurd hbq (by decide)
   have hcTail : rk run.coordinateProper.rank edge.tail = rk labeled.rank edge.tail :=
     Xb_coord_rank_eq hcoordRun haligned htailL
   have hcHead : rk run.coordinateProper.rank edge.head = rk labeled.rank edge.head :=
     Xb_coord_rank_eq hcoordRun haligned hheadL
   have hcI : rk run.coordinateProper.rank i = rk labeled.rank i :=
     Xb_coord_rank_eq hcoordRun haligned hiL
   have hleC1 : rk run.coordinateProper.rank edge.tail ≤ rk run.coordinateProper.rank i := by
     omega
   have hleC2 : rk run.coordinateProper.rank i ≤ rk run.coordinateProper.rank edge.head := by
     omega
   obtain ⟨nA, hnA⟩ : ∃ n, cg.nodes[edge.tail]? = some n :=
     ⟨_, List.getElem?_eq_getElem htailLt⟩
   obtain ⟨nB, hnB⟩ : ∃ n, cg.nodes[edge.head]? = some n :=
     ⟨_, List.getElem?_eq_getElem hheadLt⟩
   have hlabT : labeled.nodes[edge.tail]? = some ⟨nA, false, none, false⟩ := by
     have hn0 := normalize_node_record hnormalize hnA
     exact addLabelNodes_untouched_node hlabels hn0 rfl
   have hlabH : labeled.nodes[edge.head]? = some ⟨nB, false, none, false⟩ := by
     have hn0 := normalize_node_record hnormalize hnB
     exact addLabelNodes_untouched_node hlabels hn0 rfl
   obtain ⟨qT, hqT, hpT⟩ := Xb_prepared_path_eq hlabT
   obtain ⟨qH, hqH, hpH⟩ := Xb_prepared_path_eq hlabH
   have hheadD : chain.headD i = edge.tail := by
     cases hcchain : chain with
     | nil => simp [hcchain] at hhead
     | cons a as =>
       simp only [List.headD]
       simpa [hcchain] using hhead
   have hlastD : chain.getLastD i = edge.head := by
     rw [List.getLastD_eq_getLast?, hlast, Option.getD_some]
   have hgetDT : (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes.getD
       edge.tail default = qT := by
     rw [List.getD_eq_getElem?_getD, hqT, Option.getD_some]
   have hgetDH : (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes.getD
       edge.head default = qH := by
     rw [List.getD_eq_getElem?_getD, hqH, Option.getD_some]
   rw [hheadD, hgetDT] at hleftC
   rw [hlastD, hgetDH] at hrightC
   have hcontA : nA.clusterPath.contains owner = true := by
     rw [hpT] at hleftC
     exact List.contains_iff_mem.mpr hleftC
   have hcontB : nB.clusterPath.contains owner = true := by
     rw [hpH] at hrightC
     exact List.contains_iff_mem.mpr hrightC
   exact ⟨index, edge, hedge, hne, htailLt, hheadLt, hleC1, hleC2,
     nA, nB, hnA, hnB, hcontA, hcontB⟩


 /-- Exact connectivity bridge: a constraint edge keeps its head in the component
 (copy of the private `X_pushIntoComp` of `ExactFlatC5Rank.lean`). -/
 private theorem Xb_pushIntoComp {graph : Graph} {comp : List Nat}
     (hbd : ∀ e ∈ graph.edges ++ Compound.constraints graph,
       e.tail < graph.nodes.length ∧ e.head < graph.nodes.length)
     (hcompMem : comp ∈ components graph)
     {e : Edge} (he : e ∈ graph.edges ++ Compound.constraints graph)
     (hta : e.tail ∈ comp) : e.head ∈ comp := by
   obtain ⟨c, hcMem, hca, hcb⟩ := components_edge_endpoints hbd he
   have heq : c = comp := components_shared_member_eq hcMem hcompMem hca hta
   rw [heq] at hcb
   exact hcb

 /-- Find from membership (copy of the private `findSomeOfMember` of
 `BottomClearanceExistence.lean`). -/
 private theorem Xb_findSomeOfMember {l : List (Node × Nat)} {pred : Node × Nat → Bool}
     {entry : Node × Nat} (hmem : entry ∈ l) (hp : pred entry = true) :
     ∃ b : Node × Nat, l.find? pred = some b :=
   Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, hmem, hp⟩)

 /-- Inverting a fixed-boxes lookup (copy of the private `demote_lookup` of
 `BottomClearanceExistence.lean`). -/
 private theorem Xb_demote_lookup {inp : Input} {i : Nat} {b : ModelBox}
     (h : (inp.boxes.map fun box =>
         if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
           { box with role := .node } else box)[i]? = some b) :
     ∃ orig : ModelBox, inp.boxes[i]? = some orig ∧ b.id = orig.id ∧ b.parent = orig.parent ∧
       (b.role = .group →
         ¬(inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == orig.id) = true)) ∧
       b = (if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == orig.id) then
             { orig with role := .node } else orig) := by
   rw [List.getElem?_map] at h
   cases hop : inp.boxes[i]? with
   | none => rw [hop] at h; simp at h
   | some orig =>
     rw [hop, Option.map_some, Option.some.injEq] at h
     by_cases hfixed : inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == orig.id)
     · have hd : b = ({ orig with role := .node } : ModelBox) :=
         h.symm.trans (ite_eq_left hfixed)
       refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_,
         by rw [hd, ite_eq_left hfixed]⟩
       intro hrole
       rw [hd] at hrole
       simp at hrole
     · have hd : b = orig :=
         h.symm.trans (ite_eq_right (by simp [hfixed]))
       refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_,
         by rw [hd, ite_eq_right hfixed]⟩
       intro _
       exact hfixed

 /-- Fixed-boxes mapping preserves ids (copy of the private `demote_id` of
 `BottomClearanceExistence.lean`). -/
 private theorem Xb_demote_id {inp : Input} :
     ∀ b ∈ inp.boxes, ((fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box) b).id = b.id := by
   intro b _
   dsimp only
   split <;> rfl

 /-- Fixed-boxes mapping preserves parents (copy of the private `demote_parent` of
 `BottomClearanceExistence.lean`). -/
 private theorem Xb_demote_parent {inp : Input} :
     ∀ b ∈ inp.boxes, ((fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box) b).parent = b.parent := by
   intro b _
   dsimp only
   split <;> rfl

 /-- Exact-to-measured node key transport (copy of the private
 `X_exactGraph_node_key_rev` of `ExactFlatC5Rank.lean`). -/
 private theorem Xb_exactGraph_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
     {o : Options} {measured : List MeasuredLabel} {g g' : Graph}
     (h : exactGraph P exactIds inp o measured g = .ok g')
     {v : Nat} {nd' : Node} (hv : g'.nodes[v]? = some nd') :
     ∃ nd, g.nodes[v]? = some nd ∧ nd'.border = nd.border ∧
       nd'.clusterPath = nd.clusterPath ∧ nd'.decl = nd.decl := by
   have hlen : g'.nodes.length = g.nodes.length := exactGraph_length h
   have hvlt : v < g.nodes.length := by
     have hlt := (List.getElem?_eq_some_iff.mp hv).1
     omega
   have hmem : g.nodes[v]? = some g.nodes[v] := List.getElem?_eq_getElem hvlt
   obtain ⟨nd'', hnd'', hb, hc, hd⟩ := exactGraph_node_key h hmem
   have heq : nd'' = nd' := Option.some.inj (hnd''.symm.trans hv)
   subst heq
   exact ⟨g.nodes[v], hmem, hb, hc, hd⟩

 /-- Exact candidate parent top existence: replay of `candidate_parent_top_exists`
 through `X_exactGraph_node_key_rev` and `X_groupTopFind?_some`. -/
 private theorem Xb_parent_top_exists {P : Params} {inp : Input} {o : Options}
     {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hframed : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
     {x : Node × Nat} (hxMem : x ∈ (componentCandidate graph comp candidate).nodes.zipIdx)
     (hxGroup : x.1.border = -2) {outerPrefix : List Nat}
     (_hpre : outerPrefix <+: x.1.clusterPath)
     (hlen : outerPrefix.length < x.1.clusterPath.length) (hne : outerPrefix ≠ []) :
     ∃ parent : Node × Nat,
       (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
         entry.1.border == -2 && entry.1.clusterPath == x.1.clusterPath.dropLast) =
           some parent := by
   have hbd := X_exactConstraintsBounded h0 h hlines
   have hzipLookup : (componentCandidate graph comp candidate).nodes[x.2]? = some x.1 :=
     List.mem_zipIdx_iff_getElem?.mp hxMem
   obtain ⟨oIdx, ho, hsource⟩ := componentCandidate_nonplain_source hzipLookup (by omega)
   have hoIn : oIdx ∈ comp := List.mem_of_getElem? ho
   obtain ⟨nd0, hnd0, hbord0, hpath0, hdecl0⟩ := Xb_exactGraph_node_key_rev h hsource
   have hxGroup0 : nd0.border = -2 := by rw [← hbord0]; exact hxGroup
   obtain ⟨_, box_x, hboxx, hrolex, hxpath0⟩ :=
     measuredGraph_group_origin h0 hnd0 hxGroup0
   have hxpath : x.1.clusterPath = Compound.path (inp.boxes.map fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box) box_x ++ [x.1.decl] := by
     rw [hpath0, hdecl0]; exact hxpath0
   obtain ⟨orig_x, horigLookup, hidx, hparentOf, hnotfixed, hdemoteX⟩ :=
     Xb_demote_lookup hboxx
   have hpathXNe : Compound.path (inp.boxes.map fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box) box_x ≠ [] := by
     intro hnil
     have hclen : x.1.clusterPath.length = 1 := by rw [hxpath, hnil]; simp
     have hoplen : outerPrefix.length = 0 := by omega
     have hopnil : outerPrefix = [] := List.length_eq_zero_iff.mp hoplen
     exact hne hopnil
   have hdrop : x.1.clusterPath.dropLast = Compound.path (inp.boxes.map fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box) box_x := by
     rw [hxpath, List.dropLast_append_of_ne_nil (l := [x.1.decl]) (by simp)]
     simp
   have hnf : ¬(inp.fixedSizes.any (fun fixed : String × Size =>
       fixed.1 == orig_x.id) = true) := hnotfixed hrolex
   have hbxOrig : box_x = orig_x := by rw [hdemoteX, ite_eq_right hnf]
   rw [hbxOrig] at hdrop hpathXNe
   have hpxne : orig_x.parent ≠ "" := by
     intro hempty
     refine hpathXNe ?_
     unfold Compound.path
     rw [hempty]
     cases hlen : (inp.boxes.map fun box =>
         if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
           { box with role := .node } else box).length with
     | zero => simp [Compound.ancestors]
     | succ n => simp [Compound.ancestors]
   have hboxMem : orig_x ∈ inp.boxes := List.mem_of_getElem? horigLookup
   obtain ⟨parentBox, hparentMem, hpid, hpgroup, hpnotfixed⟩ :=
     framedParents_parent hframed hboxMem hpxne
   have hnp : ¬(inp.fixedSizes.any (fun fixed : String × Size =>
       fixed.1 == parentBox.id) = true) := by
     intro hc
     rw [hc] at hpnotfixed
     simp at hpnotfixed
   obtain ⟨p₀, hp₀⟩ := List.mem_iff_getElem?.mp hparentMem
   have hfbp : (inp.boxes.map fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box)[p₀]? = some parentBox := by
     simp only [List.getElem?_map, hp₀, Option.map_some, ite_eq_right hnp]
   have hp₀bound : p₀ < lines.length := by
     have hi := (List.getElem?_eq_some_iff.mp hfbp).1
     rw [List.length_map] at hi
     omega
   obtain ⟨topP, bottomP, htopPlookup, hbotmem, htopPborder, hbotborder, htopdecl,
       hbotdecl, htopPpath, hbotpath, hbotw, hboth⟩ :=
     measuredGraph_paired_markers h0 hp₀bound hfbp hpgroup
   clear bottomP hbotmem hbotborder htopdecl hbotdecl hbotpath hbotw hboth
   obtain ⟨topP', htopPlook', htopPbord', htopPpath', _⟩ :=
     exactGraph_node_key h htopPlookup
   have htopPborder : topP'.border = -2 := htopPbord'.trans htopPborder
   have hpathOrig : Compound.path (inp.boxes.map fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box) orig_x =
       Compound.path inp.boxes orig_x := by
     have h := Compound.path_map inp.boxes (fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box) Xb_demote_id Xb_demote_parent hboxMem
     rw [ite_eq_right hnf] at h
     exact h
   have hpathParent : Compound.path (inp.boxes.map fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box) parentBox =
       Compound.path inp.boxes parentBox := by
     have h := Compound.path_map inp.boxes (fun box =>
       if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
         { box with role := .node } else box) Xb_demote_id Xb_demote_parent hparentMem
     rw [ite_eq_right hnp] at h
     exact h
   have hpathStep : Compound.path inp.boxes orig_x =
       Compound.path inp.boxes parentBox ++ [p₀] :=
     Compound.path_of_parent (inputModel inp o) hwf hp₀ horigLookup (by rw [hpid]) hpxne
   have hdropFinal : topP'.clusterPath = x.1.clusterPath.dropLast := by
     rw [htopPpath', htopPpath, hpathParent, ← hpathStep, ← hpathOrig, ← hdrop]
   have htopPzip : (topP', p₀) ∈ graph.nodes.zipIdx :=
     List.mem_zipIdx_iff_getElem?.mpr htopPlook'
   have htopZip : (x.1, oIdx) ∈ graph.nodes.zipIdx :=
     List.mem_zipIdx_iff_getElem?.mpr hsource
   obtain ⟨xb, hxbfind⟩ := X_groupTopFind?_some h0 h hlines htopZip hxGroup
   obtain ⟨pb, hpbfind⟩ := X_groupTopFind?_some h0 h hlines htopPzip htopPborder
   obtain ⟨heP, _⟩ := compound_child_constraint_edges htopPzip htopPborder hpbfind
     htopZip hxGroup hdropFinal.symm hxbfind
   obtain ⟨c, hcMem, hcP, hcO⟩ :=
     components_edge_endpoints hbd (List.mem_append_right _ heP)
   have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcO hoIn
   rw [hcEq] at hcP
   have htopPin : topP' ∈ (componentCandidate graph comp candidate).nodes := by
     rw [componentCandidate_nodes]
     exact List.mem_map.mpr ⟨p₀, hcP, by
       rw [List.getD_eq_getElem?_getD, htopPlook']
       rfl⟩
   obtain ⟨i₀, hi₀⟩ := List.mem_iff_getElem?.mp htopPin
   have hp : ((fun entry : Node × Nat =>
       entry.1.border == -2 && entry.1.clusterPath == x.1.clusterPath.dropLast)
       (topP', i₀)) = true := by
     simp [htopPborder, hdropFinal]
   exact Xb_findSomeOfMember (List.mem_zipIdx_iff_getElem?.mpr hi₀) hp

 /-- Exact nested-bottom rank bound (exact counterpart of `BottomNestedBottomRankLe`).
 Residual: ranking is identical in the exact run, but the nested-top pairing
 (`componentRun_cg_top_of_bottom` over the exact graph) is not yet replayed. -/
 def Xb_NestedExact (exactIds : List String) : Prop :=
   ∀ {P : Params} {inp : Input} {o : Options}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel},
     measuredGraph P inp o lines = .ok graph0 →
     exactGraph P exactIds inp o measured graph0 = .ok graph →
     lines.length = inp.boxes.length →
     WellFormed (inputModel inp o) →
     framedParents inp = true →
     ∀ {comp : List Nat}, comp ∈ components graph →
     ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
       {orderOptions : OrderOptions},
     componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels
       orderOptions = .ok run →
     ∀ {v t : Nat} {ndV ndT : Node},
     (componentCandidate graph comp candidate).nodes[v]? = some ndV →
     (componentCandidate graph comp candidate).nodes[t]? = some ndT →
     ndV.border = 2 → ndT.border = -2 → ndV.decl = ndT.decl →
     ∀ {j : Nat} {nb : Node},
     (componentCandidate graph comp candidate).nodes[j]? = some nb →
     nb.border = 2 → nb.decl ≠ ndT.decl →
     nb.clusterPath.contains ndT.decl = true →
     rk run.coordinateProper.rank j ≤ rk run.coordinateProper.rank v

 /-- A nonempty filter yields a list (copy of the private
 `filter_ne_nil_of_not_empty` of `GroupBottomBoundaryProof.lean`). -/
 private theorem Xb_filter_ne_nil {α : Type} {l : List α}
     (h : l.isEmpty = false) : l ≠ [] := by
   intro hnil
   rw [hnil] at h
   simp at h

 /-- A member is at most the foldr max (copy of the private `X_le_foldr_max`
 of `ExactFlatC5Rank.lean`). -/
 private theorem Xb_le_foldr_max {l : List Nat} {a : Nat} (h : a ∈ l) :
     a ≤ l.foldr max 0 := by
   induction l with
   | nil => simp at h
   | cons x xs ih =>
     simp only [List.foldr_cons]
     rcases List.mem_cons.mp h with rfl | h'
     · exact Nat.le_max_left _ _
     · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

 /-- Original member rank bound by fuel induction over cluster-path length
 (replay of `bottomOrigRankLe` through the exact source lemmas). -/
 private theorem Xb_origRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hframed : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph)
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions}
     (hrun : componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels
       orderOptions = .ok run)
     {v t : Nat} {ndV ndT : Node}
     (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
     (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
     (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
     (hdecl : ndV.decl = ndT.decl)
     (hnest : Xb_NestedExact exactIds) :
     ∀ {idx : Nat} {n : Node},
     (componentCandidate graph comp candidate).nodes[idx]? = some n →
     n.clusterPath.contains ndT.decl = true →
     rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v := by
   obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
     X_cg_run_bundle h0 h hcomp hrun
   have hfindV : (componentCandidate graph comp candidate).nodes.zipIdx.find?
       (fun entry => entry.1.border == 2 && entry.1.decl == ndV.decl) = some (ndV, v) :=
     X_bottom_find_eq h0 h hcomp hvGet hbordV
   have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
       (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) = some (ndV, v) := by
     rw [← hdecl]; exact hfindV
   have htopOuter : ((ndT, t) : Node × Nat) ∈
       (componentCandidate graph comp candidate).nodes.zipIdx :=
     List.mk_mem_zipIdx_iff_getElem?.mpr htGet
   have eV : rk run.coordinateProper.rank v = rk rr.ranks v := by
     have h1 := Xb_prepared_rk hrr hc hranks (List.getElem?_eq_some_iff.mp hvGet).1
     exact h1
   let cg := componentCandidate graph comp candidate
   let maxLen := ((cg.nodes.filter fun n => n.border == -2).map
     (fun n => n.clusterPath.length)).foldr max 0
   have hbound : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
       node.border = -2 → node.clusterPath.length ≤ maxLen := by
     intro index node hnode hgroup
     have hmem : node ∈ cg.nodes.filter (fun n => n.border == -2) :=
       List.mem_filter.mpr ⟨List.mem_of_getElem? hnode, by simp [hgroup]⟩
     have hmap : node.clusterPath.length ∈
         (cg.nodes.filter fun n => n.border == -2).map
           (fun n => n.clusterPath.length) :=
       List.mem_map_of_mem hmem
     exact Xb_le_foldr_max hmap
   have hnonempty : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
       node.border = -2 → node.clusterPath ≠ [] := by
     intro index node hnode hgroup hnil
     exact (X_componentCandidate_marker_shape h0 h hnode).2 hgroup hnil
   have main : ∀ fuel idx n, cg.nodes[idx]? = some n →
       n.clusterPath.contains ndT.decl = true →
       maxLen - n.clusterPath.length = fuel → rk rr.ranks idx ≤ rk rr.ranks v := by
     intro fuel
     induction fuel using Nat.strongRecOn with
     | _ fuel ih =>
       intro idx n hidx hcontains hfuel
       rcases (X_componentCandidate_marker_shape h0 h hidx).1 with hplain | hgroup | hbottom
       · have hinterval := ranked_compound_member_interval hrr htopOuter hbordT
           hbotFindOuter (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hplain hcontains
         have hle : rk rr.ranks idx + 1 ≤ rk rr.ranks v := hinterval.2
         omega
       · obtain ⟨rrB, labeledB, bottomTB, hrrB, hcB, hkB, hreadyB, hrecordsB, hranksB,
             htitledB, hfindB⟩ :=
           X_group_bottom_source h0 h hcomp hrun hidx hgroup
         obtain ⟨origB, horigB, hborderB, hpathB, hrecordB, hfindCB⟩ :=
           X_bottom_constraint_source h0 h hkB hrecordsB hidx hgroup hfindB
         have hpathBmem : origB.clusterPath.contains ndT.decl = true := by
           rw [hpathB]; exact hcontains
         have resolveB : rk rr.ranks bottomTB.2 ≤ rk rr.ranks v := by
           by_cases hdeq : origB.decl = ndT.decl
           · have hmemB := List.find?_some hfindCB
             simp only [Bool.and_eq_true, beq_iff_eq] at hmemB
             have hndeq : n.decl = ndT.decl := hmemB.2.symm.trans hdeq
             rw [hndeq] at hfindCB
             have heq : (origB, bottomTB.2) = (ndV, v) :=
               Option.some.inj (hfindCB.symm.trans hbotFindOuter)
             have hbv : bottomTB.2 = v := congrArg Prod.snd heq
             rw [hbv]
             exact Int.le_refl _
           · have hleB : rk run.coordinateProper.rank bottomTB.2 ≤
               rk run.coordinateProper.rank v :=
               hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
                 horigB hborderB hdeq hpathBmem
             have e1 : rk run.coordinateProper.rank bottomTB.2 =
                 rk rr.ranks bottomTB.2 := by
               have h1 := Xb_prepared_rk hrr hc hranks
                 (List.getElem?_eq_some_iff.mp horigB).1
               exact h1
             omega
         cases hmemCase : (cg.nodes.zipIdx.filter fun entry =>
             entry.1.border == 0 && entry.1.clusterPath.contains n.decl).isEmpty with
         | false =>
           obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _
             (Xb_filter_ne_nil hmemCase)
           obtain ⟨hmemberZip, hmemberCond⟩ := List.mem_filter.mp hmember
           obtain ⟨hmemberPlain, hmemberInside⟩ := Bool.and_eq_true_iff.mp hmemberCond
           have hmemberPlain' : member.1.border = 0 := by simpa using hmemberPlain
           have hmemberInside' : member.1.clusterPath.contains n.decl = true := by
             simpa using hmemberInside
           have hinterval := ranked_compound_member_interval hrr
             (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB
             hmemberZip hmemberPlain' hmemberInside'
           have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks member.2 := hinterval.1
           have hR : rk rr.ranks member.2 + 1 ≤ rk rr.ranks bottomTB.2 := hinterval.2
           omega
         | true =>
           cases hchildCase : ((cg.nodes.zipIdx.filter fun entry => entry.1.border == -2).filter
               fun entry => entry.1.clusterPath.dropLast == n.clusterPath).isEmpty with
           | false =>
             obtain ⟨child, hchildMem⟩ := List.exists_mem_of_ne_nil _
               (Xb_filter_ne_nil hchildCase)
             obtain ⟨hchildTop, hchildPathEq⟩ := List.mem_filter.mp hchildMem
             obtain ⟨hchildZip, hchildGroup⟩ := List.mem_filter.mp hchildTop
             have hchildGroup' : child.1.border = -2 := by simpa using hchildGroup
             have hchildIndex := List.mem_zipIdx_iff_getElem?.mp hchildZip
             obtain ⟨rrC, labeledC, bottomTC, hrrC, hcC, hkC, hreadyC, hrecordsC, hranksC,
                 htitledC, hfindC⟩ :=
               X_group_bottom_source h0 h hcomp hrun hchildIndex hchildGroup'
             obtain ⟨childOriginal, horigC, hborderC, hpathC, hrecordC, hchildFind'⟩ :=
               X_bottom_constraint_source h0 h hkC hrecordsC hchildIndex
                 hchildGroup' hfindC
             have hchildPair : cg.nodes.zipIdx.find? (fun entry =>
                 entry.1.border == 2 && entry.1.decl == child.1.decl) =
                 some (childOriginal, bottomTC.2) := hchildFind'
             have hpathEq : child.1.clusterPath.dropLast = n.clusterPath := by
               simpa using hchildPathEq
             have hdirect := ranked_compound_child_interval hrr
               (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB
               hchildZip hchildGroup' hpathEq hchildPair
             have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks child.2 := hdirect.1
             have hne : n.clusterPath ≠ [] := hnonempty idx n hidx hgroup
             have hchildNonEmpty : child.1.clusterPath ≠ [] := by
               intro hempty
               rw [hempty, List.dropLast_nil] at hpathEq
               exact hne hpathEq.symm
             have hlenC : child.1.clusterPath.length = n.clusterPath.length + 1 := by
               rw [← hpathEq, List.length_dropLast]
               have hchildLen := List.length_pos_iff.mpr hchildNonEmpty
               omega
             have hboundChild := hbound child.2 child.1 hchildIndex hchildGroup'
             have hpos : 0 < fuel := by omega
             have hfuelChild : maxLen - child.1.clusterPath.length = fuel - 1 := by omega
             have hcontainsC : child.1.clusterPath.contains ndT.decl = true := by
               have hsub : n.clusterPath <+: child.1.clusterPath := by
                 rw [← hpathEq]; exact Xb_dropLast_is_prefix _
               have hmemN : ndT.decl ∈ n.clusterPath :=
                 List.contains_iff_mem.mp hcontains
               have hmemC : ndT.decl ∈ child.1.clusterPath :=
                 List.Sublist.mem hmemN (List.IsPrefix.sublist hsub)
               exact List.contains_iff_mem.mpr hmemC
             have hih := ih (fuel - 1) (by omega) child.2 child.1 hchildIndex
               hcontainsC hfuelChild
             omega
           | true =>
             have hempty := ranked_empty_group_interval hrr
               (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB hmemCase hchildCase
             have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks bottomTB.2 := hempty
             omega
       · by_cases hdeq : n.decl = ndT.decl
         · have hfindEq : (componentCandidate graph comp candidate).nodes.zipIdx.find?
               (fun entry => entry.1.border == 2 && entry.1.decl == n.decl) =
               some (n, idx) :=
             X_bottom_find_eq h0 h hcomp hidx hbottom
           rw [hdeq] at hfindEq
           have heq : (n, idx) = (ndV, v) :=
             Option.some.inj (hfindEq.symm.trans hbotFindOuter)
           have hiv : idx = v := congrArg Prod.snd heq
           rw [hiv]
           exact Int.le_refl _
         · have hleB : rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v :=
             hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
               hidx hbottom hdeq hcontains
           have e1 : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
             have h1 := Xb_prepared_rk hrr hc hranks
               (List.getElem?_eq_some_iff.mp hidx).1
             exact h1
           omega
   intro idx n hidx hcontains
   have hrr_le := main (maxLen - n.clusterPath.length) idx n hidx hcontains rfl
   have eI : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
     have h1 := Xb_prepared_rk hrr hc hranks
       (List.getElem?_eq_some_iff.mp hidx).1
     exact h1
   omega

 /-- From `toNat` order to `Int` order under nonnegativity (copy of the private
 `toNat_le_of_nonneg` of `BottomSyntheticRankProof.lean`). -/
 private theorem Xb_toNat_le_of_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
     (h : a.toNat ≤ b.toNat) : a ≤ b := by
   have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
   have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
   have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by exact_mod_cast h
   omega

 /-- Exact side-marker rank bound (replay of `side_marker_rank_le` through
 `X_side_original` and the generic `addClusterBorders_side_rank_bounds`). -/
 private theorem Xb_sideRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hframed : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph)
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions}
     (hrun : componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels
       orderOptions = .ok run)
     {v t : Nat} {ndV ndT : Node}
     (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
     (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
     (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
     (hdecl : ndV.decl = ndT.decl)
     (hnest : Xb_NestedExact exactIds)
     (q : ProperNode × Nat) (hq : q ∈ run.proper.nodes.zipIdx)
     (hcontains : q.1.node.clusterPath.contains
       ((componentCandidate graph comp candidate).nodes.getD t default).decl = true)
     (hside : q.1.node.border = -1 ∨ q.1.node.border = 1) :
     rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
   obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
     X_cg_run_bundle h0 h hcomp hrun
   have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
       ndT.decl := by
     rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
   have hqget : run.proper.nodes[q.2]? = some q.1 :=
     List.mem_zipIdx_iff_getElem?.mp hq
   obtain ⟨nvc, hnc, hborderEq, _, hpathImp⟩ := Xb_fbs hrun hqget
   have hsideC : nvc.node.border = -1 ∨ nvc.node.border = 1 := by
     rw [hborderEq]; exact hside
   have hncX : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[q.2]? = some nvc := by
     rw [hc]; exact hnc
   have hcoordXrfl : (coordinateGraphX P (exactDecls exactIds inp) labeled).rank =
       (OrderImpl.addClusterBorders
         (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))
         P.clusterBorderW).rank := rfl
   have horiginal := X_side_original hready hncX hsideC
   obtain ⟨top, htopMem, bottom, hfindB, hpathEq, hnn, htonat, hhi⟩ :=
     addClusterBorders_side_rank_bounds _ _ hready horiginal hsideC
   have htopGet : (titleReservations
       (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? =
       some top.1 :=
     List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp htopMem).1
   have htopBorder : top.1.node.border = -2 := by
     simpa using (List.mem_filter.mp htopMem).2
   obtain ⟨topOrig, htopCg, htopBorderEq, htopRecord⟩ :=
     X_titled_marker_source_record hk hrecords htopGet (Or.inl htopBorder)
   have htopCgBorder : topOrig.border = -2 := htopBorderEq.symm.trans htopBorder
   have htopPath : top.1.node.clusterPath = topOrig.clusterPath := by
     rw [htopRecord]; exact (titleF_keys _).2.2.1
   have hnotProxy : ¬(nvc.node.border = -2 ∨ nvc.node.border = 2) := by
     rintro (h | h) <;> omega
   have hnvcPath : nvc.node.clusterPath = q.1.node.clusterPath :=
     hpathImp hnotProxy
   have htopContains : top.1.node.clusterPath.contains ndT.decl = true := by
     rw [← hpathEq, hnvcPath, ← hdeclT]; exact hcontains
   have htopOrigContains : topOrig.clusterPath.contains ndT.decl = true := by
     rw [← htopPath]; exact htopContains
   have hfindB' : ((titleReservations
       (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
         entry.1.node.border == 2 &&
           entry.1.node.clusterPath == topOrig.clusterPath) = some bottom := by
     rw [← htopPath]; exact hfindB
   obtain ⟨origB, horigB, hborderB, hpathB, _, _⟩ :=
     X_bottom_constraint_source h0 h hk hrecords htopCg
       htopCgBorder hfindB'
   have hpathBmem : origB.clusterPath.contains ndT.decl = true := by
     rw [hpathB]; exact htopOrigContains
   have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
       (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) =
       some (ndV, v) := by
     rw [← hdecl]; exact X_bottom_find_eq h0 h hcomp hvGet hbordV
   have hBle : rk run.coordinateProper.rank bottom.2 ≤
       rk run.coordinateProper.rank v := by
     by_cases hdeq : origB.decl = ndT.decl
     · have hfindBdec := X_bottom_find_eq h0 h hcomp horigB hborderB
       rw [hdeq] at hfindBdec
       have heq := Option.some.inj (hfindBdec.symm.trans hbotFindOuter)
       have hbv : bottom.2 = v := congrArg Prod.snd heq
       rw [hbv]
       exact Int.le_refl _
     · exact hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
         horigB hborderB hdeq hpathBmem
   have hBcoord : rk run.coordinateProper.rank bottom.2 = rk rr.ranks bottom.2 := by
     have hlt : bottom.2 < (componentCandidate graph comp candidate).nodes.length :=
       (List.getElem?_eq_some_iff.mp horigB).1
     have h1 := Xb_prepared_rk hrr hc hranks hlt
     exact h1
   have hBtitle : rk (titleReservations
       (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bottom.2 =
       rk rr.ranks bottom.2 := by
     have h1 := Xb_titled_rk (P := P) (exact := exactDecls exactIds inp) hrr hranks
       (List.getElem?_eq_some_iff.mp horigB).1
     exact h1.1
   have hBnn : 0 ≤ rk rr.ranks bottom.2 := rankWithBudget_rk_nonneg hrr bottom.2
   have hbotnn : 0 ≤ rk run.coordinateProper.rank bottom.2 := by
     rw [hBcoord]; exact hBnn
   have htonat : (rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank q.2).toNat ≤
       (rk run.coordinateProper.rank bottom.2).toNat := by
     rw [hcoordXrfl, hBcoord, ← hBtitle]; exact hhi
   have hqb : rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank q.2 ≤
       rk run.coordinateProper.rank bottom.2 :=
     Xb_toNat_le_of_nonneg hnn hbotnn htonat
   have hq : rk run.coordinateProper.rank q.2 ≤
       rk run.coordinateProper.rank bottom.2 := by
     have hQ : rk run.coordinateProper.rank q.2 =
         rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank q.2 := by
       rw [hc]
     rw [hQ]; exact hqb
   exact Int.le_trans hq hBle

 /-- Exact titled rank record (replay of `titled_rank_record` through
 `sizeProperPortsX`). -/
 private theorem Xb_titled_rank_record {P : Params} {exact : List Nat} {source : Proper}
     {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
     (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
   obtain ⟨extra, heq⟩ := Xb_titled_rank_prefix P exact source
   rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
   exact h

 /-- Exact title-copy rank record (replay of `titled_copy_rank_record` through
 `sizeProperPortsX`). -/
 private theorem Xb_titled_copy_rank_record {P : Params} {exact : List Nat} {labeled : Proper}
     (haligned : labeled.nodes.length = labeled.rank.length)
     {position : Nat} {entry : ProperNode × Nat}
     (hentry : (titleNodes (sizeProperPortsX P exact labeled))[position]? = some entry) :
     (titleReservations (sizeProperPortsX P exact labeled)).rank[labeled.nodes.length + position]? =
       some (rk labeled.rank entry.2) := by
   have hsized : (sizeProperPortsX P exact labeled).rank = labeled.rank := rfl
   have hrank : (titleReservations (sizeProperPortsX P exact labeled)).rank =
       labeled.rank ++ (titleNodes (sizeProperPortsX P exact labeled)).map
         (fun value => rk labeled.rank value.2) := by
     have h0 : (titleReservations (sizeProperPortsX P exact labeled)).rank =
         (sizeProperPortsX P exact labeled).rank ++
           (titleNodes (sizeProperPortsX P exact labeled)).map
             (fun value => rk (sizeProperPortsX P exact labeled).rank value.2) := by
       unfold titleReservations titleNodes sizeProperPortsX
       rfl
     rw [h0, hsized]
   rw [hrank, List.getElem?_append_right (by omega)]
   have hindex : labeled.nodes.length + position - labeled.rank.length = position := by omega
   rw [hindex, List.getElem?_map, hentry]
   rfl

 /-- Exact titled rank record in the coordinate graph (replay of
 `coordinateGraph_titled_rank_record` through `coordinateGraphX_anchor_prefix`). -/
 private theorem Xb_coord_titled_rank_record {P : Params} {exact : List Nat} {labeled : Proper}
     {index : Nat} {rank : Int}
     (h : (titleReservations (sizeProperPortsX P exact labeled)).rank[index]? = some rank) :
     (coordinateGraphX P exact labeled).rank[index]? = some rank := by
   obtain ⟨extraC, heqC⟩ := coordinateGraphX_anchor_prefix P exact labeled
   obtain ⟨extraA, heqA⟩ := addClusterBorders_rank_prefix
     (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
   have hlen : index < (titleReservations (sizeProperPortsX P exact labeled)).rank.length :=
     (List.getElem?_eq_some_iff.mp h).1
   have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).rank[index]? =
       some rank := by
     have hrfl : (clearProxyExtents (OrderImpl.addClusterBorders
         (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).rank =
         (OrderImpl.addClusterBorders
           (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank := rfl
     rw [hrfl, heqA, List.getElem?_append_left (by omega : index < (titleReservations
       (sizeProperPortsX P exact labeled)).rank.length)]
     exact h
   have hmat : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).rank[index]? =
       some rank := by
     have hrfl : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).rank =
       (clearProxyExtents (OrderImpl.addClusterBorders
         (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).rank := rfl
     rw [hrfl]; exact hclear
   have hunfold : coordinateGraphX P exact labeled =
       materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
         (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)) := rfl
   rw [hunfold]; exact hmat

 /-- Exact coordinate title-copy source (replay of `coordinateGraph_title_rank_source`
 through `Xb_coord_lookup`). -/
 private theorem Xb_title_rank_source {cg : Graph} {P : Params} {exact : List Nat}
     {labeled : Proper}
     (hkeys : NodeKeys cg labeled) (hshape : CgShape cg)
     (haligned : labeled.nodes.length = labeled.rank.length)
     {titleIndex : Nat} {title : ProperNode}
     (htitle : (coordinateGraphX P exact labeled).nodes[titleIndex]? = some title)
     (hborder : title.node.border = 3) :
     ∃ (originalIndex : Nat) (original : ProperNode),
       labeled.nodes[originalIndex]? = some original ∧
       original.node.border = -2 ∧ original.dummy = false ∧
       title.dummy = false ∧ title.node.clusterPath = original.node.clusterPath ∧
       rk (coordinateGraphX P exact labeled).rank titleIndex = rk labeled.rank originalIndex := by
   rcases Xb_coord_lookup P exact labeled htitle with
     ⟨original, horiginal, _, hb, _, _⟩ | ⟨_, hside⟩ |
     ⟨position, entry, hentry, hindex, hd, _, hp⟩
   · rcases hkeys titleIndex original horiginal with
       ⟨before, hbefore, _, hbeforeBorder, _⟩ | ⟨_, hplain, _⟩
     · have hnot := hshape.2 before (List.mem_of_getElem? hbefore)
       exact (hnot (hbeforeBorder.symm.trans (hb.symm.trans hborder))).elim
     · omega
   · rcases hside with hside | hside <;> omega
   · obtain ⟨hsized, hsizedBorder⟩ := titleNodes_spec hentry
     obtain ⟨original, horiginal, hsourceDummy, hsourceBorder, hsourcePath⟩ :=
       X_sizeProperPorts_node_origin P exact labeled hsized
     have hsourceGroup : original.node.border = -2 := hsourceBorder.symm.trans hsizedBorder
     have horiginalReal : original.dummy = false := by
       rcases hkeys entry.2 original horiginal with
         ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
       · exact hreal
       · omega
     have hentryReal : entry.1.dummy = false := hsourceDummy.trans horiginalReal
     have htitleReal : title.dummy = false := hd.trans hentryReal
     have htitlePath : title.node.clusterPath = original.node.clusterPath :=
       (hp hentryReal).trans hsourcePath
     have htitledRank := Xb_titled_copy_rank_record haligned hentry
     have hcoordinateRank := Xb_coord_titled_rank_record htitledRank
     refine ⟨entry.2, original, horiginal, hsourceGroup, horiginalReal,
       htitleReal, htitlePath, ?_⟩
     rw [hindex]
     simp only [rk, List.getD_eq_getElem?_getD, hcoordinateRank, Option.getD_some]

 /-- Exact title-copy rank bound (replay of `title_copy_rank_le`). -/
 private theorem Xb_titleRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hframed : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph)
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions}
     (hrun : componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels
       orderOptions = .ok run)
     {v t : Nat} {ndV ndT : Node}
     (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
     (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
     (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
     (hdecl : ndV.decl = ndT.decl)
     (hnest : Xb_NestedExact exactIds)
     (q : ProperNode × Nat) (hq : q ∈ run.proper.nodes.zipIdx)
     (hcontains : q.1.node.clusterPath.contains
       ((componentCandidate graph comp candidate).nodes.getD t default).decl = true)
     (hb3 : q.1.node.border = 3) :
     rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
   obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
     X_cg_run_bundle h0 h hcomp hrun
   have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
     (exactGraph_shape (measuredGraph_shape h0) h) candidate
   have hqget : run.proper.nodes[q.2]? = some q.1 :=
     List.mem_zipIdx_iff_getElem?.mp hq
   obtain ⟨nvc, hnc, hborderEq, _, hpathImp⟩ := Xb_fbs hrun hqget
   have hncL : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[q.2]? = some nvc := by
     rw [hc]; exact hnc
   have hb3C : nvc.node.border = 3 := by rw [hborderEq]; exact hb3
   obtain ⟨originalIndex, original, horiginal, hOrigBorder, hOrigReal, _, htitlePath,
       htitleRank⟩ :=
     Xb_title_rank_source hk hshape haligned hncL hb3C
   have hnvcPath : nvc.node.clusterPath = q.1.node.clusterPath := by
     apply hpathImp
     rintro (h | h) <;> omega
   have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
       ndT.decl := by
     rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
   have horigContains : original.node.clusterPath.contains ndT.decl = true := by
     rw [← htitlePath, hnvcPath, ← hdeclT]; exact hcontains
   rcases hk originalIndex original horiginal with
     ⟨n, hn, _, hborderN, hpathN⟩ | ⟨hdT, _, _⟩
   · have hnBorder : n.border = -2 := hborderN.symm.trans hOrigBorder
     have hncN : n.clusterPath.contains ndT.decl = true := by
       rw [← hpathN]; exact horigContains
     have hle := Xb_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
       hnest hn hncN
     have hrankEq : rk run.coordinateProper.rank q.2 = rk labeled.rank originalIndex := by
       rw [← hc]; exact htitleRank
     have hlabEq : rk labeled.rank originalIndex =
         rk run.coordinateProper.rank originalIndex := by
       have h1 : originalIndex < labeled.nodes.length :=
         (List.getElem?_eq_some_iff.mp horiginal).1
       exact (Xb_coord_rank_eq hc haligned h1).symm
     rw [hrankEq, hlabEq]; exact hle
   · exact absurd (hdT.symm.trans hOrigReal) (by decide)

 /-- Dummy-only restriction of the exact bottom synthetic bound: an executed exact edge
 dummy whose path carries the outer declaration ranks at or below the outer bottom proxy
 (exact counterpart of `bottomDummyRankLe`). -/
 theorem X_bottomDummyRankLe (exactIds : List String) (hnest : Xb_NestedExact exactIds) :
     ∀ {P : Params} {inp : Input} {o : Options}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel},
     measuredGraph P inp o lines = .ok graph0 →
     exactGraph P exactIds inp o measured graph0 = .ok graph →
     lines.length = inp.boxes.length →
     WellFormed (inputModel inp o) →
     framedParents inp = true →
     ∀ {comp : List Nat}, comp ∈ components graph →
     ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
       {orderOptions : OrderOptions},
     componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels
       orderOptions = .ok run →
     ∀ {v t : Nat} {ndV ndT : Node},
     (componentCandidate graph comp candidate).nodes[v]? = some ndV →
     (componentCandidate graph comp candidate).nodes[t]? = some ndT →
     ndV.border = 2 → ndT.border = -2 → ndV.decl = ndT.decl →
     ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
     q.1.node.clusterPath.contains
       ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
     q.1.dummy = true →
     rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
   intro P inp o lines graph0 graph measured h0 h hlines hwf hframed comp hcomp candidate run
     labels orderOptions hrun v t ndV ndT hvGet htGet hbordV hbordT hdecl q hq
     hcontains hdum
   have hqget : run.proper.nodes[q.2]? = some q.1 :=
     List.mem_zipIdx_iff_getElem?.mp hq
   have hlen : q.2 < run.proper.nodes.length :=
     (List.getElem?_eq_some_iff.mp hqget).1
   have hgetD : run.proper.nodes.getD q.2 default = q.1 := by
     simp [List.getD_eq_getElem?_getD, hqget]
   have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
       ndT.decl := by
     rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
   have howner : ((componentCandidate graph comp candidate).nodes.getD t default).decl ∈
       (run.proper.nodes.getD q.2 default).node.clusterPath := by
     rw [hgetD]; exact List.contains_iff_mem.mp hcontains
   have hdumQ : (run.proper.nodes.getD q.2 default).dummy = true := by
     rw [hgetD]; exact hdum
   obtain ⟨_, _, _, _, _, _, _, hle2, _, nB, _, hnB, _, hcontB⟩ :=
     Xb_bracket hrun hlen hdumQ howner
   have hcontB' : nB.clusterPath.contains ndT.decl = true := by
     rw [← hdeclT]; exact hcontB
   have hle := Xb_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet
     hbordV hbordT hdecl hnest hnB hcontB'
   exact Int.le_trans hle2 hle
 /-- Exact nested-bottom rank induction at ranking-graph level (replay of
 `bnr_nested_bottom_rank` through the exact source lemmas). -/
 private theorem Xb_nested_bottom_rank {P : Params} {inp : Input} {o : Options}
     {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hframed : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
     {rr : RankImpl.RankResult}
     (hrr : rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
       .ok rr) :
     ∀ delta : Nat, ∀ a b : Nat, ∀ na nb : Node, ∀ ba bb : Node × Nat,
       (componentCandidate graph comp candidate).nodes[a]? = some na →
       na.border = -2 →
       (componentCandidate graph comp candidate).nodes[b]? = some nb →
       nb.border = -2 →
       na.clusterPath <+: nb.clusterPath →
       nb.clusterPath.length - na.clusterPath.length = delta →
       (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
         entry.1.border == 2 && entry.1.decl == na.decl) = some ba →
       (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
         entry.1.border == 2 && entry.1.decl == nb.decl) = some bb →
       rk rr.ranks bb.2 ≤ rk rr.ranks ba.2 := by
   intro delta
   induction delta using Nat.strongRecOn with
   | _ delta ih =>
     intro a b na nb ba bb ha hbA hb hbB hpre hdelta hba hbb
     by_cases heq : na.clusterPath = nb.clusterPath
     · have hab : a = b := X_cg_top_unique h0 h hcomp ha hb hbA hbB heq
       subst hab
       have hdecl : na.decl = nb.decl := by
         have hlastA : na.clusterPath.getLast? = some na.decl := by
           obtain ⟨box, hbox, hpathA⟩ := X_cg_group_box h0 h ha hbA
           exact Xb_cg_path_last hpathA
         have hlastB : nb.clusterPath.getLast? = some nb.decl := by
           obtain ⟨box, hbox, hpathB⟩ := X_cg_group_box h0 h hb hbB
           exact Xb_cg_path_last hpathB
         have h := congrArg List.getLast? heq
         rw [hlastA, hlastB] at h
         exact Option.some.inj h
       rw [hdecl] at hba
       have hbb_eq : bb = ba := Option.some.inj (hbb.symm.trans hba)
       rw [hbb_eq]
       exact Int.le_refl _
     · have hlt : na.clusterPath.length < nb.clusterPath.length :=
         Xb_prefix_length_lt hpre heq
       have hbne : nb.clusterPath ≠ [] :=
         (X_componentCandidate_marker_shape h0 h hb).2 hbB
       have hna_ne : na.clusterPath ≠ [] :=
         (X_componentCandidate_marker_shape h0 h ha).2 hbA
       obtain ⟨u, hu⟩ := X_candidate_parent_top_exists h0 h hlines hwf hframed hcomp candidate
         (x := (nb, b)) (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpre hlt hna_ne
       have huPred := List.find?_some hu
       simp only [Bool.and_eq_true, beq_iff_eq] at huPred
       obtain ⟨huBorder, huPath⟩ := huPred
       have huMem : u ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
         List.mem_of_find?_eq_some hu
       have huLookup : (componentCandidate graph comp candidate).nodes[u.2]? = some u.1 :=
         List.mem_zipIdx_iff_getElem?.mp huMem
       have hdropLen : u.1.clusterPath.length = nb.clusterPath.length - 1 := by
         rw [huPath]
         exact List.length_dropLast ..
       have hnbpos : 0 < nb.clusterPath.length :=
         Nat.pos_of_ne_zero (fun h => hbne (List.length_eq_zero_iff.mp h))
       have hleU : na.clusterPath.length ≤ u.1.clusterPath.length := by omega
       have hpreU : na.clusterPath <+: u.1.clusterPath :=
         Xb_prefix_of_common_prefix hpre (huPath ▸ Xb_dropLast_is_prefix nb.clusterPath) hleU
       have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
       obtain ⟨ubot, hubot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp huLookup huBorder
       have hIH := ih _ hdeltaU a u.2 na u.1 ba ubot ha hbA huLookup huBorder hpreU rfl hba hubot
       have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
       have hinterv := ranked_compound_child_interval (parent := (u.1, u.2)) (child := (nb, b)) hrr
         (List.mem_zipIdx_iff_getElem?.mpr huLookup) huBorder hubot
         (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpathUB hbb
       omega

 /-- The exact nested-bottom rank bound holds unconditionally (replay of
 `bottomNestedBottomRankLe_wf` through the exact source lemmas). This discharges
 the `Xb_NestedExact` residual used by `Xb_origRankLe` and `X_bottomDummyRankLe`. -/
 theorem Xb_NestedExact_holds (exactIds : List String) : Xb_NestedExact exactIds := by
   unfold Xb_NestedExact
   intro P inp o lines graph0 graph measured h0 h hlines hwf hframed comp hcomp candidate run
     labels orderOptions hrun v t ndV ndT hvGet htGet hbordV hbordT hdecl j nb
     hjGet hbordJ hne hcontains
   obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
     X_cg_run_bundle h0 h hcomp hrun
   have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
       (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) = some (ndV, v) := by
     have hfindV := X_bottom_find_eq h0 h hcomp hvGet hbordV
     rw [← hdecl]
     exact hfindV
   obtain ⟨tn, htnFind⟩ := X_componentRun_cg_top_of_bottom h0 h hlines hcomp hjGet hbordJ
   have htnPred := List.find?_some htnFind
   simp only [Bool.and_eq_true, beq_iff_eq] at htnPred
   obtain ⟨htnBorder, htnPathEq⟩ := htnPred
   have htnMem : tn ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
     List.mem_of_find?_eq_some htnFind
   have htnLookup : (componentCandidate graph comp candidate).nodes[tn.2]? = some tn.1 :=
     List.mem_zipIdx_iff_getElem?.mp htnMem
   have hdeclTn : tn.1.decl = nb.decl := by
     have hlastTn : tn.1.clusterPath.getLast? = some tn.1.decl := by
       obtain ⟨box, hbox, hpathTn⟩ := X_cg_group_box h0 h htnLookup htnBorder
       exact Xb_cg_path_last hpathTn
     obtain ⟨boxM, hboxM, hpathM⟩ := X_cg_bottom_box h0 h hjGet hbordJ
     have hlastM : nb.clusterPath.getLast? = some nb.decl :=
       Xb_cg_path_last hpathM
     have h := congrArg List.getLast? htnPathEq
     rw [hlastTn, hlastM] at h
     exact Option.some.inj h
   obtain ⟨tnBot, htnBot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp htnLookup htnBorder
   have hfindNb : (componentCandidate graph comp candidate).nodes.zipIdx.find?
       (fun entry => entry.1.border == 2 && entry.1.decl == nb.decl) = some (nb, j) :=
     X_bottom_find_eq h0 h hcomp hjGet hbordJ
   have htnBotEq : tnBot = (nb, j) := by
     rw [← hdeclTn] at hfindNb
     exact Option.some.inj (htnBot.symm.trans hfindNb)
   obtain ⟨boxT, hboxT, hpathT⟩ := X_cg_group_box h0 h htGet hbordT
   obtain ⟨boxM, hboxM, hpathM⟩ := X_cg_bottom_box h0 h hjGet hbordJ
   have hpreOuter : ndT.clusterPath <+: nb.clusterPath :=
     X_cg_scope_prefix hwf hboxT hpathT hboxM hpathM hcontains
   have hpre : ndT.clusterPath <+: tn.1.clusterPath := by
     rw [htnPathEq]
     exact hpreOuter
   have hrank := Xb_nested_bottom_rank h0 h hlines hwf hframed hcomp candidate hrr
     _ t tn.2 ndT tn.1 (ndV, v) tnBot htGet hbordT htnLookup htnBorder hpre rfl
     hbotFindOuter htnBot
   have hjEq : tnBot.2 = j := congrArg Prod.snd htnBotEq
   rw [hjEq] at hrank
   have hvEq : ((ndV, v) : Node × Nat).2 = v := rfl
   rw [hvEq] at hrank
   have eV : rk run.coordinateProper.rank v = rk rr.ranks v := by
     exact Xb_prepared_rk hrr hc hranks (List.getElem?_eq_some_iff.mp hvGet).1
   have eJ : rk run.coordinateProper.rank j = rk rr.ranks j := by
     exact Xb_prepared_rk hrr hc hranks (List.getElem?_eq_some_iff.mp hjGet).1
   omega
 /-- Exact proxy span record (replay of `componentRun_proxy_interval` through
 `componentRunX_spec`). -/
 private theorem Xb_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run)
     {index : Nat} {node : ProperNode}
     (hnode : run.coordinateProper.nodes[index]? = some node)
     (hborder : node.node.border = -2 ∨ node.node.border = 2) :
     ∃ (owner : Nat) (span : FramePorts.Span),
       node.node.clusterPath.getLast? = some owner ∧
       proxySpan run.coordinateProper run.coordinateXs owner index = .ok span ∧
       run.proper.nodes[index]? =
         some { node with node := { node.node with w := span.hi - span.lo } } ∧
       0 ≤ span.hi - span.lo ∧
       RouteImpl.leftOf run.proper run.xs index = span.lo ∧
       RouteImpl.leftOf run.proper run.xs index + RouteImpl.nodeW run.proper index = span.hi := by
   obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
   have nodesEq : run.proper.nodes = routed.nodes := by
     rw [← hdrop]
     rfl
   obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
     proxyWidths_proxy_interval hproxy hnode hborder
   refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
   · simpa only [nodesEq] using outputNode
   · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
   · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right

 /-- Member rank bound by classification (exact replay of `bottomMemberRankLe`):
 synthetic members (dummies, side borders, title copies) defer to the exact
 synthetic lemmas; non-synthetic members transport through the coordinate
 record and `NodeKeys` to candidate-graph originals, which `Xb_origRankLe`
 bounds. -/
 private theorem Xb_memberRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hframed : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph)
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions}
     (hrun : componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels
       orderOptions = .ok run)
     {v t : Nat} {ndV ndT : Node}
     (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
     (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
     (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
     (hdecl : ndV.decl = ndT.decl) :
     ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
     q.1.node.clusterPath.contains
       ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
     rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
   have hnest : Xb_NestedExact exactIds := Xb_NestedExact_holds exactIds
   have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
       ndT.decl := by
     rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
   intro q hq hcontains
   have hqget : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
   obtain ⟨nvc, hnc, hborderEq, _, _⟩ := Xb_fbs hrun hqget
   obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
     X_cg_run_bundle h0 h hcomp hrun
   have hncL : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[q.2]? = some nvc := by
     rwa [← hc] at hnc
   rcases Xb_coord_lookup P (exactDecls exactIds inp) labeled hncL with
     ⟨m, hm, hmd, hb, hp, -⟩ | hside | ⟨_, _, _, _, _, hb3, _⟩
   · by_cases hqd : q.1.dummy = true
     · exact X_bottomDummyRankLe exactIds hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet
         hbordV hbordT hdecl q hq hcontains hqd
     · have hqdF : q.1.dummy = false := by simpa using hqd
       by_cases hbS : nvc.node.border = -1 ∨ nvc.node.border = 1 ∨ nvc.node.border = 3
       · have hqbS : q.1.node.border = -1 ∨ q.1.node.border = 1 ∨
             q.1.node.border = 3 := by
           rcases hbS with h | h | h
           · exact Or.inl (by rw [← hborderEq]; exact h)
           · exact Or.inr (Or.inl (by rw [← hborderEq]; exact h))
           · exact Or.inr (Or.inr (by rw [← hborderEq]; exact h))
         rcases hqbS with hb1 | hb2 | hb3q
         · exact Xb_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
             hdecl hnest q hq hcontains (Or.inl hb1)
         · exact Xb_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
             hdecl hnest q hq hcontains (Or.inr hb2)
         · exact Xb_titleRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
             hdecl hnest q hq hcontains hb3q
       · by_cases hbP : nvc.node.border = -2 ∨ nvc.node.border = 2
         · obtain ⟨owner, span, _, _, hproper, _, _⟩ := Xb_proxy_interval hrun hnc hbP
           have hqq : q.1 =
               { nvc with node := { nvc.node with w := span.hi - span.lo } } :=
             Option.some.inj (hqget.symm.trans hproper)
           have hdu : nvc.dummy = q.1.dummy := by rw [hqq]
           have hmdF : m.dummy = false := by rw [← hmd, hdu]; exact hqdF
           have hpathT : nvc.node.clusterPath = q.1.node.clusterPath := by rw [hqq]
           rcases hk q.2 m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
           · have hncN : n.clusterPath.contains ndT.decl = true := by
               rw [← hnp, ← hp hmdF, hpathT, ← hdeclT]; exact hcontains
             exact Xb_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
               hdecl hnest hn hncN
           · rw [hdT] at hmdF
             simp at hmdF
         · obtain ⟨hrecFull, -⟩ := Xb_nonproxy hrun hnc hbP
           have hqq : q.1 = nvc := Option.some.inj (hqget.symm.trans hrecFull)
           have hmdF : m.dummy = false := by rw [← hmd, ← hqq]; exact hqdF
           have hpathT : nvc.node.clusterPath = q.1.node.clusterPath := by rw [hqq]
           rcases hk q.2 m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
           · have hncN : n.clusterPath.contains ndT.decl = true := by
               rw [← hnp, ← hp hmdF, hpathT, ← hdeclT]; exact hcontains
             exact Xb_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
               hdecl hnest hn hncN
           · rw [hdT] at hmdF
             simp at hmdF
   · rcases hside.2 with hb1 | hb2
     · exact Xb_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
         hdecl hnest q hq hcontains (Or.inl (by rw [← hborderEq]; exact hb1))
     · exact Xb_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
         hdecl hnest q hq hcontains (Or.inr (by rw [← hborderEq]; exact hb2))
   · exact Xb_titleRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
       hdecl hnest q hq hcontains (by rw [← hborderEq]; exact hb3)
 /-- An exact-candidate `border = 2` node index is in bounds with a real lookup
 (copy of `bottom_marker_index`). -/
 private theorem Xb_marker_index {cg : Graph} {v : Nat}
     (hcb : (cg.nodes.getD v default).border = 2) :
     v < cg.nodes.length ∧ cg.nodes[v]? = some (cg.nodes.getD v default) := by
   by_cases hlt : v < cg.nodes.length
   · have hg : cg.nodes[v]? = some (cg.nodes.getD v default) := by
       rw [List.getD_eq_getElem?_getD]
       simp [List.getElem?_eq_getElem hlt]
     exact ⟨hlt, hg⟩
   · exfalso
     have hget : cg.nodes[v]? = none := List.getElem?_eq_none (by omega)
     rw [List.getD_eq_getElem?_getD, hget, Option.getD_none] at hcb
     have hz : (default : Node).border = 0 := rfl
     rw [hz] at hcb
     omega

 /-- An exact-candidate `border = -2` node index is in bounds with a real lookup
 (copy of `top_marker_index`). -/
 private theorem Xb_top_index {cg : Graph} {v : Nat}
     (hcb : (cg.nodes.getD v default).border = -2) :
     v < cg.nodes.length ∧ cg.nodes[v]? = some (cg.nodes.getD v default) := by
   by_cases hlt : v < cg.nodes.length
   · have hg : cg.nodes[v]? = some (cg.nodes.getD v default) := by
       rw [List.getD_eq_getElem?_getD]
       simp [List.getElem?_eq_getElem hlt]
     exact ⟨hlt, hg⟩
   · exfalso
     have hget : cg.nodes[v]? = none := List.getElem?_eq_none (by omega)
     rw [List.getD_eq_getElem?_getD, hget, Option.getD_none] at hcb
     have hz : (default : Node).border = 0 := rfl
     rw [hz] at hcb
     omega

 /-- The exact coordinate-graph record of a `border = 2` bottom marker
 (replay of `bottom_marker_coordinate_record`). -/
 private theorem Xb_marker_coord_record {P : Params} {inp : Input} {o : Options}
     {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
     {comp : List Nat} (hcomp : comp ∈ components graph)
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels orderOptions = .ok run)
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     {v : Nat} {nd : Node}
     (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
     (hgroup : nd.border = 2) :
     ∃ coord : ProperNode,
       run.coordinateProper.nodes[v]? = some coord ∧
       coord.node.border = 2 ∧ coord.dummy = false ∧
       coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
   obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
     X_cg_run_bundle h0 h hcomp hrun
   have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hrecords v nd hnode
   have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exactDecls exactIds inp)
     hrec (Or.inr hgroup) rfl
   rw [hc] at hmarker
   refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
   · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
     rw [hb, (titleF_keys _).2.1]
     exact hgroup
   · exact (clearF_keys _).1.trans (titleF_keys _).1
   · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
   · exact (clearF_keys _).2.2.2.trans
       ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))

 /-- The exact executed record of the `border = 2` bottom proxy (replay of
 `bottom_marker_proper_node`). -/
 private theorem Xb_marker_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run)
     {v : Nat} {coord : ProperNode}
     (hcoord : run.coordinateProper.nodes[v]? = some coord)
     (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
     ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
       p.node.clusterPath = coord.node.clusterPath ∧
       RouteImpl.nodeH run.proper v = 0 := by
   obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
     Xb_proxy_interval hrun hcoord (Or.inr hb)
   refine ⟨_, hproper, rfl, ?_⟩
   simp only [RouteImpl.nodeH, hproper]
   exact hcoordH

 /-- Exact original indices are covered by the proper run (replay of
 `componentRun_original_nodes_covered` through `sizeProperPortsX`). -/
 private theorem Xb_original_covered {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run) :
     ∀ i, i < cg.nodes.length → i < run.proper.nodes.length := by
   obtain ⟨ranks, p0, labeled, q, hn, hl, hcoord, _, _, hproxy, hdrop,
     _, _, _⟩ := componentRunX_spec h
   have hnlen := normalize_nodes_length_le hn
   have hllen : p0.nodes.length ≤ labeled.nodes.length := by
     by_cases hle : p0.nodes.length ≤ labeled.nodes.length
     · exact hle
     · have hi : labeled.nodes.length < p0.nodes.length := by omega
       have hmap := (Labels.addLabelNodes_metadata hl).2.2.2 labeled.nodes.length
       have hget : p0.nodes[labeled.nodes.length]? =
           some p0.nodes[labeled.nodes.length] := by simp [hi]
       simp [hget] at hmap
   let titled := titleReservations (sizeProperPortsX P exact labeled)
   obtain ⟨_, _, extra, hextra, _⟩ :=
     OrderImpl.addClusterBorders_metadata titled P.clusterBorderW
   have hclen : labeled.nodes.length ≤ run.coordinateProper.nodes.length := by
     rw [← hcoord]
     unfold coordinateGraphX materializeDummyPaths clearProxyExtents
     simp only [List.length_map]
     rw [hextra]
     dsimp only [titled, titleReservations]
     simp only [List.length_zipIdx, List.length_map, List.length_append,
       sizeProperPortsX_length]
     omega
   have hplen := (proxyWidths_rel hproxy).2.2.1
   intro i hi
   rw [← hdrop]
   change i < q.nodes.length
   omega

 /-- The exact reserved `run.top` stays nonnegative: pre-reserve tops are
 nonnegative (`rankCoordsWith_spec`, as in `fbs_run_top_nonneg`) and
 `reserveExactRanks` only adds nonnegative prefix-sum shifts. -/
 private theorem Xb_top_nonneg {P : Params} {inp : Input}
     {exactIds : List String} {graph : Graph}
     {comp : List Nat}
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
     ∀ k, 0 ≤ run.top.getD k 0 := by
   obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ := Xb_run_pre hrun
   have htopLen : top_pre.length = run.layers.length := (CoordsImpl.rankCoordsWith_length hry).2
   have hpre : ∀ k, 0 ≤ top_pre.getD k 0 := by
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
   unfold reserveExactRanks at hreserve
   obtain ⟨topNew, htopM, h1⟩ := Xb_bind_ok hreserve
   obtain ⟨ysNew, hysM, h2⟩ := Xb_bind_ok h1
   have hpair := Except.ok.inj h2
   have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
   rw [htopNew_eq] at htopM
   have hextra := Xb_extra_fold (componentCandidate graph comp candidate)
     (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
     (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0)
   have hposM : ∀ e ∈ (componentCandidate graph comp candidate).nodes.zipIdx.foldl
       (fun (acc : List Int) (q : Node × Nat) =>
         if !(exactDecls exactIds inp).contains q.1.decl then acc
         else
           let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
             (componentCandidate graph comp candidate).slot
           if sizes.isEmpty then acc
           else
             let rank := (run.coordinateProper.rank.getD q.2 0).toNat
             let reserved := max q.1.h ((sizes.length : Int) * Loops.band
               (componentCandidate graph comp candidate).slot sizes)
             let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
               (run.layers.map fun layer => layer.foldl (fun h v => max h
                 (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
             acc.set rank (max (acc.getD rank 0) needed))
       (List.replicate top_pre.length (0 : Int)), 0 ≤ e := by
     intro e he
     obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
     have h := hextra.2 i
     rw [List.getD_eq_getElem?_getD, hi] at h
     simp at h
     exact h
   have htop_eq : ∀ (r : Nat), r < top_pre.length → run.top.getD r 0 =
       top_pre.getD r 0 +
         (((componentCandidate graph comp candidate).nodes.zipIdx.foldl
           (fun (acc : List Int) (q : Node × Nat) =>
             if !(exactDecls exactIds inp).contains q.1.decl then acc
             else
               let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
                 (componentCandidate graph comp candidate).slot
               if sizes.isEmpty then acc
               else
                 let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                 let reserved := max q.1.h ((sizes.length : Int) * Loops.band
                   (componentCandidate graph comp candidate).slot sizes)
                 let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                   (run.layers.map fun layer => layer.foldl (fun h v => max h
                     (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                 acc.set rank (max (acc.getD rank 0) needed))
           (List.replicate top_pre.length (0 : Int))).foldl
           (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0 := by
     intro r hr
     have hrZ : r < (top_pre.zipIdx).length := by
       rw [List.length_zipIdx]
       exact hr
     have hzin : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
       have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
       simp [List.getElem?_zipIdx, h1]
     obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
     obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
     have hbeq := Measure.checkedI32_ok hb
     have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
     have e3 : top_pre.getD r 0 = top_pre[r] := by
       rw [List.getD_eq_getElem?_getD, h1]
       rfl
     have e4 : run.top.getD r 0 = b := by
       rw [List.getD_eq_getElem?_getD, hbr]
       rfl
     rw [e4, e3]
     exact hbeq
   intro k
   by_cases hk : k < top_pre.length
   · rw [htop_eq k hk]
     have h1 := hpre k
     have h2 : 0 ≤ (((componentCandidate graph comp candidate).nodes.zipIdx.foldl
         (fun (acc : List Int) (q : Node × Nat) =>
           if !(exactDecls exactIds inp).contains q.1.decl then acc
           else
             let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
               (componentCandidate graph comp candidate).slot
             if sizes.isEmpty then acc
             else
               let rank := (run.coordinateProper.rank.getD q.2 0).toNat
               let reserved := max q.1.h ((sizes.length : Int) * Loops.band
                 (componentCandidate graph comp candidate).slot sizes)
               let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                 (run.layers.map fun layer => layer.foldl (fun h v => max h
                   (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
               acc.set rank (max (acc.getD rank 0) needed))
         (List.replicate top_pre.length (0 : Int))).foldl
         (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD k 0 :=
       Xb_shifts_nonneg _ _ hposM rfl k
     omega
   · have hlen : run.top.length = top_pre.length := by
       obtain ⟨hlenM, _⟩ := mapM_getElem? _ _ _ htopM
       have hz : (top_pre.zipIdx).length = top_pre.length := by simp
       omega
     have hg : run.top[k]? = none := List.getElem?_eq_none_iff.mpr (by omega)
     rw [List.getD_eq_getElem?_getD, hg]
     simp
 /-- The exact bottom-proxy transport facts (replay of `bottomProxyRunFacts`):
 for an executed exact component run, the `border = 2` bottom marker keeps
 border `2` in the coordinate graph with its declaration as path last, its
 proper node lies in the title's member set, its proper height is zero, its
 routed `ys` entry is nonnegative, and both indices are live. -/
 private theorem Xb_proxyFacts {P : Params} {inp : Input} {o : Options}
     {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     {comp : List Nat} (hcomp : comp ∈ components graph)
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels orderOptions = .ok run)
     {v t : Nat}
     (hbordV : ((componentCandidate graph comp candidate).nodes.getD v default).border = 2)
     (hbordT : ((componentCandidate graph comp candidate).nodes.getD t default).border = -2)
     (hdecl : ((componentCandidate graph comp candidate).nodes.getD v default).decl =
       ((componentCandidate graph comp candidate).nodes.getD t default).decl) :
     (run.coordinateProper.nodes.getD v default).node.border = 2 ∧
     (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
       some ((componentCandidate graph comp candidate).nodes.getD v default).decl ∧
     (run.proper.nodes.getD v default).node.clusterPath.contains
       ((componentCandidate graph comp candidate).nodes.getD t default).decl = true ∧
     RouteImpl.nodeH run.proper v = 0 ∧
     0 ≤ run.ys.getD v 0 ∧
     v < run.proper.nodes.length ∧ t < run.proper.nodes.length ∧
     v < run.coordinateProper.nodes.length := by
   obtain ⟨hvLt, hvGet⟩ := Xb_marker_index hbordV
   obtain ⟨htLt, htGet⟩ := Xb_top_index hbordT
   obtain ⟨box, hbox, hpath⟩ := X_cg_bottom_box h0 h hvGet hbordV
   have hpathLast : ((componentCandidate graph comp candidate).nodes.getD v default).clusterPath.getLast? =
       some ((componentCandidate graph comp candidate).nodes.getD v default).decl := by
     rw [hpath]; simp
   have hcontainsSelf : ((componentCandidate graph comp candidate).nodes.getD v default).clusterPath.contains
       ((componentCandidate graph comp candidate).nodes.getD v default).decl = true := by
     rw [hpath]; simp
   obtain ⟨coord, hcoord, hcoordB, hcoordD, hcoordP, hcoordH⟩ :=
     Xb_marker_coord_record hcomp hrun h0 h hvGet hbordV
   obtain ⟨p, hproper, hproperP, hnodeH⟩ := Xb_marker_proper hrun hcoord hcoordB hcoordH
   have hvLen : v < run.proper.nodes.length := Xb_original_covered hrun v hvLt
   have htLen : t < run.proper.nodes.length := Xb_original_covered hrun t htLt
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, _⟩ := componentRunX_spec hrun
   have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
     rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
   have hvCoord : v < run.coordinateProper.nodes.length := by omega
   have hcoordD0 : run.coordinateProper.nodes.getD v default = coord := by
     rw [List.getD_eq_getElem?_getD, hcoord, Option.getD_some]
   subst hcoordD0
   have hproperD : run.proper.nodes.getD v default = p := by
     rw [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
   have hcontains : (run.proper.nodes.getD v default).node.clusterPath.contains
       ((componentCandidate graph comp candidate).nodes.getD t default).decl = true := by
     rw [hproperD, hproperP, hcoordP, ← hdecl]
     exact hcontainsSelf
   have hrankEq : run.proper.rank = run.coordinateProper.rank := by
     rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
   have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
   obtain ⟨lv, hly, hvIn, hrknn⟩ := hcov v hvLen
   rw [hrankEq] at hrknn
   have hrkC : rk run.coordinateProper.rank v = ((rk run.coordinateProper.rank v).toNat : Int) := by
     omega
   have hlyC : run.layers[(rk run.coordinateProper.rank v).toNat]? = some lv := by
     rw [← hrankEq]; exact hly
   have hbands := X_ReserveBands_holds exactIds hrun
   have hband := (hbands.1 _ _ _ hlyC hvIn hvCoord hrkC).1
   have htopnn := Xb_top_nonneg hrun
   have hysnn : 0 ≤ run.ys.getD v 0 := by
     have h1 := htopnn (rk run.coordinateProper.rank v).toNat
     omega
   exact ⟨hcoordB, by rw [hcoordP]; exact hpathLast, hcontains, hnodeH, hysnn,
     hvLen, htLen, hvCoord⟩
 /-- Monotone `toNat` for nonnegative ranks (copy of `rkToNat_le`). -/
 private theorem Xb_rkToNat_le {a b : Int} (ha : 0 ≤ a) (h : a ≤ b) :
     a.toNat ≤ b.toNat := by
   have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
   have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg (Int.le_trans ha h)
   have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by omega
   exact Int.ofNat_le.mp h3

 /-- The reserve shift equations: `run.top`/`run.ys` are the pre-reserve lists
 shifted per rank by the same prefix sums (the two `have`s of
 `X_ReserveBands_holds`). -/
 private theorem Xb_shift_eqs {P : Params} {inp : Input} {exactIds : List String}
     {graph : Graph} {comp : List Nat}
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
     ∃ (y_pre top_pre ys_pre : List Int),
       rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
         (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧
       proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧
       (∀ r, r < top_pre.length → run.top.getD r 0 = top_pre.getD r 0 +
         (((componentCandidate graph comp candidate).nodes.zipIdx.foldl
           (fun (acc : List Int) (q : Node × Nat) =>
             if !(exactDecls exactIds inp).contains q.1.decl then acc
             else
               let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
                 (componentCandidate graph comp candidate).slot
               if sizes.isEmpty then acc
               else
                 let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                 let reserved := max q.1.h ((sizes.length : Int) * Loops.band
                   (componentCandidate graph comp candidate).slot sizes)
                 let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                   (run.layers.map fun layer => layer.foldl (fun h v => max h
                     (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                 acc.set rank (max (acc.getD rank 0) needed))
           (List.replicate top_pre.length (0 : Int))).foldl
           (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0) ∧
       (∀ j, j < ys_pre.length → run.ys.getD j 0 = ys_pre.getD j 0 +
         (((componentCandidate graph comp candidate).nodes.zipIdx.foldl
           (fun (acc : List Int) (q : Node × Nat) =>
             if !(exactDecls exactIds inp).contains q.1.decl then acc
             else
               let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
                 (componentCandidate graph comp candidate).slot
               if sizes.isEmpty then acc
               else
                 let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                 let reserved := max q.1.h ((sizes.length : Int) * Loops.band
                   (componentCandidate graph comp candidate).slot sizes)
                 let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                   (run.layers.map fun layer => layer.foldl (fun h v => max h
                     (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                 acc.set rank (max (acc.getD rank 0) needed))
           (List.replicate top_pre.length (0 : Int))).foldl
           (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD
           ((run.coordinateProper.rank.getD j 0).toNat) 0) := by
   obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ := Xb_run_pre hrun
   refine ⟨y_pre, top_pre, ys_pre, hry, hyspre, ?_, ?_⟩
   · unfold reserveExactRanks at hreserve
     obtain ⟨topNew, htopM, h1⟩ := Xb_bind_ok hreserve
     obtain ⟨ysNew, hysM, h2⟩ := Xb_bind_ok h1
     have hpair := Except.ok.inj h2
     have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
     rw [htopNew_eq] at htopM
     intro r hr
     have hrZ : r < (top_pre.zipIdx).length := by
       rw [List.length_zipIdx]
       exact hr
     have hzin : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
       have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
       simp [List.getElem?_zipIdx, h1]
     obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
     obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
     have hbeq := Measure.checkedI32_ok hb
     have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
     have e3 : top_pre.getD r 0 = top_pre[r] := by
       rw [List.getD_eq_getElem?_getD, h1]
       rfl
     have e4 : run.top.getD r 0 = b := by
       rw [List.getD_eq_getElem?_getD, hbr]
       rfl
     rw [e4, e3]
     exact hbeq
   · unfold reserveExactRanks at hreserve
     obtain ⟨topNew, htopM, h1⟩ := Xb_bind_ok hreserve
     obtain ⟨ysNew, hysM, h2⟩ := Xb_bind_ok h1
     have hpair := Except.ok.inj h2
     have hysNew_eq : ysNew = run.ys := congrArg Prod.fst hpair
     rw [hysNew_eq] at hysM
     intro j hj
     have hjZ : j < (ys_pre.zipIdx).length := by
       rw [List.length_zipIdx]
       exact hj
     have hzin : (ys_pre.zipIdx)[j]? = some (ys_pre[j], j) := by
       have h1 : ys_pre[j]? = some ys_pre[j] := List.getElem?_eq_getElem hj
       simp [List.getElem?_zipIdx, h1]
     obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ hysM
     obtain ⟨b, hb, hbr⟩ := hidx j _ hzin
     have hbeq := Measure.checkedI32_ok hb
     have h1 : ys_pre[j]? = some ys_pre[j] := List.getElem?_eq_getElem hj
     have e3 : ys_pre.getD j 0 = ys_pre[j] := by
       rw [List.getD_eq_getElem?_getD, h1]
       rfl
     have e4 : run.ys.getD j 0 = b := by
       rw [List.getD_eq_getElem?_getD, hbr]
       rfl
     rw [e4, e3]
     exact hbeq
 /-- The exact band transfer (replay of `bottomMemberBottom_of_rank`): from a
 rank bound over all member rectangles, every member bottom edge lies at or
 below the bottom proxy's routed `ys`. The proxy itself attains the bound with
 equality (post-reserve `ys`/`top` shifts cancel at the proxy rank, via
 `Xb_shift_eqs`); lower bands transport through `X_ReserveBands_holds`. -/
 private theorem Xb_memberBottom {P : Params} {inp : Input} {exactIds : List String}
     {graph : Graph} {comp : List Nat}
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P (exactDecls exactIds inp)
       (componentCandidate graph comp candidate) labels orderOptions = .ok run)
     {v t : Nat}
     (hvLen : v < run.proper.nodes.length)
     (hcoordV : run.coordinateProper.nodes[v]? =
       some (run.coordinateProper.nodes.getD v default))
     (hbV : (run.coordinateProper.nodes.getD v default).node.border = 2)
     (hrank : ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
       q.1.node.clusterPath.contains
         ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
       rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v) :
     ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
       if q.1.node.clusterPath.contains
         ((componentCandidate graph comp candidate).nodes.getD t default).decl then
         some (Labels.rectAt run.proper run.xs run.ys q.2)
       else none),
     r.y + r.h ≤ run.ys.getD v 0 := by
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, _⟩ :=
     componentRunX_spec hrun
   have hrankEq : ∀ x, rk run.proper.rank x = rk run.coordinateProper.rank x :=
     fun x => X_proper_rank_eq_local hrun x
   have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
     rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
   have hcov :=
     (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
   obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, htopShift, hysShift⟩ := Xb_shift_eqs hrun
   have hcyLen : y_pre.length = run.coordinateProper.nodes.length :=
     (CoordsImpl.rankCoordsWith_length hry).1
   have hysLen : ys_pre.length = run.coordinateProper.nodes.length := by
     rw [← hyspre]
     unfold proxyYs
     rw [List.length_map, List.length_zipIdx]
     exact hcyLen
   have hvC : v < run.coordinateProper.nodes.length :=
     (List.getElem?_eq_some_iff.mp hcoordV).1
   have hvPre : v < y_pre.length := by omega
   have hvYs : v < ys_pre.length := by omega
   have hpg := proxyYs_getD run.coordinateProper run.layers top_pre y_pre hcoordV hvPre
   rw [hyspre] at hpg
   have hbeqF : ((run.coordinateProper.nodes.getD v default).node.border == -2) =
       false := by rw [hbV]; simp
   have hbeqT : ((run.coordinateProper.nodes.getD v default).node.border == 2) =
       true := by rw [hbV]; simp
   have n1 : ¬(((run.coordinateProper.nodes.getD v default).node.border == -2) = true) := by
     rw [hbeqF]; decide
   have p2 : ((run.coordinateProper.nodes.getD v default).node.border == 2) = true := by
     rw [hbeqT]
   rw [ite_eq_right n1, ite_eq_left p2] at hpg
   have hlayV0 := hcov v hvLen
   rw [hrankEq v] at hlayV0
   obtain ⟨lv, hlyV, -, -⟩ := hlayV0
   have hrVlt : (rk run.coordinateProper.rank v).toNat < top_pre.length := by
     have h1 := (List.getElem?_eq_some_iff.mp hlyV).1
     have h2 : top_pre.length = run.layers.length :=
       (CoordsImpl.rankCoordsWith_length hry).2
     omega
   have hrkv : (run.coordinateProper.rank.getD v 0).toNat =
       (rk run.coordinateProper.rank v).toNat := rfl
   have htopV := htopShift _ hrVlt
   have hysVeq := hysShift v hvYs
   rw [hrkv] at hysVeq
   have hYsV : run.ys.getD v 0 = run.top.getD (rk run.coordinateProper.rank v).toNat 0 +
       CoordsImpl.layerHeight run.coordinateProper
         (run.layers.getD (rk run.coordinateProper.rank v).toNat []) := by
     rw [hysVeq, htopV, hpg]
     omega
   have hbands := X_ReserveBands_holds exactIds hrun
   intro r hr
   obtain ⟨q, hq, hqr⟩ := List.mem_filterMap.mp hr
   have hc : q.1.node.clusterPath.contains
       ((componentCandidate graph comp candidate).nodes.getD t default).decl = true := by
     by_cases h : q.1.node.clusterPath.contains
         ((componentCandidate graph comp candidate).nodes.getD t default).decl = true
     · exact h
     · have hf : q.1.node.clusterPath.contains
           ((componentCandidate graph comp candidate).nodes.getD t default).decl = false :=
         Bool.eq_false_iff.mpr h
       rw [hf] at hqr
       simp at hqr
   have hqr' : Labels.rectAt run.proper run.xs run.ys q.2 = r := by
     rw [hc] at hqr
     simpa using hqr
   have hlen : q.2 < run.proper.nodes.length :=
     (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)).1
   have hvCq : q.2 < run.coordinateProper.nodes.length := by omega
   have hlayQ0 := hcov q.2 hlen
   rw [hrankEq q.2] at hlayQ0
   obtain ⟨lq, hlyQ, hvInQ, hrknnQ⟩ := hlayQ0
   have hrkQnn : 0 ≤ rk run.coordinateProper.rank q.2 := hrknnQ
   have hrkQ : rk run.coordinateProper.rank q.2 =
       ((rk run.coordinateProper.rank q.2).toNat : Int) := by omega
   have hband := (hbands.1 _ _ _ hlyQ hvInQ hvCq hrkQ).2
   have hrk := hrank q hq hc
   have hqq := Xb_rkToNat_le hrkQnn hrk
   have hlyQD : run.layers.getD (rk run.coordinateProper.rank q.2).toNat [] = lq := by
     rw [List.getD_eq_getElem?_getD, hlyQ]
     rfl
   have hle : run.top.getD (rk run.coordinateProper.rank q.2).toNat 0 +
       CoordsImpl.layerHeight run.coordinateProper lq ≤ run.ys.getD v 0 := by
     by_cases heq : (rk run.coordinateProper.rank q.2).toNat =
         (rk run.coordinateProper.rank v).toNat
     · have htopEq : run.top.getD (rk run.coordinateProper.rank q.2).toNat 0 =
           run.top.getD (rk run.coordinateProper.rank v).toNat 0 := by rw [heq]
       have hlayerEq : CoordsImpl.layerHeight run.coordinateProper lq =
           CoordsImpl.layerHeight run.coordinateProper
             (run.layers.getD (rk run.coordinateProper.rank v).toNat []) := by
         rw [← hlyQD, heq]
       rw [htopEq, hlayerEq, hYsV]
       exact Int.le_refl _
     · have hlt : (rk run.coordinateProper.rank q.2).toNat <
           (rk run.coordinateProper.rank v).toNat := by omega
       have hdisj := hbands.2 _ _ _ _ hlt hlyQ hlyV
       have hnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lv :=
         CoordsImpl.layerHeight_nonneg _ _
       have hlyVD : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = lv := by
         rw [List.getD_eq_getElem?_getD, hlyV]
         rfl
       rw [hYsV, hlyVD]
       omega
   rw [← hqr']
   have hqget : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
   obtain ⟨nvcQ, hncQ, _, hHEqQ, _⟩ := Xb_fbs hrun hqget
   have hnodeHq : RouteImpl.nodeH run.proper q.2 = CoordsImpl.nodeH run.coordinateProper q.2 := by
     have e1 : RouteImpl.nodeH run.proper q.2 = q.1.node.h := by simp only [RouteImpl.nodeH, hqget]
     have e2 : CoordsImpl.nodeH run.coordinateProper q.2 = nvcQ.node.h := by
       simp only [CoordsImpl.nodeH, hncQ]
     rw [e1, e2, hHEqQ]
   show RouteImpl.yAt run.ys q.2 + RouteImpl.nodeH run.proper q.2 ≤ _
   rw [hnodeHq]
   exact Int.le_trans hband hle
 /-- The horizontal span of an exact bottom proxy's box lies inside its group
 frame's horizontal span (replay of `componentRun_group_bottom_frame_x_contains_port`). -/
 private theorem Xb_x_contains {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run)
     {v t : Nat}
     (hnode : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
     (hborder : (run.coordinateProper.nodes.getD v default).node.border = 2)
     (hcborderT : (cg.nodes.getD t default).border = -2)
     (hdecl : (cg.nodes.getD v default).decl = (cg.nodes.getD t default).decl)
     (howner : (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
       some (cg.nodes.getD v default).decl)
     (px : Int)
     (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
       px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
         (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
     (frameRect P cg run t).x ≤ px ∧
       px ≤ (frameRect P cg run t).x + (frameRect P cg run t).w := by
   obtain ⟨owner, span, ownerEq, hspan, _, _, hleft, hright⟩ :=
     Xb_proxy_interval hrun hnode (Or.inr hborder)
   have hownerEq : owner = (cg.nodes.getD t default).decl := by
     have h := Option.some.inj (ownerEq.symm.trans howner)
     rw [hdecl] at h
     exact h
   obtain ⟨li, ri, left, right, hleftGet, hrightGet, hleftBorder, hrightBorder,
     hleftOwner, hrightOwner, _, _, hlo, hhi⟩ := proxySpan_endpoint_sources hspan
   have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
     rcases hleftBorder with h | h <;> omega
   have hrightNotProxy : ¬(right.node.border = -2 ∨ right.node.border = 2) := by
     rcases hrightBorder with h | h <;> omega
   obtain ⟨hleftProper, hleftXs⟩ := Xb_nonproxy hrun hleftGet hleftNotProxy
   obtain ⟨hrightProper, hrightXs⟩ := Xb_nonproxy hrun hrightGet hrightNotProxy
   have hleftOwner' : left.node.clusterPath.getLast? =
       some (cg.nodes.getD t default).decl := by rw [hleftOwner, hownerEq]
   have hrightOwner' : right.node.clusterPath.getLast? =
       some (cg.nodes.getD t default).decl := by rw [hrightOwner, hownerEq]
   have hleftRect : Labels.rectAt run.proper run.xs run.ys li ∈
       (run.proper.nodes.zipIdx.filterMap fun q =>
         if (q.1.node.border == -1 || q.1.node.border == 1) &&
             q.1.node.clusterPath.getLast? == some (cg.nodes.getD t default).decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) := by
     apply List.mem_filterMap.mpr
     refine ⟨(left, li), List.mem_zipIdx_iff_getElem?.mpr hleftProper, ?_⟩
     rcases hleftBorder with h | h
     · simp [h, hleftOwner']
     · simp [h, hleftOwner']
   have hrightRect : Labels.rectAt run.proper run.xs run.ys ri ∈
       (run.proper.nodes.zipIdx.filterMap fun q =>
         if (q.1.node.border == -1 || q.1.node.border == 1) &&
             q.1.node.clusterPath.getLast? == some (cg.nodes.getD t default).decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) := by
     apply List.mem_filterMap.mpr
     refine ⟨(right, ri), List.mem_zipIdx_iff_getElem?.mpr hrightProper, ?_⟩
     rcases hrightBorder with h | h
     · simp [h, hrightOwner']
     · simp [h, hrightOwner']
   have hleftLo : (Labels.rectAt run.proper run.xs run.ys li).x = span.lo := by
     have hw : RouteImpl.nodeW run.proper li = left.node.w := by
       simp only [RouteImpl.nodeW, hleftProper]
     show run.xs.getD li 0 - Int.fdiv (RouteImpl.nodeW run.proper li) 2 = span.lo
     rw [hleftXs, hlo, hw]
   have hrightHi : (Labels.rectAt run.proper run.xs run.ys ri).x +
       (Labels.rectAt run.proper run.xs run.ys ri).w = span.hi := by
     have hw : RouteImpl.nodeW run.proper ri = right.node.w := by
       simp only [RouteImpl.nodeW, hrightProper]
     show run.xs.getD ri 0 - Int.fdiv (RouteImpl.nodeW run.proper ri) 2 +
       RouteImpl.nodeW run.proper ri = span.hi
     rw [hrightXs, hhi, hw]
   have hminX := boundsOf_minX_le_rect_x _ [] _ hleftRect
   have hrightBound := rect_right_le_boundsOf_right _ [] _ hrightRect
   have hboxX : (RouteImpl.boxRect run.proper run.xs run.ys v).x = span.lo := by
     show RouteImpl.leftOf run.proper run.xs v = span.lo
     exact hleft
   have hboxW : (RouteImpl.boxRect run.proper run.xs run.ys v).x +
       (RouteImpl.boxRect run.proper run.xs run.ys v).w = span.hi := by
     show RouteImpl.leftOf run.proper run.xs v +
       RouteImpl.nodeW run.proper v = span.hi
     exact hright
   simp only [frameRect, hcborderT, show ((-2 : Int) != -2) = false from rfl,
     Bool.false_eq_true, ↓reduceIte]
   constructor <;> omega

 /-- An exact bottom proxy's port point lies on its group frame boundary
 (replay of `componentRun_group_bottom_frame_boundary`). -/
 private theorem Xb_frameBoundary {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run)
     {v t : Nat}
     (hnode : run.coordinateProper.nodes[v]? = some (run.coordinateProper.nodes.getD v default))
     (hborder : (run.coordinateProper.nodes.getD v default).node.border = 2)
     (hcborderT : (cg.nodes.getD t default).border = -2)
     (hdecl : (cg.nodes.getD v default).decl = (cg.nodes.getD t default).decl)
     (howner : (run.coordinateProper.nodes.getD v default).node.clusterPath.getLast? =
       some (cg.nodes.getD v default).decl)
     (ht : t < run.proper.nodes.length)
     (hmem : Labels.rectAt run.proper run.xs run.ys v ∈
       (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains (cg.nodes.getD t default).decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none))
     (hYrect : (Labels.rectAt run.proper run.xs run.ys v).y +
       (Labels.rectAt run.proper run.xs run.ys v).h = run.ys.getD v 0)
     (hall : ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains (cg.nodes.getD t default).decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none), r.y + r.h ≤ run.ys.getD v 0)
     (hzero : 0 ≤ run.ys.getD v 0)
     (px : Int)
     (hpx : (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
       px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
         (RouteImpl.boxRect run.proper run.xs run.ys v).w) :
     Validator.onBoundary ⟨px, run.ys.getD v 0⟩ (frameRect P cg run t) := by
   have hx := Xb_x_contains hrun hnode hborder hcborderT hdecl howner px hpx
   have hy := frameRect_bottom_eq_of_members (P := P) (t := t) (Y := run.ys.getD v 0)
     hcborderT hmem hYrect hzero hall
   obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _⟩ := componentRunX_spec hrun
   have hdims := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.1
   have hshape : ProperDimsNonneg run.proper := by
     intro i nd hget
     have hi : i < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hget).1
     have hw := hdims i hi
     have hnd : RouteImpl.nodeW run.proper i = nd.node.w ∧
         RouteImpl.nodeH run.proper i = nd.node.h := by
       simp only [RouteImpl.nodeW, RouteImpl.nodeH, hget]
       trivial
     omega
   have hdim := frameRect_dims_nonneg P cg run t hshape ht
   simp only [Validator.onBoundary]
   rw [hy]
   refine ⟨hx.1, hx.2, ?_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
   · omega
   · omega

 /-- The exact bottom-boundary fact (exact counterpart of
 `groupBottomBoundaryFacts_executed`): a route port of an executed exact
 `border = 2` bottom marker lies on the frame of its paired `border = -2` top
 marker. Rank bounds come from `Xb_memberRankLe` (which discharges the former
 `Xb_NestedExact` residual via `Xb_NestedExact_holds`); geometry closes through
 `Xb_proxyFacts`, `Xb_memberBottom`, and `Xb_frameBoundary`. -/
 theorem x_bottomBoundary_holds (exactIds : List String) : X_BottomBoundary exactIds := by
   intro P inp o lines graph0 graph measured h0 h hlines hwf hframed comp hcomp candidate run
     labels orderOptions hrun v t px hbordV hbordT hdecl hpx
   obtain ⟨hvLt, hvGet⟩ := Xb_marker_index hbordV
   obtain ⟨htLt, htGet⟩ := Xb_top_index hbordT
   have hR := Xb_proxyFacts h0 h hcomp hrun hbordV hbordT hdecl
   obtain ⟨hcoordB, howner, hcontains, hHzero, hYnonneg, hvLen, htLen, hvCoord⟩ := hR
   have hrank :=
     Xb_memberRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
   have hgetV : run.proper.nodes[v]? = some (run.proper.nodes.getD v default) := by
     simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvLen]
   have hnode : run.coordinateProper.nodes[v]? =
       some (run.coordinateProper.nodes.getD v default) := by
     simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvCoord]
   have hAll := Xb_memberBottom hrun hvLen hnode hcoordB hrank
   have hq0 : (run.proper.nodes.getD v default, v) ∈ run.proper.nodes.zipIdx :=
     List.mem_zipIdx_iff_getElem?.mpr hgetV
   have hmem : Labels.rectAt run.proper run.xs run.ys v ∈
       (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains
             ((componentCandidate graph comp candidate).nodes.getD t default).decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) := by
     apply List.mem_filterMap.mpr
     refine ⟨(run.proper.nodes.getD v default, v), hq0, ?_⟩
     rw [hcontains]
     simp
   have hYrect : (Labels.rectAt run.proper run.xs run.ys v).y +
       (Labels.rectAt run.proper run.xs run.ys v).h = run.ys.getD v 0 := by
     have heq := Elegant.Layered.rectAt_eq_box run.proper run.xs run.ys v
     rw [heq]
     show RouteImpl.yAt run.ys v + RouteImpl.nodeH run.proper v = run.ys.getD v 0
     rw [hHzero]
     show run.ys.getD v 0 + 0 = run.ys.getD v 0
     omega
   exact Xb_frameBoundary hrun hnode hcoordB hbordT hdecl howner htLen hmem hYrect hAll
     hYnonneg px hpx

 end PipelineImpl

end Layered
end Elegant

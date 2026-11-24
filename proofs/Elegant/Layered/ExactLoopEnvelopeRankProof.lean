import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactFlatC2

set_option autoImplicit false

open Elegant Layered

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Other-rank half of the loop-envelope miss: the extended footprint of a
self-loop edge misses every in-scope real box whose rank differs from the
owner rank. Same binders as `X_LoopEnvelopeMiss` plus the rank-differ premise. -/
def XLEM_OtherRankMiss (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (rk run.coordinateProper.rank v).toNat ≠
      (rk run.coordinateProper.rank e.tail).toNat →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Residual footprint-below fact for plain owners: the extended footprint of
a self-loop on a non-group frame starts at or below its owner band start, and
ends above the start of every higher rank band. Strictly narrower than the
target: one vertical statement about the footprint against rank tops, no
statement about any other box. Group owners are excluded: on group self-loops
(`grpself` probes) member boxes in higher ranks push the footprint bottom past
higher band starts (`belowAll=false`), so the vertical route cannot cover them.
True on all plain-owner probes (`ExactLoopEnvelopeRankTProbe`: 216 exact-owner
checks with all `hasLayer`, `tailIn`, `covTop`, `belowAll`, plus non-exact
plain-owner checks with `covTop`, `belowAll`, and empty other-rank `bad`). -/
def XLEM_FootBelow (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    (cg.nodes.getD e.tail default).border ≠ -2 →
    ∃ lo : List Nat,
      run.layers[(rk run.coordinateProper.rank e.tail).toNat]? = some lo ∧
      run.top.getD (rk run.coordinateProper.rank e.tail).toNat 0 ≤
        (loopFootprintExt cg run execution.measured e.tail).y ∧
      ∀ (rv : Nat) (ll : List Nat),
        (rk run.coordinateProper.rank e.tail).toNat < rv →
        run.layers[rv]? = some ll →
        (loopFootprintExt cg run execution.measured e.tail).y +
          (loopFootprintExt cg run execution.measured e.tail).h ≤
          run.top.getD rv 0
/-- Loop need of one exact candidate node: the amount by which its loop band
stack exceeds its rank height. Shared with `reserveExactRanks`. -/
private def xlemRank_needed (cg : Graph) (labels : List MeasuredLabel) (p : Proper)
    (ys_pre top_pre heights : List Int) (q : Node × Nat) : Int :=
  ys_pre.getD q.2 0 +
    max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
      Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
    top_pre.getD (p.rank.getD q.2 0).toNat 0 -
    heights.getD (p.rank.getD q.2 0).toNat 0

/-- One reserve fold step: exact loop owners max their need into their rank. -/
private def xlemRank_extra_step (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (acc : List Int) (q : Node × Nat) : List Int :=
  if !exact.contains q.1.decl then acc
  else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
  else acc.set (p.rank.getD q.2 0).toNat
    (max (acc.getD (p.rank.getD q.2 0).toNat 0)
      (xlemRank_needed cg labels p ys_pre top_pre heights q))

private theorem xlemRank_getD_set_max_ge (acc : List Int) {i j : Nat} {a : Int} :
    acc.getD j 0 ≤ (acc.set i (max (acc.getD i 0) a)).getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < acc.length
    · rw [ite_eq_left rfl, ite_eq_left hi, Option.getD_some]
      simp only [← List.getD_eq_getElem?_getD]
      exact Int.le_max_left _ _
    · have hn2 : acc[i]? = none := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hi)
      rw [ite_eq_left rfl, ite_eq_right hi, hn2, Option.getD_none]
      exact Int.le_refl _
  · rw [ite_eq_right hij]
    exact Int.le_refl _
private theorem xlemRank_extra_step_length (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (acc : List Int) (q : Node × Nat) :
    (xlemRank_extra_step cg exact labels p ys_pre top_pre heights acc q).length =
      acc.length := by
  unfold xlemRank_extra_step
  split
  · rfl
  · split
    · rfl
    · exact List.length_set

private theorem xlemRank_extra_step_ge (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (acc : List Int) (q : Node × Nat) :
    ∀ j, acc.getD j 0 ≤
      (xlemRank_extra_step cg exact labels p ys_pre top_pre heights acc q).getD j 0 := by
  intro j
  unfold xlemRank_extra_step
  split
  · exact Int.le_refl _
  · split
    · exact Int.le_refl _
    · exact xlemRank_getD_set_max_ge acc

private theorem xlemRank_extra_fold_covers (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (done rest : List (Node × Nat)) (acc : List Int)
    (hlen : acc.length = top_pre.length)
    (hacc : ∀ q ∈ done, exact.contains q.1.decl →
      ¬ (loopSizes cg.edges labels q.2 cg.slot).isEmpty →
      (p.rank.getD q.2 0).toNat < top_pre.length →
      ys_pre.getD q.2 0 +
        max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
          Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
        top_pre.getD (p.rank.getD q.2 0).toNat 0 -
        heights.getD (p.rank.getD q.2 0).toNat 0 ≤
        acc.getD (p.rank.getD q.2 0).toNat 0) :
    ∀ q ∈ done ++ rest, exact.contains q.1.decl →
      ¬ (loopSizes cg.edges labels q.2 cg.slot).isEmpty →
      (p.rank.getD q.2 0).toNat < top_pre.length →
      ys_pre.getD q.2 0 +
        max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
          Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
        top_pre.getD (p.rank.getD q.2 0).toNat 0 -
        heights.getD (p.rank.getD q.2 0).toNat 0 ≤
        (rest.foldl
          (xlemRank_extra_step cg exact labels p ys_pre top_pre heights)
          acc).getD (p.rank.getD q.2 0).toNat 0 := by
  induction rest generalizing acc done with
  | nil =>
    intro q hmem hex hne hlt
    simp only [List.foldl_nil]
    rcases List.mem_append.mp hmem with h | h
    · exact hacc q h hex hne hlt
    · simp at h
  | cons q' rest ih =>
    have heq : (done ++ [q']) ++ rest = done ++ (q' :: rest) :=
      List.append_assoc done [q'] rest
    intro q hmem hex hne hlt
    rw [List.foldl_cons]
    have hmem2 : q ∈ (done ++ [q']) ++ rest := by rw [heq]; exact hmem
    refine ih (done ++ [q'])
      (xlemRank_extra_step cg exact labels p ys_pre top_pre heights acc q') ?_ ?_
      _ hmem2 hex hne hlt
    · rw [xlemRank_extra_step_length _ _ _ _ _ _ _ _ _]; exact hlen
    · intro q'' hmem'' hex'' hne'' hlt''
      rcases List.mem_append.mp hmem'' with h | h
      · calc ys_pre.getD q''.2 0 +
              max q''.1.h (((loopSizes cg.edges labels q''.2 cg.slot).length : Int) *
                Loops.band cg.slot (loopSizes cg.edges labels q''.2 cg.slot)) -
              top_pre.getD (p.rank.getD q''.2 0).toNat 0 -
              heights.getD (p.rank.getD q''.2 0).toNat 0
            ≤ acc.getD (p.rank.getD q''.2 0).toNat 0 :=
              hacc q'' h hex'' hne'' hlt''
          _ ≤ (xlemRank_extra_step cg exact labels p ys_pre top_pre heights acc
              q').getD (p.rank.getD q''.2 0).toNat 0 :=
            xlemRank_extra_step_ge cg exact labels p ys_pre top_pre heights acc q' _
      · obtain rfl : q' = q'' := (List.mem_singleton.mp h).symm
        have hset : (acc.set (p.rank.getD q'.2 0).toNat
            (max (acc.getD (p.rank.getD q'.2 0).toNat 0)
              (xlemRank_needed cg labels p ys_pre top_pre heights q'))).getD
              (p.rank.getD q'.2 0).toNat 0 =
            max (acc.getD (p.rank.getD q'.2 0).toNat 0)
              (xlemRank_needed cg labels p ys_pre top_pre heights q') := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_set_self (by omega : (p.rank.getD q'.2 0).toNat < acc.length),
            Option.getD_some]
        have hstep : xlemRank_extra_step cg exact labels p ys_pre top_pre heights acc q' =
            acc.set (p.rank.getD q'.2 0).toNat
              (max (acc.getD (p.rank.getD q'.2 0).toNat 0)
                (xlemRank_needed cg labels p ys_pre top_pre heights q')) := by
          unfold xlemRank_extra_step
          by_cases h1 : (!exact.contains q'.1.decl) = true
          · exact absurd h1 (by simpa using hex'')
          · rw [ite_eq_right h1]
            by_cases h2 : (loopSizes cg.edges labels q'.2 cg.slot).isEmpty = true
            · exact absurd h2 hne''
            · rw [ite_eq_right h2]
        rw [hstep, hset]
        exact Int.le_max_right _ _

private def xlemRank_sums (s : Int) : List Int → List Int
  | [] => []
  | e :: es => s :: xlemRank_sums (s + e) es

private theorem xlemRank_sums_length (s : Int) (l : List Int) :
    (xlemRank_sums s l).length = l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons e es ih => simp only [xlemRank_sums, List.length_cons, ih]

private theorem xlemRank_fold_sums (l : List Int) (s : Int) (out : List Int) :
    (l.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2 =
      out ++ xlemRank_sums s l := by
  induction l generalizing s out with
  | nil => simp only [List.foldl_nil, xlemRank_sums, List.append_nil]
  | cons e es ih =>
    simp only [List.foldl_cons, xlemRank_sums]
    rw [ih]
    simp [List.append_assoc]

private theorem xlemRank_sums_getD (l : List Int) (s : Int) (r : Nat)
    (hr : r < l.length) :
    (xlemRank_sums s l).getD r 0 = s + ((l.take r).sum) := by
  induction l generalizing s r with
  | nil => simp at hr
  | cons e es ih =>
    cases r with
    | zero => simp [xlemRank_sums]
    | succ r =>
      simp only [xlemRank_sums, List.getD_cons_succ]
      have hlen : (e :: es).length = es.length + 1 := rfl
      have hr' : r < es.length := by omega
      rw [ih _ _ hr']
      simp [List.take_succ_cons, List.sum_cons]
      omega
private theorem xlemRank_sum_nonneg (l : List Int) (h : ∀ i, 0 ≤ l.getD i 0) :
    0 ≤ l.sum := by
  induction l with
  | nil => exact Int.le_refl _
  | cons a as ih =>
    rw [List.sum_cons]
    exact Int.add_nonneg (h 0) (ih (fun i => h (i + 1)))

private theorem xlemRank_sum_ge_getD_zero (l : List Int) (h : ∀ i, 0 ≤ l.getD i 0) :
    l.getD 0 0 ≤ l.sum := by
  cases l with
  | nil => exact Int.le_refl _
  | cons a as =>
    rw [List.sum_cons]
    have htail : 0 ≤ as.sum := xlemRank_sum_nonneg as (fun i => h (i + 1))
    have ha : (a :: as).getD 0 0 = a := rfl
    omega

private theorem xlemRank_rest_getD (extra : List Int) (ro rv i : Nat)
    (hlt : ro + i < rv) :
    (((extra.take rv).drop ro).getD i 0) = extra.getD (ro + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take,
    ite_eq_left hlt, ← List.getD_eq_getElem?_getD]

private theorem xlemRank_shifts_diff_ge (extra shifts : List Int)
    (hpref : shifts =
      (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2)
    (hnn : ∀ i, 0 ≤ extra.getD i 0)
    {ro rv : Nat} (hlt : ro < rv) (hrv : rv < shifts.length) :
    shifts.getD ro 0 + extra.getD ro 0 ≤ shifts.getD rv 0 := by
  have hshifts : shifts = xlemRank_sums 0 extra := by
    rw [hpref, xlemRank_fold_sums]
    simp
  have hlen : shifts.length = extra.length := by
    rw [hshifts, xlemRank_sums_length]
  have hro : ro < extra.length := by omega
  have hrv' : rv < extra.length := by omega
  rw [hshifts, xlemRank_sums_getD _ _ _ hro, xlemRank_sums_getD _ _ _ hrv']
  have htake_ro : ((extra.take rv).take ro) = extra.take ro := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
  have hsplit : extra.take rv = (extra.take ro) ++ ((extra.take rv).drop ro) := by
    rw [← htake_ro]
    exact (List.take_append_drop ro (extra.take rv)).symm
  have hjoin : (extra.take ro) ++ ((extra.take rv).drop ro) = extra.take rv :=
    hsplit.symm
  have hsum : ((extra.take rv).sum) = ((extra.take ro).sum) +
      (((extra.take rv).drop ro).sum) := by
    have h2 : (((extra.take ro) ++ ((extra.take rv).drop ro)).sum) =
        ((extra.take ro).sum) + (((extra.take rv).drop ro).sum) := List.sum_append
    rwa [← hsplit] at h2
  have hrest_nn : ∀ i, 0 ≤ (((extra.take rv).drop ro).getD i 0) := by
    intro i
    by_cases h : ro + i < rv
    · rw [xlemRank_rest_getD _ _ _ _ h]
      exact hnn _
    · have hL : (((extra.take rv).drop ro).length) ≤ i := by
        rw [List.length_drop, List.length_take]
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hL]
      simp
  have hge : (((extra.take rv).drop ro).getD 0 0) ≤ (((extra.take rv).drop ro).sum) :=
    xlemRank_sum_ge_getD_zero _ hrest_nn
  have hhead : (((extra.take rv).drop ro).getD 0 0) = extra.getD ro 0 := by
    rw [xlemRank_rest_getD _ _ _ _ (by omega : ro + 0 < rv)]
    congr 1
  omega

private theorem xlemRank_frame_plain (P : Params) (cg : Graph) (run : Run) (tail : Nat)
    (hb : (cg.nodes.getD tail default).border ≠ -2)
    {nd : ProperNode} (hq : run.proper.nodes[tail]? = some nd) :
    (frameRect P cg run tail).y = run.ys.getD tail 0 ∧
      (frameRect P cg run tail).h = nd.node.h := by
  have hget : run.proper.nodes.getD tail default = nd := by
    simp only [List.getD_eq_getElem?_getD, hq, Option.getD_some]
  have hfr : frameRect P cg run tail = nodeRect cg run tail := by
    unfold frameRect
    rw [ite_eq_left (by simpa using hb)]
  constructor
  · rw [hfr]
    rfl
  · rw [hfr]
    show (run.proper.nodes.getD tail default).node.h = nd.node.h
    rw [hget]

private theorem xlemRank_ys_pre_length (run : Run)
    (y_pre top_pre ys_pre : List Int)
    (hlen : y_pre.length = run.coordinateProper.nodes.length)
    (hyspre : proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre) :
    ys_pre.length = run.coordinateProper.nodes.length := by
  rw [← hyspre]
  unfold proxyYs
  simp only [List.length_map, List.length_zipIdx]
  exact hlen
private theorem xlemRank_heights_getD (p : Proper) (layers : List (List Nat))
    (l : List Nat) (r : Nat) (hly : layers[r]? = some l) :
    ((layers.map fun layer =>
      layer.foldl (fun h v => max h (RouteImpl.nodeH p v)) 0).getD r 0) =
      CoordsImpl.layerHeight p l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hly, Option.map_some,
    Option.getD_some]
  rfl

private theorem xlemRank_extra_nonneg (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (rest : List (Node × Nat)) (acc : List Int)
    (hacc : ∀ j, 0 ≤ acc.getD j 0) :
    ∀ j, 0 ≤ ((rest.foldl
      (xlemRank_extra_step cg exact labels p ys_pre top_pre heights) acc).getD j 0) := by
  induction rest generalizing acc with
  | nil => simpa only [List.foldl_nil] using hacc
  | cons q rest ih =>
    intro j
    rw [List.foldl_cons]
    exact ih _ (fun i => Int.le_trans (hacc i)
      (xlemRank_extra_step_ge cg exact labels p ys_pre top_pre heights acc q i)) j


private theorem xlemRank_shift_top_ys (exactIds : List String) (inp : Input)
    (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    {top_pre ys_pre : List Int}
    (hres : reserveExactRanks cg (exactDecls exactIds inp) labels run.coordinateProper
      run.layers ys_pre top_pre = .ok (run.ys, run.top)) :
    let extra := cg.nodes.zipIdx.foldl
      (xlemRank_extra_step cg (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
        (run.layers.map fun layer =>
          layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
      (List.replicate top_pre.length 0);
    let shifts := (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
      (0, ([] : List Int))).2;
    (∀ r, r < top_pre.length → run.top.getD r 0 = top_pre.getD r 0 + shifts.getD r 0) ∧
    (∀ j, j < ys_pre.length →
      run.ys.getD j 0 = ys_pre.getD j 0 +
        shifts.getD ((run.coordinateProper.rank.getD j 0).toNat) 0) ∧
    shifts = (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
      (0, ([] : List Int))).2 := by
  unfold reserveExactRanks at hres
  obtain ⟨topNew, htopM, h1⟩ := bind_ok hres
  obtain ⟨ysNew, hysM, h2⟩ := bind_ok h1
  have hpair : (ysNew, topNew) = (run.ys, run.top) := Except.ok.inj h2
  have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
  have hysNew_eq : ysNew = run.ys := congrArg Prod.fst hpair
  rw [htopNew_eq] at htopM
  rw [hysNew_eq] at hysM
  refine ⟨?_, ?_, rfl⟩
  · intro r hr
    have hrZ : r < (top_pre.zipIdx).length := by
      rw [List.length_zipIdx]
      exact hr
    have hzin : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
      have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
      simp [List.getElem?_zipIdx, h1]
    obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
    obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
    have hbeq : b = top_pre[r] + ((((cg.nodes.zipIdx.foldl (fun acc q =>
      if !(exactDecls exactIds inp).contains q.1.decl then acc
      else
        let sizes := loopSizes cg.edges labels q.2 cg.slot
        if sizes.isEmpty then acc
        else
          let rank := (run.coordinateProper.rank.getD q.2 0).toNat
          let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
          let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
            (run.layers.map fun layer =>
              layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
          acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top_pre.length (0 : Int))).foldl
      (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD r 0) :=
      Measure.checkedI32_ok hb
    have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
    have e3 : top_pre.getD r 0 = top_pre[r] := by
      rw [List.getD_eq_getElem?_getD, h1]
      rfl
    have e4 : run.top.getD r 0 = b := by
      rw [List.getD_eq_getElem?_getD, hbr]
      rfl
    rw [e4, e3]
    exact hbeq

  · intro j hj
    have hjZ : j < (ys_pre.zipIdx).length := by
      rw [List.length_zipIdx]
      exact hj
    have hzin : (ys_pre.zipIdx)[j]? = some (ys_pre[j], j) := by
      have h1 : ys_pre[j]? = some ys_pre[j] := List.getElem?_eq_getElem hj
      simp [List.getElem?_zipIdx, h1]
    obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ hysM
    obtain ⟨b, hb, hbr⟩ := hidx j _ hzin
    have hbeq : b = ys_pre[j] + ((((cg.nodes.zipIdx.foldl (fun acc q =>
      if !(exactDecls exactIds inp).contains q.1.decl then acc
      else
        let sizes := loopSizes cg.edges labels q.2 cg.slot
        if sizes.isEmpty then acc
        else
          let rank := (run.coordinateProper.rank.getD q.2 0).toNat
          let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
          let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
            (run.layers.map fun layer =>
              layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
          acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top_pre.length (0 : Int))).foldl
      (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD
        ((run.coordinateProper.rank.getD j 0).toNat) 0) :=
      Measure.checkedI32_ok hb
    have h1 : ys_pre[j]? = some ys_pre[j] := List.getElem?_eq_getElem hj
    have e3 : ys_pre.getD j 0 = ys_pre[j] := by
      rw [List.getD_eq_getElem?_getD, h1]
      rfl
    have e4 : run.ys.getD j 0 = b := by
      rw [List.getD_eq_getElem?_getD, hbr]
      rfl
    rw [e4, e3]
    exact hbeq
/-- Single narrow residual for the other-rank half. Two clauses, each strictly
narrower than the target: (i) a plain non-exact loop owner carries its frame
record and its frame covers the loop band stack; (ii) a group-frame loop owner
misses every other-rank real box given well-formed input and framed parents.
Clause (i) holds on the non-exact probes (`sibself`: `resv`, `covTop`,
`belowAll`); clause (ii) holds on the group
probes (`grpself`: empty `bad`). The plain exact-owner case is proved; the
group vertical route is falsified by probes (`belowAll=false`), so the group
case is assumed outright. -/
def XLEM_OwnerRest (exactIds : List String) : Prop :=
  (∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    (cg.nodes.getD e.tail default).border ≠ -2 →
    run.exact.contains e.tail = false →
    ∃ nd : ProperNode, run.proper.nodes[e.tail]? = some nd ∧
      (loopFootprintExt cg run execution.measured e.tail).y = run.ys.getD e.tail 0 ∧
      (loopFootprintExt cg run execution.measured e.tail).h = nd.node.h ∧
      ((loopSizes cg.edges execution.measured e.tail cg.slot).length : Int) *
        Loops.band cg.slot (loopSizes cg.edges execution.measured e.tail cg.slot) ≤
        nd.node.h) ∧
  (∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (rk run.coordinateProper.rank v).toNat ≠
      (rk run.coordinateProper.rank e.tail).toNat →
    (cg.nodes.getD e.tail default).border = -2 →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v))

/-- Exact owner node: an index in `run.exact` comes from a component node
whose declaration is exact, with a component index bound. -/
private theorem xlemRank_owner_cg (exactIds : List String) (inp : Input)
    (cg : Graph) (run : Run)
    {tail : Nat} (hex : run.exact.contains tail)
    (hexact : run.exact = cg.nodes.zipIdx.filterMap fun q =>
      if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none) :
    ∃ nd : Node, cg.nodes[tail]? = some nd ∧
      (exactDecls exactIds inp).contains nd.decl ∧ tail < cg.nodes.length := by
  have hmem : tail ∈ run.exact := by
    have h := hex
    rw [List.contains_eq_mem] at h
    exact of_decide_eq_true h
  rw [hexact] at hmem
  obtain ⟨a, haMem, haEq⟩ := List.mem_filterMap.mp hmem
  have ha2 : a.2 = tail := by
    by_cases hc : (exactDecls exactIds inp).contains a.1.decl = true
    · rw [ite_eq_left hc] at haEq
      exact Option.some.inj haEq
    · rw [ite_eq_right hc] at haEq
      exact absurd haEq (by simp)
  have hexCg : (exactDecls exactIds inp).contains a.1.decl := by
    by_cases hc : (exactDecls exactIds inp).contains a.1.decl = true
    · exact hc
    · rw [ite_eq_right hc] at haEq
      exact absurd haEq (by simp)
  have hcg : cg.nodes[a.2]? = some a.1 :=
    List.mem_zipIdx_iff_getElem?.mp haMem
  rw [ha2] at hcg
  refine ⟨a.1, hcg, hexCg, ?_⟩
  exact (List.getElem?_eq_some_iff.mp hcg).1

/-- Other-box band fact: a target box stands inside its own rank band. Proved
below as `XLEM_OtherBand_holds` from `componentRunX_node_band` plus the
coordinate record transfer. -/
def XLEM_OtherBand (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (rk run.coordinateProper.rank v).toNat ≠
      (rk run.coordinateProper.rank e.tail).toNat →

    ∃ lv : List Nat,
      run.layers[(rk run.coordinateProper.rank v).toNat]? = some lv ∧
      run.top.getD (rk run.coordinateProper.rank v).toNat 0 ≤
        (RouteImpl.boxRect run.proper run.xs run.ys v).y ∧
      (RouteImpl.boxRect run.proper run.xs run.ys v).y +
        (RouteImpl.boxRect run.proper run.xs run.ys v).h ≤
        run.top.getD (rk run.coordinateProper.rank v).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper lv

private theorem xlemRank_not_meets_of_below {a b : Rect}
    (h : a.y + a.h ≤ b.y) : ¬ a.meetsInterior b := by
  unfold Rect.meetsInterior
  omega

private theorem xlemRank_not_meets_of_above {a b : Rect}
    (h : b.y + b.h ≤ a.y) : ¬ a.meetsInterior b := by
  unfold Rect.meetsInterior
  omega

/-- Copy of the private `X_nonproxy_record` in `ExactFlatC2`. -/
private theorem xlemRank_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- Copy of the private `X_fbs_coordinate_record` in `ExactFlatC2`. -/
private theorem xlemRank_fbs_coordinate_record {P : Params} {exact : List Nat} {cg : Graph}
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
  obtain ⟨hfull, -⟩ := xlemRank_nonproxy_record hrun hcadr hnp
  have := Option.some.inj (hrec.symm.trans hfull)
  rw [← this]

private theorem xlemRank_extra_fold_length (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (rest : List (Node × Nat)) (acc : List Int)
    (hlen : acc.length = top_pre.length) :
    ((rest.foldl (xlemRank_extra_step cg exact labels p ys_pre top_pre heights)
      acc).length) = top_pre.length := by
  induction rest generalizing acc with
  | nil => simpa only [List.foldl_nil] using hlen
  | cons q rest ih =>
    rw [List.foldl_cons]
    exact ih _ ((xlemRank_extra_step_length _ _ _ _ _ _ _ _ _).trans hlen)
private theorem xlemRank_exact_stack_le (P : Params) (exactIds : List String) (inp : Input)
    (cg : Graph) (run : Run) (labels : List MeasuredLabel) (orderOptions : OrderOptions)
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {tail : Nat} {nd : ProperNode}
    (hq : run.proper.nodes[tail]? = some nd)
    (hrec : ∃ cw : ProperNode, run.coordinateProper.nodes[tail]? = some cw ∧
      cw.node.border = nd.node.border ∧ cw.node.h = nd.node.h)
    (hex : run.exact.contains tail)
    (k : Nat) {e : Edge} (hedge : cg.edges[k]? = some e) (hself : e.tail = e.head)
    (hown : e.tail = tail)
    (hbdr : (cg.nodes.getD tail default).border ≠ -2)
    {rv : Nat} {lv : List Nat}
    (hlt : (rk run.coordinateProper.rank tail).toNat < rv)
    (hly : run.layers[rv]? = some lv) :
    (loopFootprintExt cg run labels tail).y +
      (((loopSizes cg.edges labels tail cg.slot).length : Int) *
        Loops.band cg.slot (loopSizes cg.edges labels tail cg.slot)) ≤
      run.top.getD rv 0 := by
  have hrunX := hrun
  rw [componentRunX_eq_gen] at hrun
  obtain ⟨ranks, p0, labeled, q0, y_pre, top_pre, ys_pre, hn, hl, hcoord, hord,
    hcross, hproxy, hdrop, hroute, hr2, hry, hyspre, hres, hcy, hroutes, hexact⟩ :=
    componentRunGen_spec hrun
  obtain ⟨ndCg, hcg, hexCg, _⟩ :=
    xlemRank_owner_cg exactIds inp cg run hex hexact
  have hmemE : e ∈ cg.edges := List.mem_of_getElem? hedge
  have hhead : e.head = tail := hself ▸ hown
  have hloop : e ∈ loopEdges cg.edges tail :=
    List.mem_filter.mpr ⟨hmemE, by simp [hown, hhead]⟩
  have hmemSz : stackSize cg.slot (routeLabels labels e.decl) ∈
      loopSizes cg.edges labels tail cg.slot := by
    unfold loopSizes
    exact List.mem_map.mpr ⟨e, hloop, rfl⟩
  have hneNil : loopSizes cg.edges labels tail cg.slot ≠ [] := by
    intro hnil
    rw [hnil] at hmemSz
    exact absurd hmemSz List.not_mem_nil
  have hne : ¬ (loopSizes cg.edges labels tail cg.slot).isEmpty := by
    intro h
    exact hneNil (List.isEmpty_iff.mp h)
  obtain ⟨nvc, hnc, hbEq, hhEq, -⟩ := xlemRank_fbs_coordinate_record hrunX hq
  obtain ⟨lo, hlo, _, _⟩ :=
    componentRunX_node_band hrunX hq ⟨nvc, hnc, hbEq, hhEq⟩
  obtain ⟨hFredY, _⟩ := xlemRank_frame_plain P cg run tail hbdr hq
  have hFy : (loopFootprintExt cg run labels tail).y = run.ys.getD tail 0 := hFredY
  have htopLen : top_pre.length = run.layers.length :=
    (CoordsImpl.rankCoordsWith_length hry).2
  have hro : (rk run.coordinateProper.rank tail).toNat < top_pre.length := by
    rw [htopLen]
    exact (List.getElem?_eq_some_iff.mp hlo).1
  have hrv' : rv < top_pre.length := by
    rw [htopLen]
    exact (List.getElem?_eq_some_iff.mp hly).1
  have hylen : y_pre.length = run.coordinateProper.nodes.length :=
    (CoordsImpl.rankCoordsWith_length hry).1
  have hysLen : ys_pre.length = run.coordinateProper.nodes.length :=
    xlemRank_ys_pre_length run y_pre top_pre ys_pre hylen hyspre
  have htailC : tail < run.coordinateProper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnc).1
  have htailY : tail < ys_pre.length := by omega
  obtain ⟨htop, hys, hpref⟩ :=
    xlemRank_shift_top_ys exactIds inp cg run labels hres
  have hH : ((run.layers.map fun layer =>
      layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD
      (rk run.coordinateProper.rank tail).toNat 0) =
      CoordsImpl.layerHeight run.coordinateProper lo :=
    xlemRank_heights_getD _ _ _ _ hlo
  have hbase : ∀ (n : Nat) (j : Nat), 0 ≤ (List.replicate n (0 : Int)).getD j 0 := by
    intro n j
    induction n generalizing j with
    | zero => exact Int.le_refl _
    | succ n ih =>
      cases j with
      | zero => exact Int.le_refl _
      | succ j => exact ih j
  have hmem2 : (ndCg, tail) ∈ ([] : List (Node × Nat)) ++ cg.nodes.zipIdx :=
    List.mem_append.mpr (Or.inr (List.mem_zipIdx_iff_getElem?.mpr hcg))
  have hneed := xlemRank_extra_fold_covers cg (exactDecls exactIds inp) labels
    run.coordinateProper ys_pre top_pre
    (run.layers.map fun layer =>
      layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0)
    [] cg.nodes.zipIdx (List.replicate top_pre.length 0) (by simp)
    (fun q hq => absurd hq List.not_mem_nil) (ndCg, tail) hmem2 hexCg hne hro
  have hneed2 : ys_pre.getD tail 0 +
      max ndCg.h (((loopSizes cg.edges labels tail cg.slot).length : Int) *
        Loops.band cg.slot (loopSizes cg.edges labels tail cg.slot)) -
      top_pre.getD (rk run.coordinateProper.rank tail).toNat 0 -
      (run.layers.map fun layer =>
        layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD
        (rk run.coordinateProper.rank tail).toNat 0 ≤
      (cg.nodes.zipIdx.foldl (xlemRank_extra_step cg (exactDecls exactIds inp) labels
        run.coordinateProper ys_pre top_pre (run.layers.map fun layer =>
          layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
        (List.replicate top_pre.length 0)).getD
        (rk run.coordinateProper.rank tail).toNat 0 := hneed
  have hpre := CoordsImpl.rankAxis_bands_disjoint hry _ _ _ _ hlt hlo hly
  have hresv : ((loopSizes cg.edges labels tail cg.slot).length : Int) *
      Loops.band cg.slot (loopSizes cg.edges labels tail cg.slot) ≤
      max ndCg.h (((loopSizes cg.edges labels tail cg.slot).length : Int) *
        Loops.band cg.slot (loopSizes cg.edges labels tail cg.slot)) :=
    Int.le_max_right _ _
  have hysT : run.ys.getD tail 0 =
      ys_pre.getD tail 0 + (((cg.nodes.zipIdx.foldl (xlemRank_extra_step cg
        (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
        (run.layers.map fun layer =>
          layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
        (List.replicate top_pre.length 0)).foldl
        (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD
        (rk run.coordinateProper.rank tail).toNat 0 := hys tail htailY
  have htopR : run.top.getD rv 0 = top_pre.getD rv 0 + (((cg.nodes.zipIdx.foldl
      (xlemRank_extra_step cg (exactDecls exactIds inp) labels run.coordinateProper ys_pre
        top_pre (run.layers.map fun layer =>
          layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
        (List.replicate top_pre.length 0)).foldl
        (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD rv 0 :=
    htop rv hrv'
  have hnn : ∀ i, 0 ≤ (cg.nodes.zipIdx.foldl (xlemRank_extra_step cg
      (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
      (run.layers.map fun layer =>
        layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
      (List.replicate top_pre.length 0)).getD i 0 :=
    xlemRank_extra_nonneg _ _ _ _ _ _ _ _ _ (fun j => hbase _ j)
  have hlenS : (((cg.nodes.zipIdx.foldl (xlemRank_extra_step cg (exactDecls exactIds inp)
      labels run.coordinateProper ys_pre top_pre (run.layers.map fun layer =>
        layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
      (List.replicate top_pre.length 0)).foldl
      (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).length =
      top_pre.length := by
    have hE : ((cg.nodes.zipIdx.foldl (xlemRank_extra_step cg (exactDecls exactIds inp)
        labels run.coordinateProper ys_pre top_pre (run.layers.map fun layer =>
          layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
        (List.replicate top_pre.length 0)).length) = top_pre.length :=
      xlemRank_extra_fold_length _ _ _ _ _ _ _ _ _ (by simp)
    have hS := xlemRank_fold_sums (cg.nodes.zipIdx.foldl (xlemRank_extra_step cg
      (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
      (run.layers.map fun layer =>
        layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
      (List.replicate top_pre.length 0)) (0 : Int) ([] : List Int)
    rw [hS]
    simp [xlemRank_sums_length, hE]
  have hdiff := xlemRank_shifts_diff_ge _ _ hpref hnn hlt (by omega)
  omega



theorem XLEM_OtherBand_holds (exactIds : List String) : XLEM_OtherBand exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hedge hself hvlt hreal hdeclT hdeclH hne
  have hnd : run.proper.nodes[v]? = some run.proper.nodes[v] :=
    List.getElem?_eq_getElem hvlt
  obtain ⟨nvc, hnc, hbEq, hhEq, -⟩ := xlemRank_fbs_coordinate_record hrun hnd
  obtain ⟨l, hly, hlo, hhi⟩ := componentRunX_node_band hrun hnd ⟨nvc, hnc, hbEq, hhEq⟩
  refine ⟨l, hly, ?_, ?_⟩
  · show run.top.getD (rk run.coordinateProper.rank v).toNat 0 ≤ run.ys.getD v 0
    exact hlo
  · show run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤
        run.top.getD (rk run.coordinateProper.rank v).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper l
    exact hhi

theorem XLEM_otherRankMiss_holds (exactIds : List String)
    (hFoot : XLEM_FootBelow exactIds) (hRest : XLEM_OwnerRest exactIds) :
    XLEM_OtherRankMiss exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg k e v
    hcomp hcg hrun hedge hself hvlt hreal hdeclT hdeclH hne
  obtain ⟨_, hdisj⟩ := X_ReserveBands_holds exactIds hrun
  obtain ⟨_, hlv, hTopV, hBotV⟩ :=
    XLEM_OtherBand_holds exactIds inp o res execution comp candidate run
      orderOptions cg k e v hcomp hcg hrun hedge hself hvlt hreal hdeclT hdeclH hne
  by_cases hb : (cg.nodes.getD e.tail default).border = -2
  · exact hRest.2 inp o res execution hwf hfp comp candidate run orderOptions cg k e v
      hcomp hcg hrun hedge hself hvlt hreal hdeclT hdeclH hne hb
  · obtain ⟨_, hlo, hTopOwn, hBelow⟩ :=
        hFoot inp o res execution comp candidate run orderOptions cg k e
          hcomp hcg hrun hedge hself hb
    have hne' : (rk run.coordinateProper.rank e.tail).toNat <
        (rk run.coordinateProper.rank v).toNat ∨
        (rk run.coordinateProper.rank v).toNat <
        (rk run.coordinateProper.rank e.tail).toNat :=
      by omega
    cases hne' with
    | inl hltRV =>
      have hle := hBelow _ _ hltRV hlv
      exact xlemRank_not_meets_of_below (by omega)
    | inr hgtRV =>
      have hle := hdisj _ _ _ _ hgtRV hlv hlo
      exact xlemRank_not_meets_of_above (by omega)

end PipelineImpl
end Layered
end Elegant

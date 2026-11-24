import Elegant.Layered.ExactLoopEnvelopeRankProof
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.LoopFootprintGeneralOrder

set_option autoImplicit false

open Elegant Layered

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Foot-below half of the loop-envelope miss, over exact runs.

Target: `XLEM_FootBelow` (`ExactLoopEnvelopeRankProof.lean`): for a plain
owner (`border ≠ -2`) the extended footprint starts at or below its rank band
start and ends above every higher rank start.

Probe truth (`proofs/wip/Probe/ExactLoopEnvelopeFootBelowTProbe.lean`,
`exactIds = ["a"]`, vector profile, declaration order):
- `1loop-exact-big`: `tails ro=0 top=0 Fy=0 Fh=1536 hgt=100 tailIn=true covTop=true belowAll=true` (4 orders).
- `1loop-exact-zero-degenerate`: `ro=0 top=0 Fy=0 Fh=1536 hgt=0 tailIn=true covTop=true belowAll=true` (4 orders).
- `2loop-exact-small`: same shape with `n=2`, `belowAll=true`.
- `1loop-nonexact-plain-sibself`: `tops=[0] layers=1 higher=[] belowAll=true covTop=true covBot=true resv=true exactOwn=false` (4 orders).
- `1loop-group-grpself`: `tops=[0,6144,9316] higher=[1,2] belowAll=false exactOwn=false border=-2` (group fails below-all, so plain premise needed).
- `2loop-group-grpself`: `belowAll=false` again.
- `illformed-dup-id`: `prep error LayoutError.domain` (no execution).

Exact owners use the prefixed stack copy below plus `X_ReserveBands_holds`;
plain non-exact owners use the narrow reservation residual plus the same bands.
Group owners stay as the single named residual `XLEM_GroupOwnerOtherRank`.
All record literals are on one line.
-/

private def xlemFB_needed (cg : Graph) (labels : List MeasuredLabel) (p : Proper)
    (ys_pre top_pre heights : List Int) (q : Node × Nat) : Int :=
  ys_pre.getD q.2 0 +
    max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
      Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
    top_pre.getD (p.rank.getD q.2 0).toNat 0 -
    heights.getD (p.rank.getD q.2 0).toNat 0

/-- One reserve fold step: exact loop owners max their need into their rank. -/
private def xlemFB_extra_step (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (acc : List Int) (q : Node × Nat) : List Int :=
  if !exact.contains q.1.decl then acc
  else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
  else acc.set (p.rank.getD q.2 0).toNat
    (max (acc.getD (p.rank.getD q.2 0).toNat 0)
      (xlemFB_needed cg labels p ys_pre top_pre heights q))

private theorem xlemFB_getD_set_max_ge (acc : List Int) {i j : Nat} {a : Int} :
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
private theorem xlemFB_extra_step_length (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (acc : List Int) (q : Node × Nat) :
    (xlemFB_extra_step cg exact labels p ys_pre top_pre heights acc q).length =
      acc.length := by
  unfold xlemFB_extra_step
  split
  · rfl
  · split
    · rfl
    · exact List.length_set

private theorem xlemFB_extra_step_ge (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (acc : List Int) (q : Node × Nat) :
    ∀ j, acc.getD j 0 ≤
      (xlemFB_extra_step cg exact labels p ys_pre top_pre heights acc q).getD j 0 := by
  intro j
  unfold xlemFB_extra_step
  split
  · exact Int.le_refl _
  · split
    · exact Int.le_refl _
    · exact xlemFB_getD_set_max_ge acc

private theorem xlemFB_extra_fold_covers (cg : Graph) (exact : List Nat)
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
          (xlemFB_extra_step cg exact labels p ys_pre top_pre heights)
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
      (xlemFB_extra_step cg exact labels p ys_pre top_pre heights acc q') ?_ ?_
      _ hmem2 hex hne hlt
    · rw [xlemFB_extra_step_length _ _ _ _ _ _ _ _ _]; exact hlen
    · intro q'' hmem'' hex'' hne'' hlt''
      rcases List.mem_append.mp hmem'' with h | h
      · calc ys_pre.getD q''.2 0 +
              max q''.1.h (((loopSizes cg.edges labels q''.2 cg.slot).length : Int) *
                Loops.band cg.slot (loopSizes cg.edges labels q''.2 cg.slot)) -
              top_pre.getD (p.rank.getD q''.2 0).toNat 0 -
              heights.getD (p.rank.getD q''.2 0).toNat 0
            ≤ acc.getD (p.rank.getD q''.2 0).toNat 0 :=
              hacc q'' h hex'' hne'' hlt''
          _ ≤ (xlemFB_extra_step cg exact labels p ys_pre top_pre heights acc
              q').getD (p.rank.getD q''.2 0).toNat 0 :=
            xlemFB_extra_step_ge cg exact labels p ys_pre top_pre heights acc q' _
      · obtain rfl : q' = q'' := (List.mem_singleton.mp h).symm
        have hset : (acc.set (p.rank.getD q'.2 0).toNat
            (max (acc.getD (p.rank.getD q'.2 0).toNat 0)
              (xlemFB_needed cg labels p ys_pre top_pre heights q'))).getD
              (p.rank.getD q'.2 0).toNat 0 =
            max (acc.getD (p.rank.getD q'.2 0).toNat 0)
              (xlemFB_needed cg labels p ys_pre top_pre heights q') := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_set_self (by omega : (p.rank.getD q'.2 0).toNat < acc.length),
            Option.getD_some]
        have hstep : xlemFB_extra_step cg exact labels p ys_pre top_pre heights acc q' =
            acc.set (p.rank.getD q'.2 0).toNat
              (max (acc.getD (p.rank.getD q'.2 0).toNat 0)
                (xlemFB_needed cg labels p ys_pre top_pre heights q')) := by
          unfold xlemFB_extra_step
          by_cases h1 : (!exact.contains q'.1.decl) = true
          · exact absurd h1 (by simpa using hex'')
          · rw [ite_eq_right h1]
            by_cases h2 : (loopSizes cg.edges labels q'.2 cg.slot).isEmpty = true
            · exact absurd h2 hne''
            · rw [ite_eq_right h2]
        rw [hstep, hset]
        exact Int.le_max_right _ _

private def xlemFB_sums (s : Int) : List Int → List Int
  | [] => []
  | e :: es => s :: xlemFB_sums (s + e) es

private theorem xlemFB_sums_length (s : Int) (l : List Int) :
    (xlemFB_sums s l).length = l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons e es ih => simp only [xlemFB_sums, List.length_cons, ih]

private theorem xlemFB_fold_sums (l : List Int) (s : Int) (out : List Int) :
    (l.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2 =
      out ++ xlemFB_sums s l := by
  induction l generalizing s out with
  | nil => simp only [List.foldl_nil, xlemFB_sums, List.append_nil]
  | cons e es ih =>
    simp only [List.foldl_cons, xlemFB_sums]
    rw [ih]
    simp [List.append_assoc]

private theorem xlemFB_sums_getD (l : List Int) (s : Int) (r : Nat)
    (hr : r < l.length) :
    (xlemFB_sums s l).getD r 0 = s + ((l.take r).sum) := by
  induction l generalizing s r with
  | nil => simp at hr
  | cons e es ih =>
    cases r with
    | zero => simp [xlemFB_sums]
    | succ r =>
      simp only [xlemFB_sums, List.getD_cons_succ]
      have hlen : (e :: es).length = es.length + 1 := rfl
      have hr' : r < es.length := by omega
      rw [ih _ _ hr']
      simp [List.take_succ_cons, List.sum_cons]
      omega
private theorem xlemFB_sum_nonneg (l : List Int) (h : ∀ i, 0 ≤ l.getD i 0) :
    0 ≤ l.sum := by
  induction l with
  | nil => exact Int.le_refl _
  | cons a as ih =>
    rw [List.sum_cons]
    exact Int.add_nonneg (h 0) (ih (fun i => h (i + 1)))

private theorem xlemFB_sum_ge_getD_zero (l : List Int) (h : ∀ i, 0 ≤ l.getD i 0) :
    l.getD 0 0 ≤ l.sum := by
  cases l with
  | nil => exact Int.le_refl _
  | cons a as =>
    rw [List.sum_cons]
    have htail : 0 ≤ as.sum := xlemFB_sum_nonneg as (fun i => h (i + 1))
    have ha : (a :: as).getD 0 0 = a := rfl
    omega

private theorem xlemFB_rest_getD (extra : List Int) (ro rv i : Nat)
    (hlt : ro + i < rv) :
    (((extra.take rv).drop ro).getD i 0) = extra.getD (ro + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take,
    ite_eq_left hlt, ← List.getD_eq_getElem?_getD]

private theorem xlemFB_shifts_diff_ge (extra shifts : List Int)
    (hpref : shifts =
      (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2)
    (hnn : ∀ i, 0 ≤ extra.getD i 0)
    {ro rv : Nat} (hlt : ro < rv) (hrv : rv < shifts.length) :
    shifts.getD ro 0 + extra.getD ro 0 ≤ shifts.getD rv 0 := by
  have hshifts : shifts = xlemFB_sums 0 extra := by
    rw [hpref, xlemFB_fold_sums]
    simp
  have hlen : shifts.length = extra.length := by
    rw [hshifts, xlemFB_sums_length]
  have hro : ro < extra.length := by omega
  have hrv' : rv < extra.length := by omega
  rw [hshifts, xlemFB_sums_getD _ _ _ hro, xlemFB_sums_getD _ _ _ hrv']
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
    · rw [xlemFB_rest_getD _ _ _ _ h]
      exact hnn _
    · have hL : (((extra.take rv).drop ro).length) ≤ i := by
        rw [List.length_drop, List.length_take]
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hL]
      simp
  have hge : (((extra.take rv).drop ro).getD 0 0) ≤ (((extra.take rv).drop ro).sum) :=
    xlemFB_sum_ge_getD_zero _ hrest_nn
  have hhead : (((extra.take rv).drop ro).getD 0 0) = extra.getD ro 0 := by
    rw [xlemFB_rest_getD _ _ _ _ (by omega : ro + 0 < rv)]
    congr 1
  omega

private theorem xlemFB_frame_plain (P : Params) (cg : Graph) (run : Run) (tail : Nat)
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

private theorem xlemFB_ys_pre_length (run : Run)
    (y_pre top_pre ys_pre : List Int)
    (hlen : y_pre.length = run.coordinateProper.nodes.length)
    (hyspre : proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre) :
    ys_pre.length = run.coordinateProper.nodes.length := by
  rw [← hyspre]
  unfold proxyYs
  simp only [List.length_map, List.length_zipIdx]
  exact hlen
private theorem xlemFB_heights_getD (p : Proper) (layers : List (List Nat))
    (l : List Nat) (r : Nat) (hly : layers[r]? = some l) :
    ((layers.map fun layer =>
      layer.foldl (fun h v => max h (RouteImpl.nodeH p v)) 0).getD r 0) =
      CoordsImpl.layerHeight p l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hly, Option.map_some,
    Option.getD_some]
  rfl

private theorem xlemFB_extra_nonneg (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (rest : List (Node × Nat)) (acc : List Int)
    (hacc : ∀ j, 0 ≤ acc.getD j 0) :
    ∀ j, 0 ≤ ((rest.foldl
      (xlemFB_extra_step cg exact labels p ys_pre top_pre heights) acc).getD j 0) := by
  induction rest generalizing acc with
  | nil => simpa only [List.foldl_nil] using hacc
  | cons q rest ih =>
    intro j
    rw [List.foldl_cons]
    exact ih _ (fun i => Int.le_trans (hacc i)
      (xlemFB_extra_step_ge cg exact labels p ys_pre top_pre heights acc q i)) j


private theorem xlemFB_shift_top_ys (exactIds : List String) (inp : Input)
    (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    {top_pre ys_pre : List Int}
    (hres : reserveExactRanks cg (exactDecls exactIds inp) labels run.coordinateProper
      run.layers ys_pre top_pre = .ok (run.ys, run.top)) :
    let extra := cg.nodes.zipIdx.foldl
      (xlemFB_extra_step cg (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
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

/-- Exact owner node: an index in `run.exact` comes from a component node
whose declaration is exact, with a component index bound. -/
private theorem xlemFB_owner_cg (exactIds : List String) (inp : Input)
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


private theorem xlemFB_not_meets_of_below {a b : Rect}
    (h : a.y + a.h ≤ b.y) : ¬ a.meetsInterior b := by
  unfold Rect.meetsInterior
  omega

private theorem xlemFB_not_meets_of_above {a b : Rect}
    (h : b.y + b.h ≤ a.y) : ¬ a.meetsInterior b := by
  unfold Rect.meetsInterior
  omega

/-- Copy of the private `X_nonproxy_record` in `ExactFlatC2`. -/
private theorem xlemFB_nonproxy_record {P : Params} {exact : List Nat}
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
private theorem xlemFB_fbs_coordinate_record {P : Params} {exact : List Nat} {cg : Graph}
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
  obtain ⟨hfull, -⟩ := xlemFB_nonproxy_record hrun hcadr hnp
  have := Option.some.inj (hrec.symm.trans hfull)
  rw [← this]

private theorem xlemFB_extra_fold_length (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys_pre top_pre heights : List Int)
    (rest : List (Node × Nat)) (acc : List Int)
    (hlen : acc.length = top_pre.length) :
    ((rest.foldl (xlemFB_extra_step cg exact labels p ys_pre top_pre heights)
      acc).length) = top_pre.length := by
  induction rest generalizing acc with
  | nil => simpa only [List.foldl_nil] using hlen
  | cons q rest ih =>
    rw [List.foldl_cons]
    exact ih _ ((xlemFB_extra_step_length _ _ _ _ _ _ _ _ _).trans hlen)
private theorem xlemFB_exact_stack_le (P : Params) (exactIds : List String) (inp : Input)
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
    xlemFB_owner_cg exactIds inp cg run hex hexact
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
  obtain ⟨nvc, hnc, hbEq, hhEq, -⟩ := xlemFB_fbs_coordinate_record hrunX hq
  obtain ⟨lo, hlo, _, _⟩ :=
    componentRunX_node_band hrunX hq ⟨nvc, hnc, hbEq, hhEq⟩
  obtain ⟨hFredY, _⟩ := xlemFB_frame_plain P cg run tail hbdr hq
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
    xlemFB_ys_pre_length run y_pre top_pre ys_pre hylen hyspre
  have htailC : tail < run.coordinateProper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hnc).1
  have htailY : tail < ys_pre.length := by omega
  obtain ⟨htop, hys, hpref⟩ :=
    xlemFB_shift_top_ys exactIds inp cg run labels hres
  have hH : ((run.layers.map fun layer =>
      layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0).getD
      (rk run.coordinateProper.rank tail).toNat 0) =
      CoordsImpl.layerHeight run.coordinateProper lo :=
    xlemFB_heights_getD _ _ _ _ hlo
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
  have hneed := xlemFB_extra_fold_covers cg (exactDecls exactIds inp) labels
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
      (cg.nodes.zipIdx.foldl (xlemFB_extra_step cg (exactDecls exactIds inp) labels
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
      ys_pre.getD tail 0 + (((cg.nodes.zipIdx.foldl (xlemFB_extra_step cg
        (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
        (run.layers.map fun layer =>
          layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
        (List.replicate top_pre.length 0)).foldl
        (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD
        (rk run.coordinateProper.rank tail).toNat 0 := hys tail htailY
  have htopR : run.top.getD rv 0 = top_pre.getD rv 0 + (((cg.nodes.zipIdx.foldl
      (xlemFB_extra_step cg (exactDecls exactIds inp) labels run.coordinateProper ys_pre
        top_pre (run.layers.map fun layer =>
          layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
        (List.replicate top_pre.length 0)).foldl
        (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD rv 0 :=
    htop rv hrv'
  have hnn : ∀ i, 0 ≤ (cg.nodes.zipIdx.foldl (xlemFB_extra_step cg
      (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
      (run.layers.map fun layer =>
        layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
      (List.replicate top_pre.length 0)).getD i 0 :=
    xlemFB_extra_nonneg _ _ _ _ _ _ _ _ _ (fun j => hbase _ j)
  have hlenS : (((cg.nodes.zipIdx.foldl (xlemFB_extra_step cg (exactDecls exactIds inp)
      labels run.coordinateProper ys_pre top_pre (run.layers.map fun layer =>
        layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
      (List.replicate top_pre.length 0)).foldl
      (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).length =
      top_pre.length := by
    have hE : ((cg.nodes.zipIdx.foldl (xlemFB_extra_step cg (exactDecls exactIds inp)
        labels run.coordinateProper ys_pre top_pre (run.layers.map fun layer =>
          layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
        (List.replicate top_pre.length 0)).length) = top_pre.length :=
      xlemFB_extra_fold_length _ _ _ _ _ _ _ _ _ (by simp)
    have hS := xlemFB_fold_sums (cg.nodes.zipIdx.foldl (xlemFB_extra_step cg
      (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
      (run.layers.map fun layer =>
        layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0))
      (List.replicate top_pre.length 0)) (0 : Int) ([] : List Int)
    rw [hS]
    simp [xlemFB_sums_length, hE]
  have hdiff := xlemFB_shifts_diff_ge _ _ hpref hnn hlt (by omega)
  omega
/-- Group-owner other-rank residual: a group-frame loop owner misses every
other-rank real box. Exactly the second clause of `XLEM_OwnerRest`; the
vertical route is falsified by probes (`belowAll=false` on `grpself`), so the
group case is assumed outright. Strictly narrower than the target. -/
def XLEM_GroupOwnerOtherRank (exactIds : List String) : Prop :=
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
    (cg.nodes.getD e.tail default).border = -2 →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v)
/-- Plain non-exact loop reservation residual: the loop band stack fits in
the owner frame. Exactly the hard inequality of `XLEM_OwnerRest` clause (i)
and of non-exact `XLEM_FootBelow`; true on `sibself` probes (`resv=true`). -/
def XLEM_PlainReserve (exactIds : List String) : Prop :=
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
    run.exact.contains e.tail = false →
    ((loopSizes cg.edges execution.measured e.tail cg.slot).length : Int) *
      Loops.band cg.slot (loopSizes cg.edges execution.measured e.tail cg.slot) ≤
      (frameRect execution.params cg run e.tail).h
/-- Exact-owner foot-below: the footprint of an exact plain owner starts at
or below its band start and ends above every higher band start. Uses the
prefixed stack copy for `n * band` and `X_ReserveBands_holds` for the frame
height. True on exact probes (`covTop`, `belowAll`). -/
theorem XLEM_footBelow_exact_case (exactIds : List String)
    (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidate execution.graph comp candidate)
    (hrun : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured orderOptions = .ok run)
    (hedge : cg.edges[k]? = some e) (hself : e.tail = e.head)
    (hbdr : (cg.nodes.getD e.tail default).border ≠ -2)
    (hex : run.exact.contains e.tail = true) :
    ∃ lo : List Nat,
      run.layers[(rk run.coordinateProper.rank e.tail).toNat]? = some lo ∧
      run.top.getD (rk run.coordinateProper.rank e.tail).toNat 0 ≤
        (loopFootprintExt cg run execution.measured e.tail).y ∧
      ∀ (rv : Nat) (ll : List Nat),
        (rk run.coordinateProper.rank e.tail).toNat < rv →
        run.layers[rv]? = some ll →
        (loopFootprintExt cg run execution.measured e.tail).y +
          (loopFootprintExt cg run execution.measured e.tail).h ≤
          run.top.getD rv 0 := by
  subst hcg
  have hbd := sceneExecutionX_edges_bounded execution
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp
    candidate hcomp hbd (List.mem_of_getElem? hedge)
  have htailCG : e.tail < (componentCandidate execution.graph comp candidate).nodes.length :=
    hbnd.1
  have htailP : e.tail < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun _ htailCG
  obtain ⟨nd, hnd⟩ : ∃ nd, run.proper.nodes[e.tail]? = some nd :=
    ⟨_, List.getElem?_eq_getElem htailP⟩
  obtain ⟨nvc, hnc, hbEq, hhEq, -⟩ := xlemFB_fbs_coordinate_record hrun hnd
  obtain ⟨lo, hlo, hloTop, hloBot⟩ :=
    componentRunX_node_band hrun hnd ⟨nvc, hnc, hbEq, hhEq⟩
  obtain ⟨hFy, hFh⟩ :=
    xlemFB_frame_plain execution.params
      (componentCandidate execution.graph comp candidate) run e.tail hbdr hnd
  have hFootY : (loopFootprintExt
      (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).y =
      run.ys.getD e.tail 0 := hFy
  have hFootH : (loopFootprintExt
      (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).h =
      max nd.node.h (((loopSizes
        (componentCandidate execution.graph comp candidate).edges
        execution.measured e.tail
        (componentCandidate execution.graph comp candidate).slot).length : Int) *
        Loops.band (componentCandidate execution.graph comp candidate).slot
          (loopSizes
            (componentCandidate execution.graph comp candidate).edges
            execution.measured e.tail
            (componentCandidate execution.graph comp candidate).slot)) := by
    have hEq : (frameRect default
        (componentCandidate execution.graph comp candidate) run e.tail).h =
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run e.tail).h := rfl
    have hU : (loopFootprintExt
        (componentCandidate execution.graph comp candidate) run
        execution.measured e.tail).h =
        max (frameRect default
          (componentCandidate execution.graph comp candidate) run e.tail).h
          (((loopSizes
            (componentCandidate execution.graph comp candidate).edges
            execution.measured e.tail
            (componentCandidate execution.graph comp candidate).slot).length : Int) *
            Loops.band (componentCandidate execution.graph comp candidate).slot
              (loopSizes
                (componentCandidate execution.graph comp candidate).edges
                execution.measured e.tail
                (componentCandidate execution.graph comp candidate).slot)) := rfl
    rw [hU, hEq, hFh]
  refine ⟨lo, hlo, by omega, ?_⟩
  intro rv ll hlt hly
  have hNodeH : RouteImpl.nodeH run.proper e.tail = nd.node.h := by
    simp only [RouteImpl.nodeH, hnd]
  obtain ⟨_, hdisj⟩ := X_ReserveBands_holds exactIds hrun
  have hFrameLe : run.ys.getD e.tail 0 + nd.node.h ≤ run.top.getD rv 0 := by
    have h1 : run.ys.getD e.tail 0 + RouteImpl.nodeH run.proper e.tail ≤
        run.top.getD (rk run.coordinateProper.rank e.tail).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper lo := by
      have := hloBot
      omega
    have h2 : run.top.getD (rk run.coordinateProper.rank e.tail).toNat 0 +
        CoordsImpl.layerHeight run.coordinateProper lo ≤ run.top.getD rv 0 :=
      hdisj _ _ _ _ hlt hlo hly
    omega
  have hStackFoot : (loopFootprintExt
      (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).y +
      (((loopSizes
        (componentCandidate execution.graph comp candidate).edges
        execution.measured e.tail
        (componentCandidate execution.graph comp candidate).slot).length : Int) *
        Loops.band (componentCandidate execution.graph comp candidate).slot
          (loopSizes
            (componentCandidate execution.graph comp candidate).edges
            execution.measured e.tail
            (componentCandidate execution.graph comp candidate).slot)) ≤
      run.top.getD rv 0 :=
    xlemFB_exact_stack_le execution.params exactIds inp
      (componentCandidate execution.graph comp candidate) run execution.measured
      orderOptions hrun hnd ⟨nvc, hnc, hbEq, hhEq⟩ hex _ hedge hself rfl hbdr hlt hly
  have hStackYs : run.ys.getD e.tail 0 +
      (((loopSizes
        (componentCandidate execution.graph comp candidate).edges
        execution.measured e.tail
        (componentCandidate execution.graph comp candidate).slot).length : Int) *
        Loops.band (componentCandidate execution.graph comp candidate).slot
          (loopSizes
            (componentCandidate execution.graph comp candidate).edges
            execution.measured e.tail
            (componentCandidate execution.graph comp candidate).slot)) ≤
      run.top.getD rv 0 := by
    rw [← hFootY]
    exact hStackFoot
  have hMax : (loopFootprintExt
      (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).y +
      (loopFootprintExt
        (componentCandidate execution.graph comp candidate) run
        execution.measured e.tail).h ≤ run.top.getD rv 0 := by
    rw [hFootY, hFootH]
    omega
  exact hMax
/-- Plain non-exact frame record: a non-exact plain owner carries its frame
record and its frame covers the loop band stack, modulo the narrow
reservation residual. True on `sibself` probes (`resv`, `covTop`). -/
theorem XLEM_ownerRest_plain_holds (exactIds : List String)
    (hRes : XLEM_PlainReserve exactIds)
    (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidate execution.graph comp candidate)
    (hrun : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured orderOptions = .ok run)
    (hedge : cg.edges[k]? = some e) (hself : e.tail = e.head)
    (hbdr : (cg.nodes.getD e.tail default).border ≠ -2)
    (hnex : run.exact.contains e.tail = false) :
    ∃ nd : ProperNode, run.proper.nodes[e.tail]? = some nd ∧
      (loopFootprintExt cg run execution.measured e.tail).y =
        run.ys.getD e.tail 0 ∧
      (loopFootprintExt cg run execution.measured e.tail).h = nd.node.h ∧
      ((loopSizes cg.edges execution.measured e.tail cg.slot).length : Int) *
        Loops.band cg.slot
          (loopSizes cg.edges execution.measured e.tail cg.slot) ≤
        nd.node.h := by
  subst hcg
  have hbd := sceneExecutionX_edges_bounded execution
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp
    candidate hcomp hbd (List.mem_of_getElem? hedge)
  have htailCG : e.tail < (componentCandidate execution.graph comp candidate).nodes.length :=
    hbnd.1
  have htailP : e.tail < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun _ htailCG
  obtain ⟨nd, hnd⟩ : ∃ nd, run.proper.nodes[e.tail]? = some nd :=
    ⟨_, List.getElem?_eq_getElem htailP⟩
  obtain ⟨hFy, hFh⟩ :=
    xlemFB_frame_plain execution.params
      (componentCandidate execution.graph comp candidate) run e.tail hbdr hnd
  have hFootY : (loopFootprintExt
      (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).y = run.ys.getD e.tail 0 := hFy
  have hResLe := hRes inp o res execution comp candidate run orderOptions
    (componentCandidate execution.graph comp candidate) k e hcomp rfl hrun
    hedge hself hbdr hnex
  have hLe : ((loopSizes
      (componentCandidate execution.graph comp candidate).edges
      execution.measured e.tail
      (componentCandidate execution.graph comp candidate).slot).length : Int) *
      Loops.band (componentCandidate execution.graph comp candidate).slot
        (loopSizes
          (componentCandidate execution.graph comp candidate).edges
          execution.measured e.tail
          (componentCandidate execution.graph comp candidate).slot) ≤
      nd.node.h := by
    have hEq : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run e.tail).h =
        nd.node.h := hFh
    omega
  have hFootH : (loopFootprintExt
      (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).h = nd.node.h := by
    have hEq : (frameRect default
        (componentCandidate execution.graph comp candidate) run e.tail).h =
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run e.tail).h := rfl
    have hU : (loopFootprintExt
        (componentCandidate execution.graph comp candidate) run
        execution.measured e.tail).h =
        max (frameRect default
          (componentCandidate execution.graph comp candidate) run e.tail).h
          (((loopSizes
            (componentCandidate execution.graph comp candidate).edges
            execution.measured e.tail
            (componentCandidate execution.graph comp candidate).slot).length : Int) *
            Loops.band (componentCandidate execution.graph comp candidate).slot
              (loopSizes
                (componentCandidate execution.graph comp candidate).edges
                execution.measured e.tail
                (componentCandidate execution.graph comp candidate).slot)) := rfl
    rw [hU, hEq, hFh]
    exact Int.max_eq_left hLe
  exact ⟨nd, hnd, hFootY, hFootH, hLe⟩
/-- Plain non-exact foot-below, modulo the reservation residual. The band
stack collapses to the frame height (`max_eq_left` with the residual), so
the upper bound is band inclusion plus disjointness; no stack shift needed.
True on `sibself` probes (`covTop`, `belowAll`). -/
theorem XLEM_footBelow_plain_case (exactIds : List String)
    (hRes : XLEM_PlainReserve exactIds)
    (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge)
    (hcomp : comp ∈ components execution.graph)
    (hcg : cg = componentCandidate execution.graph comp candidate)
    (hrun : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured orderOptions = .ok run)
    (hedge : cg.edges[k]? = some e) (hself : e.tail = e.head)
    (hbdr : (cg.nodes.getD e.tail default).border ≠ -2)
    (hnex : run.exact.contains e.tail = false) :
    ∃ lo : List Nat,
      run.layers[(rk run.coordinateProper.rank e.tail).toNat]? = some lo ∧
      run.top.getD (rk run.coordinateProper.rank e.tail).toNat 0 ≤
        (loopFootprintExt cg run execution.measured e.tail).y ∧
      ∀ (rv : Nat) (ll : List Nat),
        (rk run.coordinateProper.rank e.tail).toNat < rv →
        run.layers[rv]? = some ll →
        (loopFootprintExt cg run execution.measured e.tail).y +
          (loopFootprintExt cg run execution.measured e.tail).h ≤
          run.top.getD rv 0 := by
  subst hcg
  have hbd := sceneExecutionX_edges_bounded execution
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp
    candidate hcomp hbd (List.mem_of_getElem? hedge)
  have htailCG : e.tail < (componentCandidate execution.graph comp candidate).nodes.length :=
    hbnd.1
  have htailP : e.tail < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun _ htailCG
  obtain ⟨nd, hnd⟩ : ∃ nd, run.proper.nodes[e.tail]? = some nd :=
    ⟨_, List.getElem?_eq_getElem htailP⟩
  obtain ⟨nvc, hnc, hbEq, hhEq, -⟩ := xlemFB_fbs_coordinate_record hrun hnd
  obtain ⟨lo, hlo, hloTop, hloBot⟩ :=
    componentRunX_node_band hrun hnd ⟨nvc, hnc, hbEq, hhEq⟩
  obtain ⟨hFy, hFh⟩ :=
    xlemFB_frame_plain execution.params
      (componentCandidate execution.graph comp candidate) run e.tail hbdr hnd
  have hFootY : (loopFootprintExt
      (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).y = run.ys.getD e.tail 0 := hFy
  have hResLe := hRes inp o res execution comp candidate run orderOptions
    (componentCandidate execution.graph comp candidate) k e hcomp rfl hrun
    hedge hself hbdr hnex
  have hLe : ((loopSizes
      (componentCandidate execution.graph comp candidate).edges
      execution.measured e.tail
      (componentCandidate execution.graph comp candidate).slot).length : Int) *
      Loops.band (componentCandidate execution.graph comp candidate).slot
        (loopSizes
          (componentCandidate execution.graph comp candidate).edges
          execution.measured e.tail
          (componentCandidate execution.graph comp candidate).slot) ≤
      nd.node.h := by
    have hEq : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run e.tail).h =
        nd.node.h := hFh
    omega
  have hFootH : (loopFootprintExt
      (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).h = nd.node.h := by
    have hEq : (frameRect default
        (componentCandidate execution.graph comp candidate) run e.tail).h =
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run e.tail).h := rfl
    have hU : (loopFootprintExt
        (componentCandidate execution.graph comp candidate) run
        execution.measured e.tail).h =
        max (frameRect default
          (componentCandidate execution.graph comp candidate) run e.tail).h
          (((loopSizes
            (componentCandidate execution.graph comp candidate).edges
            execution.measured e.tail
            (componentCandidate execution.graph comp candidate).slot).length : Int) *
            Loops.band (componentCandidate execution.graph comp candidate).slot
              (loopSizes
                (componentCandidate execution.graph comp candidate).edges
                execution.measured e.tail
                (componentCandidate execution.graph comp candidate).slot)) := rfl
    rw [hU, hEq, hFh]
    exact Int.max_eq_left hLe
  refine ⟨lo, hlo, by omega, ?_⟩
  intro rv ll hlt hly
  have hNodeH : RouteImpl.nodeH run.proper e.tail = nd.node.h := by
    simp only [RouteImpl.nodeH, hnd]
  obtain ⟨_, hdisj⟩ := X_ReserveBands_holds exactIds hrun
  have hFrameLe : run.ys.getD e.tail 0 + nd.node.h ≤ run.top.getD rv 0 := by
    have h1 : run.ys.getD e.tail 0 + RouteImpl.nodeH run.proper e.tail ≤
        run.top.getD (rk run.coordinateProper.rank e.tail).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper lo := by
      have := hloBot
      omega
    have h2 : run.top.getD (rk run.coordinateProper.rank e.tail).toNat 0 +
        CoordsImpl.layerHeight run.coordinateProper lo ≤ run.top.getD rv 0 :=
      hdisj _ _ _ _ hlt hlo hly
    omega
  have hGoal : (loopFootprintExt
      (componentCandidate execution.graph comp candidate) run
      execution.measured e.tail).y +
      (loopFootprintExt
        (componentCandidate execution.graph comp candidate) run
        execution.measured e.tail).h ≤ run.top.getD rv 0 := by
    rw [hFootY, hFootH]
    exact hFrameLe
  exact hGoal
/-- Full foot-below from the exact case and the plain reservation residual.
Case-splits on `run.exact.contains`; group owners stay excluded by the
`border ≠ -2` premise (probes: `belowAll=false` on `grpself`). -/
theorem XLEM_footBelow_holds (exactIds : List String)
    (hRes : XLEM_PlainReserve exactIds) : XLEM_FootBelow exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e
    hcomp hcg hrun hedge hself hbdr
  by_cases hex : run.exact.contains e.tail = true
  · exact XLEM_footBelow_exact_case exactIds inp o res execution comp
      candidate run orderOptions cg k e hcomp hcg hrun hedge hself hbdr hex
  · have hnex : run.exact.contains e.tail = false :=
      Bool.eq_false_iff.mpr hex
    exact XLEM_footBelow_plain_case exactIds hRes inp o res execution comp
      candidate run orderOptions cg k e hcomp hcg hrun hedge hself hbdr hnex
/-- Closed other-rank miss from the foot-below chain and the two residuals.
Takes at most the group-owner residual and the plain reservation residual;
the exact-owner foot-below and the plain frame record are proved. The group
case requires well-formed input and framed parents; plain reservation does
not require those admission facts. -/
theorem XLEM_otherRankMiss_closed (exactIds : List String)
    (hRes : XLEM_PlainReserve exactIds)
    (hGrp : XLEM_GroupOwnerOtherRank exactIds) :
    XLEM_OtherRankMiss exactIds := by
  apply XLEM_otherRankMiss_holds exactIds
  · exact XLEM_footBelow_holds exactIds hRes
  · constructor
    · intro inp o res execution comp candidate run orderOptions cg k e
        hcomp hcg hrun hedge hself hbdr hnex
      exact XLEM_ownerRest_plain_holds exactIds hRes inp o res execution
        comp candidate run orderOptions cg k e hcomp hcg hrun hedge hself
        hbdr hnex
    · exact hGrp

end PipelineImpl
end Layered
end Elegant

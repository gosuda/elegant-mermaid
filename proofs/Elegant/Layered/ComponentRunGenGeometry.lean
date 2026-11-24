import Elegant.Layered.ComponentRunGen
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExactFlatC2
import ElegantGeometry.Disjoint
import Elegant.Layered.ForeignNonGroupSpansProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

structure RunHooksShift (P : Params) (sizeHook : Proper → Proper) (reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)) (exactOut : List Nat) (cg : Graph) (labels : List MeasuredLabel) : Prop where
  shifts : ∀ (p : Proper) (layers : List (List Nat)) (ys top ys' top' : List Int),
    reserveHook p layers ys top = .ok (ys', top') →
    ∃ extra shifts : List Int, extra.length = top.length ∧ (∀ e ∈ extra, 0 ≤ e) ∧
      shifts = (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2 ∧
      shifts.length = top.length ∧
      (∀ r, r < top.length → top'.getD r 0 = top.getD r 0 + shifts.getD r 0) ∧
      (∀ j, j < ys.length → ys'.getD j 0 = ys.getD j 0 + shifts.getD ((p.rank.getD j 0).toNat) 0)
  bands : ∀ {run : Run} {orderOptions : OrderOptions},
    componentRunGen P sizeHook reserveHook exactOut cg labels orderOptions = .ok run →
    (∀ (r : Nat) (l : List Nat) (v : Nat), run.layers[r]? = some l → v ∈ l →
      v < run.coordinateProper.nodes.length → rk run.coordinateProper.rank v = (r : Int) →
      run.top.getD r 0 ≤ run.ys.getD v 0 ∧
      run.ys.getD v 0 + CoordsImpl.nodeH run.coordinateProper v ≤
        run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l) ∧
    (∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l ≤
      run.top.getD r' 0)
private theorem gen_prefix_replicate_zero_aux (s : List Int) (out : List Int) (hs : ∀ e ∈ s, e = 0) :
    ((s.foldl (fun (acc : Int × List Int) e => (acc.1 + e, acc.2 ++ [acc.1])) (0, out)).2) = out ++ List.replicate s.length 0 := by
  induction s generalizing out with
  | nil => simp
  | cons e s ih =>
    have he : e = 0 := hs e List.mem_cons_self
    have hsTail : ∀ x ∈ s, x = 0 := fun x hx => hs x (List.mem_cons_of_mem e hx)
    have hstep : (fun (acc : Int × List Int) e => (acc.1 + e, acc.2 ++ [acc.1])) (0, out) e = (0, out ++ [0]) := by
      rw [he]
      rfl
    simp only [List.foldl_cons, hstep]
    rw [ih (out ++ [0]) hsTail]
    simp [List.append_assoc, List.replicate_succ]

private theorem gen_prefix_replicate_zero (n : Nat) :
    (((List.replicate n (0 : Int)).foldl (fun (acc : Int × List Int) e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2) = List.replicate n 0 := by
  have h := gen_prefix_replicate_zero_aux (List.replicate n 0) [] (fun e he => (List.mem_replicate.mp he).2)
  simpa using h

theorem runHooksShift_plain (P : Params) (cg : Graph) (labels : List MeasuredLabel) :
    RunHooksShift P (sizeProperPorts P) (fun _ _ ys top => .ok (ys, top)) [] cg labels where
  shifts := fun p layers ys top ys' top' h => by
    have hpair : (ys, top) = (ys', top') := Except.ok.inj h
    refine ⟨List.replicate top.length 0, List.replicate top.length 0, by simp, fun e he => ?_, (gen_prefix_replicate_zero _).symm, ?_, ?_, ?_⟩
    · rw [List.mem_replicate] at he
      obtain ⟨_, rfl⟩ := he
      omega
    · simp
    · intro r hr
      cases hpair
      have h0 : (List.replicate top.length 0).getD r (0 : Int) = 0 := by
        show (((List.replicate top.length 0)[r]?).getD (0 : Int)) = 0
        rw [List.getElem?_replicate_of_lt hr]
        rfl
      omega
    · intro j hj
      cases hpair
      have hidx : (List.replicate top.length 0).getD ((p.rank.getD j 0).toNat) (0 : Int) = 0 := by
        show (((List.replicate top.length 0)[(p.rank.getD j 0).toNat]?).getD (0 : Int)) = 0
        by_cases hlt : (p.rank.getD j 0).toNat < top.length
        · rw [List.getElem?_replicate_of_lt hlt]
          rfl
        · rw [List.getElem?_eq_none (by rw [List.length_replicate]; omega)]
          decide
      rw [hidx]
      omega
  bands := by
    intro run orderOptions hgen
    obtain ⟨ranks, p0, labeled, q0, y_pre, top_pre, ys_pre, hn, hl, hcoord, hord, hcross, hproxy, hdrop, hroute, hr2, hry, hyspre, hres, hcy, hroutes, hexact⟩ := componentRunGen_spec hgen
    have hpair : (ys_pre, top_pre) = (run.ys, run.top) := Except.ok.inj hres
    have hysEq : ys_pre = run.ys := congrArg Prod.fst hpair
    have htopEq : top_pre = run.top := congrArg Prod.snd hpair
    have heq : coordinateGen (sizeProperPorts P) P labeled = coordinateGraph P labeled := rfl
    rw [heq] at hcoord
    have hylen : y_pre.length = run.coordinateProper.nodes.length := (CoordsImpl.rankCoordsWith_length hry).1
    constructor
    · intro r l v hly hvIn hvn hrk
      have hband := CoordsImpl.rankAxis_node_in_band hry hly hvIn hvn hrk
      have hvY : v < y_pre.length := by rw [hylen]; exact hvn
      obtain ⟨nd, hnd⟩ : ∃ nd, run.coordinateProper.nodes[v]? = some nd :=
        ⟨_, List.getElem?_eq_getElem hvn⟩
      have hcg : (coordinateGraph P labeled).nodes[v]? = some nd := by rw [hcoord]; exact hnd
      have hraw : ys_pre.getD v 0 =
          (if nd.node.border == -2 then top_pre.getD (rk run.coordinateProper.rank v).toNat 0
            else if nd.node.border == 2 then top_pre.getD (rk run.coordinateProper.rank v).toNat 0 +
              CoordsImpl.layerHeight run.coordinateProper (run.layers.getD (rk run.coordinateProper.rank v).toNat [])
            else y_pre.getD v 0) := by
        rw [← hyspre]
        exact proxyYs_getD run.coordinateProper run.layers top_pre y_pre hnd hvY
      have hLH : 0 ≤ CoordsImpl.layerHeight run.coordinateProper l := CoordsImpl.layerHeight_nonneg _ _
      have hrkn : (rk run.coordinateProper.rank v).toNat = r := by rw [hrk]; rfl
      by_cases hbm2 : nd.node.border = -2
      · have hflat : nd.node.h = 0 := pc_frame_flat hcg (Or.inl hbm2)
        have hbeq : (nd.node.border == -2) = true := by rw [hbm2]; rfl
        rw [hbeq] at hraw
        simp only [reduceIte] at hraw
        have hnodeH : CoordsImpl.nodeH run.coordinateProper v = 0 := by
          simp only [CoordsImpl.nodeH, hnd, hflat]
        rw [hrkn, hysEq, htopEq] at hraw
        omega
      · by_cases hb2 : nd.node.border = 2
        · have hflat : nd.node.h = 0 := pc_frame_flat hcg (Or.inr hb2)
          have hbeqF : (nd.node.border == -2) = false := by simp [hbm2]
          have hbeqT : (nd.node.border == 2) = true := by rw [hb2]; rfl
          rw [hbeqF] at hraw
          simp only [Bool.false_eq_true, reduceIte] at hraw
          rw [hbeqT] at hraw
          simp only [reduceIte] at hraw
          have hnodeH : CoordsImpl.nodeH run.coordinateProper v = 0 := by
            simp only [CoordsImpl.nodeH, hnd, hflat]
          have hgetL : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = l := by
            rw [hrkn, List.getD_eq_getElem?_getD, hly]
            rfl
          rw [hgetL, hrkn, hysEq, htopEq] at hraw
          omega
        · have hbeqF : (nd.node.border == -2) = false := by simp [hbm2]
          have hbeqF2 : (nd.node.border == 2) = false := by simp [hb2]
          rw [hbeqF] at hraw
          simp only [Bool.false_eq_true, reduceIte] at hraw
          rw [hbeqF2] at hraw
          simp only [Bool.false_eq_true, reduceIte] at hraw
          rw [hysEq] at hraw
          rw [htopEq] at hband
          omega
    · intro r r' l l' hlt hly hly'
      have hdisj := CoordsImpl.rankAxis_bands_disjoint hry r r' l l' hlt hly hly'
      rw [htopEq] at hdisj
      exact hdisj

private theorem gen_extra_step_preserves (acc : List Int) (m : Nat) (needed : Int)
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

private theorem gen_foldl_preserves (step : List Int → (Node × Nat) → List Int)
    (topLen : Nat)
    (hstep : ∀ acc q, acc.length = topLen → (∀ i, 0 ≤ acc.getD i 0) →
      (step acc q).length = topLen ∧ ∀ i, 0 ≤ (step acc q).getD i 0)
    (xs : List (Node × Nat)) (acc : List Int)
    (hlen : acc.length = topLen) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (xs.foldl step acc).length = topLen ∧ ∀ i, 0 ≤ (xs.foldl step acc).getD i 0 := by
  induction xs generalizing acc with
  | nil => exact ⟨hlen, hpos⟩
  | cons q xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hlen', hpos'⟩ := hstep acc q hlen hpos
    exact ih _ hlen' hpos'

private theorem gen_extra_step_concrete (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int)
    (acc : List Int) (q : Node × Nat)
    (hlen : acc.length = top.length) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (if !exact.contains q.1.decl then acc
      else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
      else acc.set ((p.rank.getD q.2 0).toNat)
        (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
          (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length * Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 - heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
      ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
        else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
        else acc.set ((p.rank.getD q.2 0).toNat)
          (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
            (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length * Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 - heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
  by_cases h1 : (!exact.contains q.1.decl) = true
  · rw [ite_eq_left h1]
    exact ⟨hlen, hpos⟩
  · rw [ite_eq_right h1]
    by_cases h2 : (loopSizes cg.edges labels q.2 cg.slot).isEmpty = true
    · rw [ite_eq_left h2]
      exact ⟨hlen, hpos⟩
    · rw [ite_eq_right h2]
      obtain ⟨hlen', hpos'⟩ := gen_extra_step_preserves acc _ _ hpos
      exact ⟨hlen'.trans hlen, hpos'⟩

private theorem gen_extra_fold (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int) :
    let extra := cg.nodes.zipIdx.foldl (fun (acc : List Int) (q : Node × Nat) =>
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
    · have hg : (List.replicate top.length (0 : Int))[i]? = some (0 : Int) := by
        rw [List.getElem?_eq_getElem (by simpa using h)]
        simp
      rw [List.getD_eq_getElem?_getD, hg]
      simp
    · have hg : (List.replicate top.length (0 : Int))[i]? = none :=
        List.getElem?_eq_none_iff.mpr (by simpa using Nat.le_of_not_gt h)
      rw [List.getD_eq_getElem?_getD, hg]
      simp
  have hstep : ∀ (acc : List Int) (q : Node × Nat), acc.length = top.length → (∀ i, 0 ≤ acc.getD i 0) →
      (if !exact.contains q.1.decl then acc
        else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
        else acc.set ((p.rank.getD q.2 0).toNat)
          (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
            (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length * Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 - heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
        ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
          else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
          else acc.set ((p.rank.getD q.2 0).toNat)
            (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
              (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length * Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 - heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
    intro acc q hlen hpos
    exact gen_extra_step_concrete cg exact labels p ys top heights acc q hlen hpos
  have h := gen_foldl_preserves (fun (acc : List Int) (q : Node × Nat) =>
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

private theorem gen_prefix_length (extra : List Int) (s : Int) (out : List Int) :
    ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).length =
      out.length + extra.length := by
  induction extra generalizing s out with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

theorem runHooksShift_exact (P : Params) (exactIds : List String) (inp : Input) (cg : Graph) (labels : List MeasuredLabel) :
    RunHooksShift P (sizeProperPortsX P (exactDecls exactIds inp)) (reserveExactRanks cg (exactDecls exactIds inp) labels) (cg.nodes.zipIdx.filterMap fun q => if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none) cg labels where
  shifts := fun p layers ys top ys' top' h => by
    unfold reserveExactRanks at h
    obtain ⟨topNew, htopM, h1⟩ := bind_ok h
    obtain ⟨ysNew, hysM, h2⟩ := bind_ok h1
    have hpair : (ysNew, topNew) = (ys', top') := Except.ok.inj h2
    have htopNew_eq : topNew = top' := congrArg Prod.snd hpair
    have hysNew_eq : ysNew = ys' := congrArg Prod.fst hpair
    rw [htopNew_eq] at htopM
    rw [hysNew_eq] at hysM
    have hExtra := gen_extra_fold cg (exactDecls exactIds inp) labels p ys top (layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH p v)) 0)
    obtain ⟨hlenExtra, hposExtra⟩ := hExtra
    refine ⟨_, _, hlenExtra, ?_, rfl, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
      have h2 := hposExtra i
      rw [List.getD_eq_getElem?_getD, hi] at h2
      simpa using h2
    · rw [gen_prefix_length _ 0 _, hlenExtra]
      simp
    · intro r hr
      have hrZ : r < (top.zipIdx).length := by
        rw [List.length_zipIdx]
        exact hr
      have hzin : (top.zipIdx)[r]? = some (top[r], r) := by
        have h1 : top[r]? = some top[r] := List.getElem?_eq_getElem hr
        simp [List.getElem?_zipIdx, h1]
      obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
      obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
      have hbeq : b = top[r] + ((((cg.nodes.zipIdx.foldl (fun acc q =>
        if !(exactDecls exactIds inp).contains q.1.decl then acc
        else
          let sizes := loopSizes cg.edges labels q.2 cg.slot
          if sizes.isEmpty then acc
          else
            let rank := (p.rank.getD q.2 0).toNat
            let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
            let needed := ys.getD q.2 0 + reserved - top.getD rank 0 - (layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH p v)) 0).getD rank 0
            acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top.length (0 : Int))).foldl
        (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD r 0) :=
        Measure.checkedI32_ok hb
      have h1 : top[r]? = some top[r] := List.getElem?_eq_getElem hr
      have e3 : top.getD r 0 = top[r] := by
        rw [List.getD_eq_getElem?_getD, h1]
        rfl
      have e4 : top'.getD r 0 = b := by
        rw [List.getD_eq_getElem?_getD, hbr]
        rfl
      rw [e4, e3]
      exact hbeq
    · intro j hj
      have hjZ : j < (ys.zipIdx).length := by
        rw [List.length_zipIdx]
        exact hj
      have hzin : (ys.zipIdx)[j]? = some (ys[j], j) := by
        have h1 : ys[j]? = some ys[j] := List.getElem?_eq_getElem hj
        simp [List.getElem?_zipIdx, h1]
      obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ hysM
      obtain ⟨b, hb, hbr⟩ := hidx j _ hzin
      have hbeq : b = ys[j] + ((((cg.nodes.zipIdx.foldl (fun acc q =>
        if !(exactDecls exactIds inp).contains q.1.decl then acc
        else
          let sizes := loopSizes cg.edges labels q.2 cg.slot
          if sizes.isEmpty then acc
          else
            let rank := (p.rank.getD q.2 0).toNat
            let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
            let needed := ys.getD q.2 0 + reserved - top.getD rank 0 - (layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH p v)) 0).getD rank 0
            acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top.length (0 : Int))).foldl
        (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD ((p.rank.getD j 0).toNat) 0) :=
        Measure.checkedI32_ok hb
      have h1 : ys[j]? = some ys[j] := List.getElem?_eq_getElem hj
      have e3 : ys.getD j 0 = ys[j] := by
        rw [List.getD_eq_getElem?_getD, h1]
        rfl
      have e4 : ys'.getD j 0 = b := by
        rw [List.getD_eq_getElem?_getD, hbr]
        rfl
      rw [e4, e3]
      exact hbeq
  bands := by
    intro run orderOptions hgen
    have hX : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run := by
      rw [componentRunX_eq_gen]
      exact hgen
    exact X_ReserveBands_holds exactIds hX
theorem componentRunGen_positions_disjoint
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions} {exactOut : List Nat}
    {sizeHook : Proper → Proper} {reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)}
    (hshift : RunHooksShift P sizeHook reserveHook exactOut cg labels)
    (hrun : componentRunGen P sizeHook reserveHook exactOut cg labels orderOptions = .ok run)
    {u v : Nat} {nodeU nodeV : Node}
    (hnodeU : cg.nodes[u]? = some nodeU)
    (hnodeV : cg.nodes[v]? = some nodeV)
    (hbU : nodeU.border = 0) (hbV : nodeV.border = 0) (hne : u ≠ v)
    (hcovered : ∀ i, i < cg.nodes.length → i < run.proper.nodes.length)
    (hrecU : ∃ actualU : ProperNode, run.coordinateProper.nodes[u]? = some actualU ∧ run.proper.nodes[u]? = some actualU ∧ actualU.node.border = 0)
    (hrecV : ∃ actualV : ProperNode, run.coordinateProper.nodes[v]? = some actualV ∧ run.proper.nodes[v]? = some actualV ∧ actualV.node.border = 0)
    (hSep : ∀ (layer : List Nat) (i j a b : Nat) (first second : ProperNode),
      layer ∈ run.layers → i < j → layer[i]? = some a → layer[j]? = some b →
      run.coordinateProper.nodes[a]? = some first → run.coordinateProper.nodes[b]? = some second →
      ¬(first.node.border = -2 ∨ first.node.border = 2) → ¬(second.node.border = -2 ∨ second.node.border = 2) →
      RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤ RouteImpl.leftOf run.proper run.xs b) :
    Disjoint (frameRect P cg run u) (frameRect P cg run v) := by
  obtain ⟨actualU, hcoordU, hpropU, hbU0⟩ := hrecU
  obtain ⟨actualV, hcoordV, hpropV, hbV0⟩ := hrecV
  have hu' : u < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeU).1
  have hv' : v < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeV).1
  have huP : u < run.proper.nodes.length := hcovered u hu'
  have hvP : v < run.proper.nodes.length := hcovered v hv'
  have hgetU : cg.nodes.getD u default = nodeU := by
    rw [List.getD_eq_getElem?_getD, hnodeU]
    rfl
  have hgetV : cg.nodes.getD v default = nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hframeU : frameRect P cg run u = nodeRect cg run u := by
    unfold frameRect
    simp only []
    rw [hgetU, hbU]
    rfl
  have hframeV : frameRect P cg run v = nodeRect cg run v := by
    unfold frameRect
    simp only []
    rw [hgetV, hbV]
    rfl
  rw [hframeU, hframeV]
  have hrectU : nodeRect cg run u =
      ⟨run.xs.getD u 0 - Int.fdiv actualU.node.w 2, run.ys.getD u 0,
        actualU.node.w, actualU.node.h⟩ := by
    simp [nodeRect, hpropU]
  have hrectV : nodeRect cg run v =
      ⟨run.xs.getD v 0 - Int.fdiv actualV.node.w 2, run.ys.getD v 0,
        actualV.node.w, actualV.node.h⟩ := by
    simp [nodeRect, hpropV]
  obtain ⟨ranks, p0, labeled, q0, y_pre, top_pre, ys_pre, hn, hl, hcoord, hord, hcross, hproxy, hdrop, hroute, hr2, hry, hyspre, hres, hcy, hroutes, hexact⟩ := componentRunGen_spec hrun
  obtain ⟨hinBand, hdisjBands⟩ := hshift.bands hrun
  obtain ⟨ord, hordOk, hordLayers⟩ := hord
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hrank, hqlen, _, _, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have huC : u < run.coordinateProper.nodes.length := by omega
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact hrank
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨lU, hlyU, huIn, hrkU⟩ := hcov u huP
  obtain ⟨lV, hlyV, hvIn, hrkV⟩ := hcov v hvP
  let rU : Nat := (rk run.proper.rank u).toNat
  let rV : Nat := (rk run.proper.rank v).toNat
  have hrkU' : rk run.proper.rank u = (rU : Int) := by
    have h := Int.toNat_of_nonneg hrkU
    exact h.symm
  have hrkV' : rk run.proper.rank v = (rV : Int) := by
    have h := Int.toNat_of_nonneg hrkV
    exact h.symm
  have hrkCoordU : rk run.coordinateProper.rank u = (rU : Int) := by
    rw [← hranks]; exact hrkU'
  have hrkCoordV : rk run.coordinateProper.rank v = (rV : Int) := by
    rw [← hranks]; exact hrkV'
  have hlyU' : run.layers[rU]? = some lU := hlyU
  have hlyV' : run.layers[rV]? = some lV := hlyV
  rcases Nat.lt_trichotomy rU rV with hlt | heq | hgt
  · have hbandU := hinBand rU lU u hlyU' huIn huC hrkCoordU
    have hbandV := hinBand rV lV v hlyV' hvIn hvC hrkCoordV
    have hbands := hdisjBands rU rV lU lV hlt hlyU' hlyV'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega
  · rw [heq] at hlyU'
    obtain hlVeq : lV = lU := Option.some.inj (hlyV'.symm.trans hlyU')
    rw [hlVeq] at hvIn
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp huIn
    obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hvIn
    have hnePV : pu ≠ pv := by
      intro heq'
      subst heq'
      exact hne (Option.some.inj (hpu.symm.trans hpv))
    have hlayerMem : lU ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyU'
      rw [← hmemEq]
      exact List.getElem_mem hmemLT
    rcases Nat.lt_or_gt_of_ne hnePV with hplt | hpgt
    · have hsep := hSep lU pu pv u v actualU actualV hlayerMem hplt hpu hpv hcoordU hcoordV
        (by simp [hbU0]) (by simp [hbV0])
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
    · have hsep := hSep lU pv pu v u actualV actualU hlayerMem hpgt hpv hpu hcoordV hcoordU
        (by simp [hbV0]) (by simp [hbU0])
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
  · have hbandU := hinBand rU lU u hlyU' huIn huC hrkCoordU
    have hbandV := hinBand rV lV v hlyV' hvIn hvC hrkCoordV
    have hbands := hdisjBands rV rU lV lU hgt hlyV' hlyU'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

theorem componentRunGen_positions_disjoint_plain
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {index : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp index) labels orderOptions =
      .ok run)
    {u v : Nat} {nodeU nodeV : Node}
    (hnodeU : (componentCandidate graph comp index).nodes[u]? = some nodeU)
    (hnodeV : (componentCandidate graph comp index).nodes[v]? = some nodeV)
    (hbU : nodeU.border = 0) (hbV : nodeV.border = 0) (hne : u ≠ v) :
    Disjoint (frameRect P (componentCandidate graph comp index) run u)
      (frameRect P (componentCandidate graph comp index) run v) := by
  let cg := componentCandidate graph comp index
  have hrunGen : componentRunGen P (sizeProperPorts P) (fun _ _ ys top => .ok (ys, top)) [] cg labels orderOptions = .ok run := by
    rw [← componentRun_eq_gen]
    exact hrun
  have hcovered := componentRun_original_nodes_covered hrun
  obtain ⟨actualU, hcoordU, hpropU, _, hbU0, _, _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnodeU hbU
  obtain ⟨actualV, hcoordV, hpropV, _, hbV0, _, _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnodeV hbV
  exact componentRunGen_positions_disjoint (runHooksShift_plain P cg labels) hrunGen
    hnodeU hnodeV hbU hbV hne hcovered
    ⟨actualU, hcoordU, hpropU, hbU0⟩ ⟨actualV, hcoordV, hpropV, hbV0⟩
    (fun layer i j a b first second hmem hij ha hb hf hs hb1 hb2 =>
      componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hmem hij ha hb hf hs hb1 hb2)

theorem componentRunX_positions_disjoint
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {u v : Nat} {nodeU nodeV : Node}
    (hnodeU : cg.nodes[u]? = some nodeU)
    (hnodeV : cg.nodes[v]? = some nodeV)
    (hbU : nodeU.border = 0) (hbV : nodeV.border = 0) (hne : u ≠ v)
    (hcovered : ∀ i, i < cg.nodes.length → i < run.proper.nodes.length)
    (hrecU : ∃ actualU : ProperNode, run.coordinateProper.nodes[u]? = some actualU ∧ run.proper.nodes[u]? = some actualU ∧ actualU.node.border = 0)
    (hrecV : ∃ actualV : ProperNode, run.coordinateProper.nodes[v]? = some actualV ∧ run.proper.nodes[v]? = some actualV ∧ actualV.node.border = 0)
    (hSep : ∀ (layer : List Nat) (i j a b : Nat) (first second : ProperNode),
      layer ∈ run.layers → i < j → layer[i]? = some a → layer[j]? = some b →
      run.coordinateProper.nodes[a]? = some first → run.coordinateProper.nodes[b]? = some second →
      ¬(first.node.border = -2 ∨ first.node.border = 2) → ¬(second.node.border = -2 ∨ second.node.border = 2) →
      RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤ RouteImpl.leftOf run.proper run.xs b) :
    Disjoint (frameRect P cg run u) (frameRect P cg run v) := by
  have hrunGen : componentRunGen P (sizeProperPortsX P (exactDecls exactIds inp)) (reserveExactRanks cg (exactDecls exactIds inp) labels) (cg.nodes.zipIdx.filterMap fun q => if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none) cg labels orderOptions = .ok run := by
    rw [← componentRunX_eq_gen]
    exact hrun
  exact componentRunGen_positions_disjoint (runHooksShift_exact P exactIds inp cg labels) hrunGen hnodeU hnodeV hbU hbV hne hcovered hrecU hrecV hSep

theorem reserveShift_prefix_pairwise (es : List Int) (hpos : ∀ e ∈ es, 0 ≤ e)
    (s : Int) (out : List Int)
    (hm : out.Pairwise (· ≤ ·)) (hle : ∀ x ∈ out, x ≤ s) :
    ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).Pairwise
      (· ≤ ·) := by
  induction es generalizing s out with
  | nil => simpa
  | cons e es ih =>
    have he : 0 ≤ e := hpos e List.mem_cons_self
    simp only [List.foldl_cons]
    apply ih
    · intro e' he'
      exact hpos e' (List.mem_cons_of_mem e he')
    · apply List.pairwise_append.mpr
      refine ⟨hm, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      rw [hy]
      exact hle x hx
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have := hle x hx
        omega
      · omega

theorem componentRunGen_shift_values
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions} {exactOut : List Nat}
    {sizeHook : Proper → Proper} {reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)}
    (hshift : RunHooksShift P sizeHook reserveHook exactOut cg labels)
    (hrun : componentRunGen P sizeHook reserveHook exactOut cg labels orderOptions = .ok run) :
    ∃ (top_pre ys_pre : List Int) (extra shifts : List Int),
      reserveHook run.coordinateProper run.layers ys_pre top_pre = .ok (run.ys, run.top) ∧
      extra.length = top_pre.length ∧ (∀ e ∈ extra, 0 ≤ e) ∧
      shifts = (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2 ∧
      shifts.length = top_pre.length ∧
      (∀ r, r < top_pre.length → run.top.getD r 0 = top_pre.getD r 0 + shifts.getD r 0) ∧
      (∀ j, j < ys_pre.length → run.ys.getD j 0 = ys_pre.getD j 0 + shifts.getD ((run.coordinateProper.rank.getD j 0).toNat) 0) := by
  obtain ⟨ranks, p0, labeled, q0, _, top_pre, ys_pre, hn, hl, hcoord, hord, hcross, hproxy, hdrop, hroute, hr2, hry, hyspre, hres, hcy, hroutes, hexact⟩ := componentRunGen_spec hrun
  obtain ⟨extra, shifts, hlen, hnn, hpref, hlenS, htop, hys⟩ := hshift.shifts run.coordinateProper run.layers ys_pre top_pre run.ys run.top hres
  exact ⟨top_pre, ys_pre, extra, shifts, hres, hlen, hnn, hpref, hlenS, htop, hys⟩

theorem componentRunGen_rank_step_lower
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exactOut : List Nat}
    {sizeHook : Proper → Proper}
    {reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)}
    (hshift : RunHooksShift P sizeHook reserveHook exactOut cg labels)
    (hrun : componentRunGen P sizeHook reserveHook exactOut cg labels orderOptions = .ok run)
    {k : Nat} (hk : k + 1 < run.layers.length) :
    run.top.getD k 0 + (run.layers.map (RouteImpl.layerHeight run.proper)).getD k 0 +
      CoordsImpl.rankGapAt P.rankGap run.proper run.layers k +
      P.slot * (run.lanes.routing.gaps.getD k default).slots ≤ run.top.getD (k + 1) 0 := by
  obtain ⟨ranks, p0, labeled, q0, y_pre, top_pre, ys_pre, hn, hl, hcoord, hord, hcross,
    hproxy, hdrop, hroute, hrouting, hry, hyspre, hres, hcy, hroutes, hexact⟩ :=
    componentRunGen_spec hrun
  obtain ⟨extra, shifts, hlen, hnn, hpref, hlenS, htop, hys⟩ :=
    hshift.shifts run.coordinateProper run.layers ys_pre top_pre run.ys run.top hres
  have htopLen : top_pre.length = run.layers.length := (CoordsImpl.rankCoordsWith_length hry).2
  obtain ⟨_, _, hslotsLen, _, _, htopPre, _⟩ := CoordsImpl.rankCoordsWith_spec hry
  obtain ⟨_, _, _, _, hgl, _, _⟩ := RouteImpl.routeWithLanes_geometry hroute
  have hgap : k < run.lanes.routing.gaps.length := by omega
  have hslot : (run.lanes.routing.gaps.map (·.slots)).getD k 0 =
      (run.lanes.routing.gaps.getD k default).slots := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hgap]
  have hss : (run.routing.gaps.map (·.slots)).length + 1 = run.layers.length := by
    simp only [List.length_map] at hslotsLen ⊢
    omega
  have hshiftPair : shifts.Pairwise (· ≤ ·) := by
    rw [hpref]
    exact reserveShift_prefix_pairwise extra hnn 0 [] (by simp) (by simp)
  have hshiftNext : shifts.getD k 0 ≤ shifts.getD (k + 1) 0 := by
    have hi : k < shifts.length := by omega
    have hj : k + 1 < shifts.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simp only [Option.getD_some]
    exact hshiftPair.rel_getElem_of_lt hi hj (by omega)
  have hpreStep := rankSteps_topsFrom_step P.rankGap P.slot run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)) 0 k hss hk
  rw [← htopPre, ← hrouting, hslot] at hpreStep
  have hnodeH : ∀ v, RouteImpl.nodeH run.proper v = RouteImpl.nodeH run.coordinateProper v := by
    intro v
    have hn : run.proper.nodes = q0.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
    have heq : RouteImpl.nodeH run.proper v = RouteImpl.nodeH q0 v := by
      unfold RouteImpl.nodeH
      rw [hn]
    exact heq.trans (nodeH_proxy hproxy v)
  have hLH : ∀ l, RouteImpl.layerHeight run.proper l =
      CoordsImpl.layerHeight run.coordinateProper l := by
    intro l
    have hf : RouteImpl.nodeH run.proper = RouteImpl.nodeH run.coordinateProper := funext hnodeH
    simp only [RouteImpl.layerHeight, hf]
    rfl
  have hmap : run.layers.map (RouteImpl.layerHeight run.proper) =
      run.layers.map (CoordsImpl.layerHeight run.coordinateProper) := by
    exact List.map_congr_left (fun l _ => hLH l)
  have hRG : CoordsImpl.rankGapAt P.rankGap run.proper run.layers k =
      CoordsImpl.rankGapAt P.rankGap run.coordinateProper run.layers k := by
    rw [← hdrop]
    exact rankGapAt_proxy hproxy _ _ _
  rw [hmap, hRG, htop k (by omega), htop (k + 1) (by omega)]
  omega

theorem componentRunGen_node_band
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions} {exactOut : List Nat}
    {sizeHook : Proper → Proper} {reserveHook : Proper → List (List Nat) → List Int → List Int → Except LayoutError (List Int × List Int)}
    (hshift : RunHooksShift P sizeHook reserveHook exactOut cg labels)
    (hrun : componentRunGen P sizeHook reserveHook exactOut cg labels orderOptions = .ok run)
    {q : Nat} {nd : ProperNode} (hq : run.proper.nodes[q]? = some nd)
    (hrec : ∃ cw : ProperNode, run.coordinateProper.nodes[q]? = some cw ∧ cw.node.border = nd.node.border ∧ cw.node.h = nd.node.h) :
    ∃ l : List Nat,
      run.layers[(rk run.coordinateProper.rank q).toNat]? = some l ∧
      run.top.getD (rk run.coordinateProper.rank q).toNat 0 ≤ run.ys.getD q 0 ∧
      run.ys.getD q 0 + RouteImpl.nodeH run.proper q ≤
        run.top.getD (rk run.coordinateProper.rank q).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper l := by
  obtain ⟨cw, hcw, _, hheightEq⟩ := hrec
  obtain ⟨ranks, p0, labeled, q0, y_pre, top_pre, ys_pre, hn, hl, hcoord, hord, hcross, hproxy, hdrop, hroute, hr2, hry, hyspre, hres, hcy, hroutes, hexact⟩ := componentRunGen_spec hrun
  obtain ⟨hinBand, _⟩ := hshift.bands hrun
  obtain ⟨_, hrank, hqlen, _, _, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact hrank
  have hqP : q < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hq).1
  have hvn : q < run.coordinateProper.nodes.length := by
    rw [← hnodesLen]; exact hqP
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_len, _sz, _members, hcov, _edges⟩ :=
    RouteImpl.layersOk_spec hlayersOk
  obtain ⟨l, hly, hqIn, hrkNN⟩ := hcov q hqP
  have hrkNNcp : 0 ≤ rk run.coordinateProper.rank q := by
    rw [← hranks]; exact hrkNN
  have hlycp : run.layers[(rk run.coordinateProper.rank q).toNat]? = some l := by
    rw [← hranks]; exact hly
  have hrk : rk run.coordinateProper.rank q = ((rk run.coordinateProper.rank q).toNat : Int) := by
    have h := Int.toNat_of_nonneg hrkNNcp
    exact h.symm
  have hband := hinBand ((rk run.coordinateProper.rank q).toNat) l q hlycp hqIn hvn hrk
  have hnodeHcp : CoordsImpl.nodeH run.coordinateProper q = cw.node.h := by
    simp only [CoordsImpl.nodeH, hcw]
  have hnodeH : RouteImpl.nodeH run.proper q = cw.node.h := by
    simp only [RouteImpl.nodeH, hq, hheightEq]
  rw [hnodeHcp, ← hnodeH] at hband
  exact ⟨l, hlycp, hband.1, hband.2⟩

theorem componentRunGen_node_band_plain
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {q : Nat} {nd : ProperNode} (hq : run.proper.nodes[q]? = some nd) :
    ∃ l : List Nat,
      run.layers[(rk run.coordinateProper.rank q).toNat]? = some l ∧
      run.top.getD (rk run.coordinateProper.rank q).toNat 0 ≤ run.ys.getD q 0 ∧
      run.ys.getD q 0 + RouteImpl.nodeH run.proper q ≤
        run.top.getD (rk run.coordinateProper.rank q).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper l := by
  have hrunGen : componentRunGen P (sizeProperPorts P) (fun _ _ ys top => .ok (ys, top)) [] cg labels orderOptions = .ok run := by
    rw [← componentRun_eq_gen]
    exact hrun
  obtain ⟨cw, hcw, hborder, hheight⟩ := run_record_source hrun hq
  exact componentRunGen_node_band (runHooksShift_plain P cg labels) hrunGen hq ⟨cw, hcw, hborder, hheight⟩

theorem componentRunX_node_band
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {q : Nat} {nd : ProperNode} (hq : run.proper.nodes[q]? = some nd)
    (hrec : ∃ cw : ProperNode, run.coordinateProper.nodes[q]? = some cw ∧ cw.node.border = nd.node.border ∧ cw.node.h = nd.node.h) :
    ∃ l : List Nat,
      run.layers[(rk run.coordinateProper.rank q).toNat]? = some l ∧
      run.top.getD (rk run.coordinateProper.rank q).toNat 0 ≤ run.ys.getD q 0 ∧
      run.ys.getD q 0 + RouteImpl.nodeH run.proper q ≤
        run.top.getD (rk run.coordinateProper.rank q).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper l := by
  have hrunGen : componentRunGen P (sizeProperPortsX P (exactDecls exactIds inp)) (reserveExactRanks cg (exactDecls exactIds inp) labels) (cg.nodes.zipIdx.filterMap fun q => if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none) cg labels orderOptions = .ok run := by
    rw [← componentRunX_eq_gen]
    exact hrun
  exact componentRunGen_node_band (runHooksShift_exact P exactIds inp cg labels) hrunGen hq hrec

theorem componentRunX_node_rank_band
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {u : Nat} (hu : u < run.proper.nodes.length) :
    ∃ l, run.layers[(rk run.proper.rank u).toNat]? = some l ∧
      0 ≤ rk run.proper.rank u ∧
      run.top.getD (rk run.proper.rank u).toNat 0 ≤ run.ys.getD u 0 ∧
      run.ys.getD u 0 + RouteImpl.nodeH run.proper u ≤
        run.top.getD (rk run.proper.rank u).toNat 0 + CoordsImpl.layerHeight run.coordinateProper l := by
  have hrunG : componentRunGen P (sizeProperPortsX P (exactDecls exactIds inp))
      (reserveExactRanks cg (exactDecls exactIds inp) labels)
      (cg.nodes.zipIdx.filterMap fun q => if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none)
      cg labels orderOptions = .ok run := by
    rw [← componentRunX_eq_gen]
    exact hrun
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, hr, _, _⟩ := componentRunX_spec hrun
  obtain ⟨_, hrank, hlen, _, hlookup, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by rw [← hdrop]; exact hrank
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  obtain ⟨_, _, _, hcovered, _⟩ := RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hr).1
  obtain ⟨_, _, _, hnn⟩ := hcovered u hu
  have hc : u < run.coordinateProper.nodes.length := by rw [← hlen, ← hnodes]; exact hu
  obtain ⟨coord, hcoord⟩ : ∃ nd, run.coordinateProper.nodes[u]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hc⟩
  obtain ⟨routed, hrouted, _, hb, hh⟩ := hlookup u coord hcoord
  have hn : run.proper.nodes[u]? = some routed := by rw [hnodes]; exact hrouted
  obtain ⟨l, hl, hlo, hhi⟩ := componentRunGen_node_band
    (runHooksShift_exact P exactIds inp cg labels) hrunG hn ⟨coord, hcoord, hb.symm, hh.symm⟩
  rw [← hranks] at hl hlo hhi
  exact ⟨l, hl, hnn, hlo, hhi⟩

theorem componentRunX_edge_rank_gap
    {P : Params} {exactIds : List String} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < run.proper.edges.length) :
    run.ys.getD (RouteImpl.edgeAt run.proper i).tail 0 +
        RouteImpl.nodeH run.proper (RouteImpl.edgeAt run.proper i).tail ≤
      run.top.getD (RouteImpl.gapOf run.proper i) 0 +
        (run.layers.map (RouteImpl.layerHeight run.proper)).getD (RouteImpl.gapOf run.proper i) 0 ∧
    run.top.getD (RouteImpl.gapOf run.proper i) 0 +
        (run.layers.map (RouteImpl.layerHeight run.proper)).getD (RouteImpl.gapOf run.proper i) 0 ≤
      run.top.getD (RouteImpl.gapOf run.proper i + 1) 0 ∧
    run.top.getD (RouteImpl.gapOf run.proper i + 1) 0 ≤
      run.ys.getD (RouteImpl.edgeAt run.proper i).head 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, hr, _, _⟩ := componentRunX_spec hrun
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  obtain ⟨_, _, _, _, hedges⟩ := RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hr).1
  let tail := (RouteImpl.edgeAt run.proper i).tail
  let head := (RouteImpl.edgeAt run.proper i).head
  have htail : tail < run.proper.nodes.length := (hedges i hi).1
  have hhead : head < run.proper.nodes.length := (hedges i hi).2.1
  have hstep : rk run.proper.rank head = rk run.proper.rank tail + 1 := (hedges i hi).2.2
  obtain ⟨tl, htl, htailNN, _, htailBottom⟩ := componentRunX_node_rank_band hrun htail
  obtain ⟨hl, hhl, _, hheadTop, _⟩ := componentRunX_node_rank_band hrun hhead
  obtain ⟨_, hdisjBands⟩ := X_ReserveBands_holds exactIds hrun
  have horders := hdisjBands _ _ tl hl (by omega) htl hhl
  have hLH : RouteImpl.layerHeight run.proper tl = CoordsImpl.layerHeight run.coordinateProper tl := by
    have heq : RouteImpl.layerHeight run.proper tl = RouteImpl.layerHeight q0 tl := by
      simp only [RouteImpl.layerHeight, RouteImpl.nodeH, hnodes]
    exact heq.trans (layerHeight_proxy hproxy tl)
  have hheight : (run.layers.map (RouteImpl.layerHeight run.proper)).getD
      (RouteImpl.gapOf run.proper i) 0 = CoordsImpl.layerHeight run.coordinateProper tl := by
    change (run.layers.map (RouteImpl.layerHeight run.proper)).getD (rk run.proper.rank tail).toNat 0 = _
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, htl, Option.map_some,
      Option.getD_some, hLH]
  have hnext : (rk run.proper.rank head).toNat = RouteImpl.gapOf run.proper i + 1 := by
    change (rk run.proper.rank head).toNat = (rk run.proper.rank tail).toNat + 1
    omega
  rw [hheight, ← hnext]
  exact ⟨htailBottom, horders, hheadTop⟩

end PipelineImpl
end Layered

end Elegant

import Elegant.IshikawaDeeperGapOnlyProof

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-! # Deeper-descendant envelope for HARD B (`HardBDeeperDescEnvelope`)

Target theorems (proved at the end of this module):
* `hardBDeeperDescEnvelope`: the residual `HardBDeeperDescEnvelope`
  (sibling-subtree envelope: time containment plus the sibling-line bound)
  holds on the executed rib, with no residual hypothesis.
* `hardBDeeperEnvTransport'''`: `HardBDeeperEnvTransport` with no residual
  hypothesis, via `hardBDeeperEnvTransport''` plus the envelope.

Proof split into named sub-lemmas:
* `descEnv_sin_run_le` / `descEnv_sin_run_ge`: slope-residual bounds for
  `run` (local copies of the private `HardBClose` lemmas).
* `descEnv_line_drop`: one falling bone-line drops at most `run + 1` over
  any sub-interval (floor analysis, no cross-line comparison).
* `descEnv_fall_lb`: an odd bone's fall over a sub-span is at least
  `run - 1` (floor analysis).
* `descEnv_start_gap`: every odd birth starts at least `run H + 3` left of
  its even parent's `x0` (reservation plus the strict draw bound).
* `descEnv_base`: the envelope invariant for the sibling `S` itself.
* `descEnv_step_even` / `descEnv_step_odd`: the invariant transports over
  one parent-child edge (even children interpolate exactly; odd children
  re-establish the margin and apply the drop/fall bounds).
* `descEnv_chain_entry`, `descEnv_trans`: ancestor-chain utilities.
* `descEnv_induct`: the invariant reaches every indexed descendant.
-/

/-- Interpolated bone-line value at ordinate `t`, matching the even-birth
attachment shape (`depthBone`). -/
def descLineOf (b : Bone) (t : Int) : Int :=
  b.x0 + Int.fdiv ((b.x1 - b.x0) * (t - b.t0)) (b.t1 - b.t0)

/-- Envelope invariant for an odd descendant bone `b` of the sibling `S`:
positive span inside `S`, and `b`'s line on or left of `S`'s line over `b`'s
own span. Future steps only ever evaluate lines at descendant slots, which
lie inside the evaluated bone's span, so pointwise domination on the bone's
own span composes. -/
def DescOddBound (S b : Bone) : Prop :=
  0 < b.t1 - b.t0 ∧ S.t0 ≤ b.t0 ∧ b.t1 ≤ S.t1 ∧
    ∀ t, b.t0 ≤ t → t ≤ b.t1 → descLineOf b t ≤ descLineOf S t

/-- Envelope invariant for an even descendant bone `b` of `S`: its point
lies inside `S`'s span and both its ends lie on or left of `S`'s line. -/
def DescEvenBound (S b : Bone) : Prop :=
  S.t0 ≤ b.t1 ∧ b.t1 ≤ S.t1 ∧
    b.x0 ≤ descLineOf S b.t1 ∧ b.x1 ≤ descLineOf S b.t1

/-- Parity-dispatched envelope invariant for a descendant bone. -/
def DescBound (S : Bone) (e : Entry) (b : Bone) : Prop :=
  if e.depth % 2 = 1 then DescOddBound S b else DescEvenBound S b

/-- Slope-residual upper bound for `run` (local copy of the private
`IshikawaClearanceHardBClose.sin_run_le`). -/
private theorem descEnv_sin_run_le (p : Params) (x : Int) (_hx : 0 ≤ x)
    (_hcos : 0 ≤ p.cos) (hsin : 1 ≤ p.sin) :
    p.sin * run p x ≤ x * p.cos := by
  unfold run
  have h := Int.mul_fdiv_add_fmod (x * p.cos) p.sin
  have h2 := Int.fmod_nonneg_of_pos (x * p.cos) (show (0 : Int) < p.sin by omega)
  omega

/-- Slope-residual lower bound for `run` (local copy of the private
`IshikawaClearanceHardBClose.sin_run_ge`). -/
private theorem descEnv_sin_run_ge (p : Params) (x : Int) (_hx : 0 ≤ x)
    (_hcos : 0 ≤ p.cos) (hsin : 1 ≤ p.sin) :
    x * p.cos - p.sin + 1 ≤ p.sin * run p x := by
  unfold run
  have h := Int.mul_fdiv_add_fmod (x * p.cos) p.sin
  have h2 := Int.fmod_lt_of_pos (x * p.cos) (show (0 : Int) < p.sin by omega)
  omega

set_option maxHeartbeats 1000000 in
/-- One falling bone-line drops at most `run + 1` over any sub-interval.
Pure floor arithmetic about a single line: no cross-line comparison. -/
private theorem descEnv_line_drop (p : Params) (hcos : 0 ≤ p.cos)
    (hsin : 1 ≤ p.sin) (x0 t0 Sp u v : Int) (hSp : 0 < Sp)
    (_hlo : t0 ≤ u) (huv : u ≤ v) :
    (x0 + Int.fdiv (-(run p Sp * (u - t0))) Sp) -
      (x0 + Int.fdiv (-(run p Sp * (v - t0))) Sp) ≤ run p (v - u) + 1 := by
  have hsin0 : 0 < p.sin := by omega
  -- Factor the numerator difference once, explicitly.
  have hCsubA : run p Sp * (v - t0) - run p Sp * (u - t0)
      = run p Sp * (v - u) := by
    simp only [Int.mul_sub]
    omega
  have e1 := Int.mul_fdiv_add_fmod (-(run p Sp * (u - t0))) Sp
  have e2 := Int.mul_fdiv_add_fmod (-(run p Sp * (v - t0))) Sp
  have rnn1 := Int.fmod_nonneg_of_pos (-(run p Sp * (u - t0))) hSp
  have rlt1 := Int.fmod_lt_of_pos (-(run p Sp * (u - t0))) hSp
  have rnn2 := Int.fmod_nonneg_of_pos (-(run p Sp * (v - t0))) hSp
  have rlt2 := Int.fmod_lt_of_pos (-(run p Sp * (v - t0))) hSp
  have hRsin : p.sin * run p Sp ≤ Sp * p.cos :=
    descEnv_sin_run_le p Sp (by omega) hcos hsin
  have hrunD : (v - u) * p.cos - p.sin + 1 ≤ p.sin * run p (v - u) :=
    descEnv_sin_run_ge p (v - u) (by omega) hcos hsin
  have hDnn : 0 ≤ v - u := by omega
  have m1 : (p.sin * run p Sp) * (v - u) ≤ (Sp * p.cos) * (v - u) :=
    Int.mul_le_mul_of_nonneg_right hRsin hDnn
  have m2 : Sp * ((v - u) * p.cos - p.sin + 1)
      ≤ Sp * (p.sin * run p (v - u)) :=
    Int.mul_le_mul_of_nonneg_left hrunD (by omega)
  have hkey : p.sin * (run p Sp * (v - u))
      ≤ p.sin * (Sp * run p (v - u) + Sp) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_comm, Int.mul_left_comm,
      Int.mul_one] at m1 m2 ⊢
    omega
  have hkey2 := Int.le_of_mul_le_mul_left hkey hsin0
  have hupper : Sp * (Int.fdiv (-(run p Sp * (u - t0))) Sp -
      Int.fdiv (-(run p Sp * (v - t0))) Sp)
      ≤ Sp * run p (v - u) + 2 * Sp - 1 := by
    simp only [Int.mul_sub] at e1 e2 rnn1 rlt1 rnn2 rlt2 hCsubA hkey2 ⊢
    omega
  have hfin : Sp * (run p (v - u) + 2) = Sp * run p (v - u) + 2 * Sp := by
    rw [Int.mul_add, Int.mul_comm Sp 2]
  have hlt : Sp * (Int.fdiv (-(run p Sp * (u - t0))) Sp -
      Int.fdiv (-(run p Sp * (v - t0))) Sp) < Sp * (run p (v - u) + 2) := by
    omega
  have hdiv := Int.lt_of_mul_lt_mul_left hlt (by omega : 0 ≤ Sp)
  omega

set_option maxHeartbeats 1000000 in
/-- An odd bone's fall over a sub-span `b ≤ S` is at least `run b - 1`.
Pure floor arithmetic about a single falling line. -/
private theorem descEnv_fall_lb (p : Params) (hcos : 0 ≤ p.cos)
    (hsin : 1 ≤ p.sin) (Sd b : Int) (hSd : 0 < Sd)
    (hb0 : 0 ≤ b) (hbSd : b ≤ Sd) :
    run p b - 1 ≤ -(Int.fdiv (-(run p Sd * b)) Sd) := by
  have hsin0 : 0 < p.sin := by omega
  have hge : Sd * p.cos - p.sin + 1 ≤ p.sin * run p Sd :=
    descEnv_sin_run_ge p Sd (by omega) hcos hsin
  have hle : p.sin * run p b ≤ b * p.cos :=
    descEnv_sin_run_le p b hb0 hcos hsin
  have g1 : b * (Sd * p.cos - p.sin + 1) ≤ b * (p.sin * run p Sd) :=
    Int.mul_le_mul_of_nonneg_left hge hb0
  have g2 : Sd * (p.sin * run p b) ≤ Sd * (b * p.cos) :=
    Int.mul_le_mul_of_nonneg_left hle (by omega)
  have hprod : b * (p.sin - 1) ≤ Sd * (p.sin - 1) :=
    Int.mul_le_mul_of_nonneg_right hbSd (by omega)
  have g3 : p.sin * (Sd * run p b) ≤ p.sin * (run p Sd * b + Sd) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_comm, Int.mul_left_comm,
      Int.mul_one] at g1 g2 hprod ⊢
    omega
  have hmain : Sd * (run p b - 1) ≤ run p Sd * b := by
    have g4 := Int.le_of_mul_le_mul_left g3 hsin0
    rw [Int.mul_sub, Int.mul_one] at ⊢
    omega
  have hbridge : -(run p Sd * b) ≤ Sd * (1 - run p b) := by
    have e : Sd * (1 - run p b) = -(Sd * (run p b - 1)) := by
      simp only [Int.mul_sub, Int.mul_one]
      omega
    rw [e]
    have c : run p Sd * b = -(-(run p Sd * b)) := by omega
    omega
  have hq : Int.fdiv (-(run p Sd * b)) Sd ≤ 1 - run p b :=
    Chart.fdiv_le_of_le_mul hSd hbridge
  omega

/-- Odd-birth attachment margin (local copy of the private
`IshikawaClearanceFacts.attachment_start_margin`). -/
private theorem descEnv_attach_start_margin (left right count drawn margin : Int)
    (hden : 0 < count + 1) (hmargin : 0 ≤ margin)
    (hreserve : (count + 1) * margin ≤ left - right)
    (hdrawn : drawn + 1 ≤ count) :
    left + Int.fdiv ((right - left) * (count - drawn)) (count + 1) + margin ≤
      left := by
  have hspan : 0 ≤ left - right :=
    Int.le_trans (Int.mul_nonneg (Int.le_of_lt hden) hmargin) hreserve
  have hmul := Int.mul_le_mul_of_nonneg_left
    (show (1 : Int) ≤ count - drawn by omega) hspan
  simp only [Int.mul_one] at hmul
  have halgebra : (right - left) * (count - drawn) =
      -((left - right) * (count - drawn)) := by
    simp only [Int.sub_mul]
    omega
  have hbound : (right - left) * (count - drawn) ≤ (count + 1) * (-margin) := by
    rw [Int.mul_neg]
    omega
  have hquot := Chart.fdiv_le_of_le_mul hden hbound
  omega

/-- Every ancestor-chain conclusion carries its own entry. -/
private theorem descEnv_chain_entry (E : List Entry) (sIdx b : Nat)
    (h : IndexedAncestor E sIdx b) : ∃ bE, E[b]? = some bE := by
  induction h with
  | edge _ child hchild _ => exact ⟨child, hchild⟩
  | tail _ _ hlook _ _ => exact ⟨_, hlook⟩

/-- Ancestor chains compose. -/
private theorem descEnv_trans {E : List Entry} {a b c : Nat}
    (hab : IndexedAncestor E a b) (hbc : IndexedAncestor E b c) :
    IndexedAncestor E a c := by
  induction hbc with
  | edge _ e he hp => exact IndexedAncestor.tail hab e he hp
  | tail _ e he hp ih => exact IndexedAncestor.tail ih e he hp

/-- The envelope invariant holds for the sibling `S` itself (equality).
Slot order plus the slot gap give `S` a positive span; pointwise domination
is reflexivity. -/
private theorem descEnv_base (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))))
    (child _j : Entry) (childIdx _jIdx : Nat) (_nj : Tree.Node)
    (frames : List Bone) (_childBorn _jBorn sBorn : Bone) (sIdx : Nat) (S : Entry)
    (nS : Tree.Node)
    (hconfig : HardBCaseConfig ns p cause k spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) child _j childIdx _jIdx _nj frames
      _childBorn _jBorn)
    (hreal : HardBRealFrames ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) placed hplace frames)
    (hS : (generatedRib ns (cause, k)).entries[sIdx]? = some S)
    (_hsne : sIdx ≠ _jIdx)
    (hSP : S.parent = ↑(child.parent).toNat)
    (_hchain : IndexedAncestor (generatedRib ns (cause, k)).entries sIdx _jIdx)
    (hsBorn : frames[sIdx + 1]? = some sBorn)
    (hnS : ns[S.node]? = some nS) :
    DescOddBound sBorn sBorn := by
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  let E := (generatedRib ns (cause, k)).entries
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw _hrun
  have hne : ns ≠ [] := by
    intro heq
    simp [heq, children] at _hcause
  have hparameters := successful_slope_parameters ns p raw hne _hrun
  obtain ⟨hchild, _hj, hodd, _hjlt, _hnj, _hlen, _hchildBorn, _hjBorn, _hspan⟩ :=
    hconfig
  obtain ⟨frames0, hshape0, hsub⟩ := hreal
  obtain ⟨hlen0, _hroot0, hrecords0⟩ := hshape0
  have hSmem : (S, sIdx) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hS
  obtain ⟨sDone, sRest, sPrefix, _⟩ := List.eq_append_cons_of_mem hSmem
  obtain ⟨sPos, sPar, sBorn0, hsPos, hsParLookup, hsBorn0, hsEq⟩ :=
    hrecords0 sDone S sIdx sRest sPrefix
  have hsBornF0 : frames0[sIdx + 1]? = some sBorn := hsub _ _ hsBorn
  have hsBornEq : sBorn0 = sBorn := Option.some.inj (hsBorn0.symm.trans hsBornF0)
  -- `S` is odd: same parent and depth as the odd route `child`.
  have hClb : -1 ≤ child.parent :=
    generated_entry_parent_lower_bound ns cause k child childIdx hchild
  have hrootFalse : child.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink _hcause child childIdx
      hchild heq
    exact hodd (by omega)
  have hCnn : 0 ≤ child.parent := by omega
  have hCParNat : child.parent = ((child.parent).toNat : Int) := by omega
  let pS := (child.parent).toNat
  have hSPeq : S.parent = (pS : Int) := hSP
  have hCParEq : child.parent = (pS : Int) := hCParNat
  have htoNat : ((pS : Int) + 1).toNat = pS + 1 := by omega
  have hParLookup : frames0[pS + 1]? = some sPar := by
    have h := hsParLookup
    rw [hSPeq, htoNat] at h
    exact h
  obtain ⟨hpsLt, _⟩ := List.getElem?_eq_some_iff.mp hParLookup
  rw [hlen0] at hpsLt
  have hEr : r.entries = E := rfl
  have hHr : r.heights = (generatedRib ns (cause, k)).heights := rfl
  have hEl : E.length = (generatedRib ns (cause, k)).entries.length := rfl
  have hErLen : r.entries.length = E.length := by rw [hEr]
  have hlen0' : frames0.length = r.entries.length + 1 := hlen0
  have hpELT : pS < E.length := by omega
  obtain ⟨pE, hpEGet⟩ : ∃ pE, E[pS]? = some pE :=
    ⟨_, List.getElem?_eq_getElem hpELT⟩
  have hpMem : (pE, pS) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hpEGet
  have hSdepth := generated_parent_child_depth ns cause k hlink _hcause
    pE S pS sIdx hpMem hSmem hSPeq
  have hCdepth := generated_parent_child_depth ns cause k hlink _hcause
    pE child pS childIdx hpMem hchild hCParEq
  have hSodd : S.depth % 2 ≠ 0 := by omega
  have hpEven : pE.depth % 2 = 0 :=
    parent_depth_even pE.depth S.depth (by omega) hSodd
  -- Parent bone of `S` is `pE`'s born bone.
  obtain ⟨pDone, pRest, pPrefix, _⟩ := List.eq_append_cons_of_mem hpMem
  obtain ⟨pPos, _pPar, pBorn, hpPosOrd, _hpParLookup, hpBornLookup, hpEq⟩ :=
    hrecords0 pDone pE pS pRest pPrefix
  have hsParEq : sPar = pBorn := by
    have h1 : frames0[pS + 1]? = some sPar := hParLookup
    exact Option.some.inj (h1.symm.trans hpBornLookup)
  -- Slot equations for `S`.
  have hSt1 : sBorn.t1 =
      Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    rw [← hsBornEq, hsEq, hsParEq]
    exact (depthBone_odd_endpoints p _ S.depth _ _ _ hSodd).2.1
  have hSt0 : sBorn.t0 = pBorn.t0 := by
    rw [← hsBornEq, hsEq, hsParEq]
    exact (depthBone_odd_endpoints p _ S.depth _ _ _ hSodd).1
  have hpT : pBorn.t0 =
      Int.fdiv (r.length * (pPos.2 + 1 : Nat)) (E.length + 1 : Nat) ∧
      pBorn.t1 =
      Int.fdiv (r.length * (pPos.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    rw [hpEq]
    exact ⟨(depthBone_even_endpoints p _ pE.depth _ _ _ hpEven).1,
      (depthBone_even_endpoints p _ pE.depth _ _ _ hpEven).2.1⟩
  -- Order: parent slot strictly precedes the odd slot.
  have hposLT : pPos.2 < sPos.2 := by
    have hord := generated_parent_child_order ns cause k pE S pS sIdx hpMem
      hSmem hSPeq pPos sPos hpPosOrd hsPos
    exact (hord.1 hpEven)
  -- Heights lower bound from the witness node.
  have hmemN : nS ∈ ns := List.mem_of_getElem? hnS
  have hdims := successful_node_dimensions ns p raw _hrun nS hmemN
  have hHbound := measured_entry_height_bound ns E S
    (List.fst_mem_of_mem_zipIdx hSmem) nS hnS
  have hH1 : 1 ≤ r.heights := by
    have hgen : r.heights = (generatedRib ns (cause, k)).heights := rfl
    have hrib := (generated_rib_fields ns cause k).2.2.2
    have hEfold : E.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 =
        (generatedRib ns (cause, k)).entries.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := rfl
    have hd1 : 1 ≤ nS.height := hdims.2
    omega
  have hHnn : 0 ≤ r.heights := by omega
  -- Slot gap.
  have hSmem' : (S, sIdx) ∈
      (generatedRib ns (cause, k)).entries.zipIdx := hSmem
  have hbudget := generated_reservation_budget ns p ribs _hg
    (generatedRib ns (cause, k)) _hsource (by
      cases hentries : (generatedRib ns (cause, k)).entries with
      | nil =>
        rw [hentries] at hSmem'
        exact absurd hSmem' (by simp)
      | cons _ _ => rfl)
  have hslotGap : Int.fdiv (r.length * (pPos.2 + 1 : Nat)) (E.length + 1 : Nat) +
      r.heights ≤ Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    have hlen : 0 < ((E.length + 1 : Nat) : Int) := by omega
    have hlt : (pPos.2 + 1 : Nat) + 1 ≤ (sPos.2 + 1 : Nat) := by omega
    exact ordinal_slots_gap r.length ((E.length + 1 : Nat) : Int) r.heights
      ((pPos.2 + 1 : Nat) : Int) ((sPos.2 + 1 : Nat) : Int) hlen hHnn (by
        have hden : ((E.length + 1 : Nat) : Int) =
            (((generatedRib ns (cause, k)).entries.length + 1 : Nat) : Int) := by
          rw [hEl]
        rw [hden, hHr]
        exact hbudget) (by omega)
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro t ht0 ht1
  exact Int.le_refl _

/-- `S` is odd: same parent and depth as the odd route `child`. -/
private theorem descEnv_sOdd (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))))
    (child _j : Entry) (childIdx _jIdx : Nat) (_nj : Tree.Node)
    (frames : List Bone) (_childBorn _jBorn sBorn : Bone) (sIdx : Nat) (S : Entry)
    (nS : Tree.Node)
    (hconfig : HardBCaseConfig ns p cause k spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) child _j childIdx _jIdx _nj frames
      _childBorn _jBorn)
    (hreal : HardBRealFrames ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) placed hplace frames)
    (hS : (generatedRib ns (cause, k)).entries[sIdx]? = some S)
    (_hsne : sIdx ≠ _jIdx)
    (hSP : S.parent = ↑(child.parent).toNat)
    (_hchain : IndexedAncestor (generatedRib ns (cause, k)).entries sIdx _jIdx)
    (_hsBorn : frames[sIdx + 1]? = some sBorn)
    (_hnS : ns[S.node]? = some nS) :
    S.depth % 2 ≠ 0 := by
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  let E := (generatedRib ns (cause, k)).entries
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw _hrun
  obtain ⟨hchild, _hj, hodd, _hjlt, _hnj, _hlen, _hchildBorn, _hjBorn, _hspan⟩ :=
    hconfig
  obtain ⟨frames0, hshape0, hsub⟩ := hreal
  obtain ⟨hlen0, _hroot0, hrecords0⟩ := hshape0
  have hSmem : (S, sIdx) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hS
  obtain ⟨sDone, sRest, sPrefix, _⟩ := List.eq_append_cons_of_mem hSmem
  obtain ⟨_sPos, sPar, _sBorn0, _hsPos, hsParLookup, _hsBorn0, _hsEq⟩ :=
    hrecords0 sDone S sIdx sRest sPrefix
  have hClb : -1 ≤ child.parent :=
    generated_entry_parent_lower_bound ns cause k child childIdx hchild
  have hrootFalse : child.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink _hcause child childIdx
      hchild heq
    exact hodd (by omega)
  have hCParNat : child.parent = ((child.parent).toNat : Int) := by omega
  let pS := (child.parent).toNat
  have hSPeq : S.parent = (pS : Int) := hSP
  have hParLookup : frames0[(S.parent + 1).toNat]? = some sPar := hsParLookup
  have htoNat : ((pS : Int) + 1).toNat = pS + 1 := by omega
  rw [hSPeq, htoNat] at hParLookup
  have hEr : r.entries = E := rfl
  have hErLen : r.entries.length = E.length := by rw [hEr]
  have hlen0' : frames0.length = r.entries.length + 1 := hlen0
  have hpELT : pS < E.length := by
    obtain ⟨hpsLt, _⟩ := List.getElem?_eq_some_iff.mp hParLookup
    omega
  obtain ⟨pE, hpEGet⟩ : ∃ pE, E[pS]? = some pE :=
    ⟨_, List.getElem?_eq_getElem hpELT⟩
  have hpMem : (pE, pS) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hpEGet
  have hSdepth := generated_parent_child_depth ns cause k hlink _hcause
    pE S pS sIdx hpMem hSmem hSPeq
  have hCdepth := generated_parent_child_depth ns cause k hlink _hcause
    pE child pS childIdx hpMem hchild hCParNat
  omega

/-- Shared `S`-side facts: order positions, slot equations, span, gap, fall,
height bound, and reservation budget. Proved once from the executed records;
consumed by both one-step transport lemmas. -/
private theorem descEnv_sSetup (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))))
    (child _j : Entry) (childIdx _jIdx : Nat) (_nj : Tree.Node)
    (frames : List Bone) (_childBorn _jBorn sBorn : Bone) (sIdx : Nat) (S : Entry)
    (nS : Tree.Node)
    (hconfig : HardBCaseConfig ns p cause k spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) child _j childIdx _jIdx _nj frames
      _childBorn _jBorn)
    (hreal : HardBRealFrames ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) placed hplace frames)
    (hS : (generatedRib ns (cause, k)).entries[sIdx]? = some S)
    (_hsne : sIdx ≠ _jIdx)
    (hSP : S.parent = ↑(child.parent).toNat)
    (_hchain : IndexedAncestor (generatedRib ns (cause, k)).entries sIdx _jIdx)
    (hsBorn : frames[sIdx + 1]? = some sBorn)
    (hnS : ns[S.node]? = some nS) :
    ∃ (sPos pPos : Nat × Nat) (pE : Entry),
      (generatedRib ns (cause, k)).entries[(child.parent).toNat]? = some pE ∧
      pE.depth % 2 = 0 ∧
      (generatedRib ns (cause, k)).order.zipIdx.find?
        (fun v => v.1 == (child.parent).toNat) = some pPos ∧
      (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == sIdx) =
        some sPos ∧
      sBorn.t0 = Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).length * (pPos.2 + 1 : Nat))
        ((generatedRib ns (cause, k)).entries.length + 1 : Nat) ∧
      sBorn.t1 = Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).length * (sPos.2 + 1 : Nat))
        ((generatedRib ns (cause, k)).entries.length + 1 : Nat) ∧
      0 < sBorn.t1 - sBorn.t0 ∧
      sBorn.t0 + (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).heights ≤ sBorn.t1 ∧
      sBorn.x1 - sBorn.x0 = -(run p (sBorn.t1 - sBorn.t0)) ∧
      1 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).heights ∧
      (((generatedRib ns (cause, k)).entries.length + 1 : Nat) : Int) *
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k))).heights ≤
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k))).length := by
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  let E := (generatedRib ns (cause, k)).entries
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw _hrun
  have hSodd := descEnv_sOdd ns p raw _hrun ribs _hg cause k _hsource _hcause
    spine placed hplace _env child _j childIdx _jIdx _nj frames _childBorn
    _jBorn sBorn sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
  obtain ⟨hchild, _hj, hodd, _hjlt, _hnj, _hlen, _hchildBorn, _hjBorn, _hspan⟩ :=
    hconfig
  obtain ⟨frames0, hshape0, hsub⟩ := hreal
  obtain ⟨hlen0, _hroot0, hrecords0⟩ := hshape0
  have hSmem : (S, sIdx) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hS
  obtain ⟨sDone, sRest, sPrefix, _⟩ := List.eq_append_cons_of_mem hSmem
  obtain ⟨sPos, sPar, sBorn0, hsPos, hsParLookup, hsBorn0, hsEq⟩ :=
    hrecords0 sDone S sIdx sRest sPrefix
  have hsBornF0 : frames0[sIdx + 1]? = some sBorn := hsub _ _ hsBorn
  have hsBornEq : sBorn0 = sBorn := Option.some.inj (hsBorn0.symm.trans hsBornF0)
  have hClb : -1 ≤ child.parent :=
    generated_entry_parent_lower_bound ns cause k child childIdx hchild
  have hCParNat : child.parent = ((child.parent).toNat : Int) := by
    have hrootFalse : child.parent ≠ -1 := by
      intro heq
      have hd := generated_root_depth ns cause k hlink _hcause child childIdx
        hchild heq
      exact hodd (by omega)
    omega
  let pS := (child.parent).toNat
  have hSPeq : S.parent = (pS : Int) := hSP
  have hCParEq : child.parent = (pS : Int) := hCParNat
  have hParLookup : frames0[(S.parent + 1).toNat]? = some sPar := hsParLookup
  have htoNat : ((pS : Int) + 1).toNat = pS + 1 := by omega
  rw [hSPeq, htoNat] at hParLookup
  have hEr : r.entries = E := rfl
  have hHr : r.heights = (generatedRib ns (cause, k)).heights := rfl
  have hErLen : r.entries.length = E.length := by rw [hEr]
  have hlen0' : frames0.length = r.entries.length + 1 := hlen0
  have hpELT : pS < E.length := by
    obtain ⟨hpsLt, _⟩ := List.getElem?_eq_some_iff.mp hParLookup
    omega
  obtain ⟨pE, hpEGet⟩ : ∃ pE, E[pS]? = some pE :=
    ⟨_, List.getElem?_eq_getElem hpELT⟩
  have hpMem : (pE, pS) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hpEGet
  have hpEven : pE.depth % 2 = 0 :=
    parent_depth_even pE.depth S.depth (by
      have hSdepth := generated_parent_child_depth ns cause k hlink _hcause
        pE S pS sIdx hpMem hSmem hSPeq
      have hCdepth := generated_parent_child_depth ns cause k hlink _hcause
        pE child pS childIdx hpMem hchild hCParEq
      omega) hSodd
  obtain ⟨pDone, pRest, pPrefix, _⟩ := List.eq_append_cons_of_mem hpMem
  obtain ⟨pPos, _pPar, pBorn, hpPosOrd, _hpParLookup, hpBornLookup, hpEq⟩ :=
    hrecords0 pDone pE pS pRest pPrefix
  have hsParEq : sPar = pBorn := by
    have h1 : frames0[pS + 1]? = some sPar := hParLookup
    exact Option.some.inj (h1.symm.trans hpBornLookup)
  have hSt1 : sBorn.t1 =
      Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    rw [← hsBornEq, hsEq, hsParEq]
    exact (depthBone_odd_endpoints p _ S.depth _ _ _ hSodd).2.1
  have hSt0 : sBorn.t0 = pBorn.t0 := by
    rw [← hsBornEq, hsEq, hsParEq]
    exact (depthBone_odd_endpoints p _ S.depth _ _ _ hSodd).1
  have hpT : pBorn.t0 =
      Int.fdiv (r.length * (pPos.2 + 1 : Nat)) (E.length + 1 : Nat) ∧
      pBorn.t1 =
      Int.fdiv (r.length * (pPos.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    rw [hpEq]
    exact ⟨(depthBone_even_endpoints p _ pE.depth _ _ _ hpEven).1,
      (depthBone_even_endpoints p _ pE.depth _ _ _ hpEven).2.1⟩
  have hposLT : pPos.2 < sPos.2 := by
    have hord := generated_parent_child_order ns cause k pE S pS sIdx hpMem
      hSmem hSPeq pPos sPos hpPosOrd hsPos
    exact (hord.1 hpEven)
  have hmemN : nS ∈ ns := List.mem_of_getElem? hnS
  have hdims := successful_node_dimensions ns p raw _hrun nS hmemN
  have hHbound := measured_entry_height_bound ns E S
    (List.fst_mem_of_mem_zipIdx hSmem) nS hnS
  have hH1 : 1 ≤ r.heights := by
    have hgen : r.heights = (generatedRib ns (cause, k)).heights := rfl
    have hrib := (generated_rib_fields ns cause k).2.2.2
    have hEfold : E.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 =
        (generatedRib ns (cause, k)).entries.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := rfl
    have hd1 : 1 ≤ nS.height := hdims.2
    omega
  have hHnn : 0 ≤ r.heights := by omega
  have hSmem' : (S, sIdx) ∈
      (generatedRib ns (cause, k)).entries.zipIdx := hSmem
  have hbudget := generated_reservation_budget ns p ribs _hg
    (generatedRib ns (cause, k)) _hsource (by
      cases hentries : (generatedRib ns (cause, k)).entries with
      | nil =>
        rw [hentries] at hSmem'
        exact absurd hSmem' (by simp)
      | cons _ _ => rfl)
  have hslotGap : Int.fdiv (r.length * (pPos.2 + 1 : Nat)) (E.length + 1 : Nat) +
      r.heights ≤ Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    have hlen : 0 < ((E.length + 1 : Nat) : Int) := by omega
    have hlt : (pPos.2 + 1 : Nat) + 1 ≤ (sPos.2 + 1 : Nat) := by omega
    exact ordinal_slots_gap r.length ((E.length + 1 : Nat) : Int) r.heights
      ((pPos.2 + 1 : Nat) : Int) ((sPos.2 + 1 : Nat) : Int) hlen hHnn (by
        have hden : ((E.length + 1 : Nat) : Int) =
            (((generatedRib ns (cause, k)).entries.length + 1 : Nat) : Int) := by
          have hEl : E.length = (generatedRib ns (cause, k)).entries.length := rfl
          rw [hEl]
        have hHr2 : r.heights = (generatedRib ns (cause, k)).heights := rfl
        rw [hden, hHr2]
        exact hbudget) (by omega)
  have hX1 : sBorn.x1 = sBorn.x0 - run p (sBorn.t1 - sBorn.t0) := by
    rw [hSt1, hSt0, ← hsBornEq, hsEq, hsParEq]
    exact (depthBone_odd_endpoints p _ S.depth _ _ _ hSodd).2.2.2
  have hfall : sBorn.x1 - sBorn.x0 = -(run p (sBorn.t1 - sBorn.t0)) := by omega
  have hgap : sBorn.t0 + r.heights ≤ sBorn.t1 := by
    rw [hSt0, hSt1]
    have hpt := hpT
    omega
  have hspanPos : 0 < sBorn.t1 - sBorn.t0 := by omega
  have hSt0v : sBorn.t0 =
      Int.fdiv (r.length * (pPos.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    rw [hSt0]; exact hpT.1
  have hSt1v : sBorn.t1 =
      Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (E.length + 1 : Nat) := hSt1
  have hhl : ((E.length + 1 : Nat) : Int) * r.heights ≤ r.length := by
    have hden : ((E.length + 1 : Nat) : Int) =
        (((generatedRib ns (cause, k)).entries.length + 1 : Nat) : Int) := by
      have hEl : E.length = (generatedRib ns (cause, k)).entries.length := rfl
      rw [hEl]
    rw [hden, hHr]
    exact hbudget
  exact ⟨sPos, pPos, pE, hpEGet, hpEven, hpPosOrd, hsPos, hSt0v, hSt1v, hspanPos,
    hgap, hfall, hH1, hhl⟩
/-- One-edge transport for an even child: time containment via order and slot
gaps; the start interpolates exactly on the parent odd line, the end runs
horizontally left. -/
private theorem descEnv_step_even (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))))
    (child _j : Entry) (childIdx _jIdx : Nat) (_nj : Tree.Node)
    (frames : List Bone) (_childBorn _jBorn sBorn : Bone) (sIdx : Nat) (S : Entry)
    (nS : Tree.Node)
    (hconfig : HardBCaseConfig ns p cause k spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) child _j childIdx _jIdx _nj frames
      _childBorn _jBorn)
    (hreal : HardBRealFrames ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) placed hplace frames)
    (hS : (generatedRib ns (cause, k)).entries[sIdx]? = some S)
    (_hsne : sIdx ≠ _jIdx)
    (hSP : S.parent = ↑(child.parent).toNat)
    (_hchain : IndexedAncestor (generatedRib ns (cause, k)).entries sIdx _jIdx)
    (hsBorn : frames[sIdx + 1]? = some sBorn)
    (hnS : ns[S.node]? = some nS)
    (a b : Nat) (aE bE : Entry) (aBorn bBorn : Bone)
    (haE : (generatedRib ns (cause, k)).entries[a]? = some aE)
    (hbE : (generatedRib ns (cause, k)).entries[b]? = some bE)
    (hpar : bE.parent = (a : Int))
    (hchainS : IndexedAncestor (generatedRib ns (cause, k)).entries sIdx b)
    (hframesA : frames[a + 1]? = some aBorn)
    (hframesB : frames[b + 1]? = some bBorn)
    (hQa : (aE.depth % 2 = 1 → DescOddBound sBorn aBorn) ∧
      (aE.depth % 2 = 0 → DescEvenBound sBorn aBorn))
    (hbeven : bE.depth % 2 = 0) :
    (bE.depth % 2 = 1 → DescOddBound sBorn bBorn) ∧
      (bE.depth % 2 = 0 → DescEvenBound sBorn bBorn) := by
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  let E := (generatedRib ns (cause, k)).entries
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw _hrun
  have hSmem : (S, sIdx) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hS
  have hSodd := descEnv_sOdd ns p raw _hrun ribs _hg cause k _hsource _hcause
    spine placed hplace _env child _j childIdx _jIdx _nj frames _childBorn
    _jBorn sBorn sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
  obtain ⟨sPos, pPos, pE, hpEGet, hpEven, hpPosOrd, hsPos, hSt0v, hSt1v, _hspanPos,
    _hgap, _hfall, hH1, hhl⟩ :=
    descEnv_sSetup ns p raw _hrun ribs _hg cause k _hsource _hcause spine placed
      hplace _env child _j childIdx _jIdx _nj frames _childBorn _jBorn sBorn
      sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
  obtain ⟨hchild, _hj, hodd, _hjlt, _hnj, _hlen, _hchildBorn, _hjBorn, _hspan⟩ :=
    hconfig
  obtain ⟨frames0, hshape0, hsub⟩ := hreal
  obtain ⟨hlen0, _hroot0, hrecords0⟩ := hshape0
  have hSt0 : sBorn.t0 =
      Int.fdiv (r.length * (pPos.2 + 1 : Nat)) (E.length + 1 : Nat) := hSt0v
  have hSt1 : sBorn.t1 =
      Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (E.length + 1 : Nat) := hSt1v
  have hH1' : 1 ≤ r.heights := hH1
  have hhl' : ((E.length + 1 : Nat) : Int) * r.heights ≤ r.length := hhl
  have hne : ns ≠ [] := by
    intro heq
    simp [heq, children] at _hcause
  have hparameters := successful_slope_parameters ns p raw hne _hrun
  have hcos : 0 ≤ p.cos := hparameters.1
  have hsin0 : 0 < p.sin := by have := hparameters.2; omega
  have hHnn : 0 ≤ r.heights := by omega
  have hErLen : r.entries.length = E.length := rfl
  have hlen0' : frames0.length = r.entries.length + 1 := hlen0
  -- `b`'s birth record.
  have hbMem : (bE, b) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hbE
  obtain ⟨bDone, bRest, bPrefix, _⟩ := List.eq_append_cons_of_mem hbMem
  obtain ⟨posB, parB, bornB, hfindB, hparLookupB, hbornLookupB, heqB⟩ :=
    hrecords0 bDone bE b bRest bPrefix
  have hbornF0 : frames0[b + 1]? = some bBorn := hsub _ _ hframesB
  have hbornEq : bornB = bBorn := Option.some.inj (hbornLookupB.symm.trans hbornF0)
  have hparEq : parB = aBorn := by
    have h1 : frames0[(bE.parent + 1).toNat]? = some parB := hparLookupB
    have hown : (bE.parent + 1).toNat = a + 1 := by rw [hpar]; omega
    rw [hown] at h1
    have h2 : frames0[a + 1]? = some aBorn := hsub _ _ hframesA
    exact Option.some.inj (h1.symm.trans h2)
  -- `b` is even, `a` is odd.
  have haMem : (aE, a) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr haE
  have hdepb : bE.depth = aE.depth + 1 :=
    generated_parent_child_depth ns cause k hlink _hcause aE bE a b haMem
      hbMem hpar
  have hmodA := Nat.mod_lt aE.depth (by decide : 0 < 2)
  have hmodB := Nat.mod_lt bE.depth (by decide : 0 < 2)
  have haodd : aE.depth % 2 = 1 := by omega
  have haoddNe : aE.depth % 2 ≠ 0 := by omega
  have hQaOdd := hQa.1 haodd
  obtain ⟨_hAspan, _hAt0, _hAt1, hAline⟩ := hQaOdd
  -- Birth equations for `b` (record form, then `E`-form).
  have hbT1r : bBorn.t1 =
      Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [← hbornEq, heqB, hparEq]
    exact (depthBone_even_endpoints p _ bE.depth _ _ _ hbeven).2.1
  have hbT1 : bBorn.t1 =
      Int.fdiv (r.length * (posB.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    rw [← hErLen]
    exact hbT1r
  have hbT0 : bBorn.t0 = bBorn.t1 := by
    have h1 : bBorn.t0 =
        Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
      rw [← hbornEq, heqB, hparEq]
      exact (depthBone_even_endpoints p _ bE.depth _ _ _ hbeven).1
    rw [h1, hbT1r]
  have hbX0 : bBorn.x0 = aBorn.x0 + Int.fdiv
      ((aBorn.x1 - aBorn.x0) *
        (Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat) -
          aBorn.t0)) (aBorn.t1 - aBorn.t0) := by
    rw [← hbornEq, heqB, hparEq]
    simp [depthBone, hbeven, r]
  rw [← hbT1r] at hbX0
  have hbX1 : bBorn.x1 =
      bBorn.x0 - boneLength p (children ns bE.node).length (run p r.heights + 3) := by
    rw [← hbornEq, heqB, hparEq]
    exact (depthBone_even_endpoints p _ bE.depth _ _ _ hbeven).2.2
  -- `a`'s record and grandparent `P_a` for the lower span bound.
  obtain ⟨aDone, aRest, aPrefix, _⟩ := List.eq_append_cons_of_mem haMem
  obtain ⟨posA, parA, bornA, hfindA, hparLookupA, hbornLookupA, heqA⟩ :=
    hrecords0 aDone aE a aRest aPrefix
  have haBornF0 : frames0[a + 1]? = some aBorn := hsub _ _ hframesA
  have haBornEq : bornA = aBorn := Option.some.inj (hbornLookupA.symm.trans haBornF0)
  -- `a`'s own slot.
  have haT1v : aBorn.t1 =
      Int.fdiv (r.length * (posA.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    have h0 : aBorn.t1 =
        Int.fdiv (r.length * (posA.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
      rw [← haBornEq, heqA]
      exact (depthBone_odd_endpoints p _ aE.depth _ _ _ haoddNe).2.1
    rw [hErLen] at h0
    exact h0
  -- Grandparent `P_a`: entry, record, even bones.
  have hPaBridge : frames0[(aE.parent + 1).toNat]? = some parA := hparLookupA
  have haParNat : aE.parent = ((aE.parent).toNat : Int) := by
    have hlb : -1 ≤ aE.parent :=
      generated_entry_parent_lower_bound ns cause k aE a haMem
    have hne : aE.parent ≠ -1 := by
      intro heq
      have hrt := generated_root_depth ns cause k hlink _hcause aE a haMem heq
      have hdepth := generated_parent_child_depth ns cause k hlink _hcause aE bE
        a b haMem hbMem hpar
      omega
    omega
  let pA := (aE.parent).toNat
  have hParEqA : aE.parent = (pA : Int) := haParNat
  have htoNatA : ((pA : Int) + 1).toNat = pA + 1 := by omega
  have hParLookupA : frames0[pA + 1]? = some parA := by
    have h := hparLookupA
    rw [hParEqA, htoNatA] at h
    exact h
  have hpAELT : pA < E.length := by
    obtain ⟨hltA, _⟩ := List.getElem?_eq_some_iff.mp hParLookupA
    have hlenA : frames0.length = r.entries.length + 1 := hlen0
    omega
  obtain ⟨pAe, hpAeGet⟩ : ∃ pAe, E[pA]? = some pAe :=
    ⟨_, List.getElem?_eq_getElem hpAELT⟩
  have hpAMem : (pAe, pA) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hpAeGet
  have hpaDepth := generated_parent_child_depth ns cause k hlink _hcause
    pAe aE pA a hpAMem haMem hParEqA
  have hpAeven : pAe.depth % 2 = 0 :=
    parent_depth_even pAe.depth aE.depth (by omega) haoddNe
  obtain ⟨paDone, paRest, paPrefix, _⟩ := List.eq_append_cons_of_mem hpAMem
  obtain ⟨posPA, _paPar, paBorn, hfindPA, hparLookupPA, hbornLookupPA, heqPA⟩ :=
    hrecords0 paDone pAe pA paRest paPrefix
  have hparAeq : parA = paBorn := by
    have h1 : frames0[pA + 1]? = some parA := hParLookupA
    exact Option.some.inj (h1.symm.trans hbornLookupPA)
  have hpaT : paBorn.t0 =
      Int.fdiv (r.length * (posPA.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    have h0 : paBorn.t0 =
        Int.fdiv (r.length * (posPA.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
      rw [heqPA]
      exact (depthBone_even_endpoints p _ pAe.depth _ _ _ hpAeven).1
    rw [hErLen] at h0
    exact h0
  have haT0v : aBorn.t0 =
      Int.fdiv (r.length * (posPA.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    have h1 : aBorn.t0 = parA.t0 := by
      rw [← haBornEq, heqA]
      exact (depthBone_odd_endpoints p _ aE.depth _ _ _ haoddNe).1
    rw [h1, hparAeq, hpaT]
  have hparameters := successful_slope_parameters ns p raw hne _hrun
  have hcos : 0 ≤ p.cos := hparameters.1
  have hsin0 : 0 < p.sin := by have := hparameters.2; omega
  have hchainPSb : IndexedAncestor E ((child.parent).toNat) b :=
    descEnv_trans (IndexedAncestor.edge _ _ S hS hSP) hchainS
  have hchainPAb : IndexedAncestor E pA b :=
    descEnv_trans (IndexedAncestor.edge _ _ aE haE hParEqA)
      (IndexedAncestor.edge _ _ bE hbE hpar)
  have hpMemPS : (pE, (child.parent).toNat) ∈ E.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hpEGet
  have hpMemPA : (pAe, pA) ∈ E.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hpAeGet
  -- Order positions.
  have hposPSB : pPos.2 < posB.2 := by
    have hord := generated_ancestor_order ns cause k pE bE
      ((child.parent).toNat) b hpMemPS hbMem hchainPSb pPos posB hpPosOrd hfindB
    exact (hord.1 hpEven)
  have hposPAB : posPA.2 < posB.2 := by
    have hord := generated_ancestor_order ns cause k pAe bE
      pA b hpMemPA hbMem hchainPAb posPA posB hfindPA hfindB
    exact (hord.1 hpAeven)
  have hposBA : posB.2 < posA.2 := by
    have hchainAB : IndexedAncestor E a b :=
      IndexedAncestor.edge _ _ bE hbE hpar
    have hord := generated_ancestor_order ns cause k aE bE
      a b haMem hbMem hchainAB posA posB hfindA hfindB
    exact (hord.2 haoddNe)
  have hposBS : posB.2 < sPos.2 := by
    have hord := generated_ancestor_order ns cause k S bE
      sIdx b hSmem hbMem hchainS sPos posB hsPos hfindB
    exact (hord.2 hSodd)
  -- Slot gaps.
  have hslotPSB : Int.fdiv (r.length * (pPos.2 + 1 : Nat)) (E.length + 1 : Nat) +
      r.heights ≤ Int.fdiv (r.length * (posB.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    have hlen : 0 < ((E.length + 1 : Nat) : Int) := by omega
    have hlt : (pPos.2 + 1 : Nat) + 1 ≤ (posB.2 + 1 : Nat) := by omega
    exact ordinal_slots_gap r.length ((E.length + 1 : Nat) : Int) r.heights
      ((pPos.2 + 1 : Nat) : Int) ((posB.2 + 1 : Nat) : Int) hlen hHnn hhl' (by omega)
  have hslotPAB : Int.fdiv (r.length * (posPA.2 + 1 : Nat)) (E.length + 1 : Nat) +
      r.heights ≤ Int.fdiv (r.length * (posB.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    have hlen : 0 < ((E.length + 1 : Nat) : Int) := by omega
    have hlt : (posPA.2 + 1 : Nat) + 1 ≤ (posB.2 + 1 : Nat) := by omega
    exact ordinal_slots_gap r.length ((E.length + 1 : Nat) : Int) r.heights
      ((posPA.2 + 1 : Nat) : Int) ((posB.2 + 1 : Nat) : Int) hlen hHnn hhl' (by omega)
  have hslotBA : Int.fdiv (r.length * (posB.2 + 1 : Nat)) (E.length + 1 : Nat) +
      r.heights ≤ Int.fdiv (r.length * (posA.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    have hlen : 0 < ((E.length + 1 : Nat) : Int) := by omega
    have hlt : (posB.2 + 1 : Nat) + 1 ≤ (posA.2 + 1 : Nat) := by omega
    exact ordinal_slots_gap r.length ((E.length + 1 : Nat) : Int) r.heights
      ((posB.2 + 1 : Nat) : Int) ((posA.2 + 1 : Nat) : Int) hlen hHnn hhl' (by omega)
  have hslotBS : Int.fdiv (r.length * (posB.2 + 1 : Nat)) (E.length + 1 : Nat) +
      r.heights ≤ Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (E.length + 1 : Nat) := by
    have hlen : 0 < ((E.length + 1 : Nat) : Int) := by omega
    have hlt : (posB.2 + 1 : Nat) + 1 ≤ (sPos.2 + 1 : Nat) := by omega
    exact ordinal_slots_gap r.length ((E.length + 1 : Nat) : Int) r.heights
      ((posB.2 + 1 : Nat) : Int) ((sPos.2 + 1 : Nat) : Int) hlen hHnn hhl' (by omega)
  -- Time containment.
  have hTimeLo : sBorn.t0 ≤ bBorn.t1 := by omega
  have hTimeHi : bBorn.t1 ≤ sBorn.t1 := by omega
  -- Pointwise on the parent line.
  have hslotInAlo : aBorn.t0 ≤ bBorn.t1 := by omega
  have hslotInAhi : bBorn.t1 ≤ aBorn.t1 := by omega
  have hline : descLineOf aBorn bBorn.t1 ≤ descLineOf sBorn bBorn.t1 :=
    hAline bBorn.t1 hslotInAlo hslotInAhi
  have hbX0line : bBorn.x0 ≤ descLineOf sBorn bBorn.t1 := by
    have h := hline
    simp only [descLineOf] at h ⊢
    omega
  have hmarginNN : 0 ≤ run p r.heights + 3 := by
    have hrunNN : 0 ≤ run p r.heights :=
      Int.fdiv_nonneg (Int.mul_nonneg hHnn hcos) (Int.le_of_lt hsin0)
    omega
  have hLnn : 0 ≤
      boneLength p (children ns bE.node).length (run p r.heights + 3) := by
    have h1 : 0 ≤ (((children ns bE.node).length : Int) + 1) *
        (run p r.heights + 3) :=
      Int.mul_nonneg (by omega) hmarginNN
    have h2 : (((children ns bE.node).length : Int) + 1) *
        (run p r.heights + 3) ≤
        boneLength p (children ns bE.node).length (run p r.heights + 3) :=
      Int.le_max_right _ _
    omega
  have hbX1le : bBorn.x1 ≤ descLineOf sBorn bBorn.t1 := by omega
  exact ⟨fun h => absurd h (by omega), fun _ =>
    ⟨hTimeLo, hTimeHi, hbX0line, hbX1le⟩⟩

 set_option maxHeartbeats 1000000 in
 /-- One-edge transport for an odd child: time containment via order and slot
 gaps; the start runs left of the even parent's start by the reservation
 margin, and pointwise domination follows from the parent-line drop bound,
 the child-line fall bound, and the margin absorbing the rounding of at most
 2. -/
 private theorem descEnv_step_odd (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout)
     (_hrun : layout ns p = .ok raw)
     (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
     (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
     (hplace : place ns p spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) = .ok placed)
     (_env : IshikawaEnvFrames ns p
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))))
     (child _j : Entry) (childIdx _jIdx : Nat) (_nj : Tree.Node)
     (frames : List Bone) (_childBorn _jBorn sBorn : Bone) (sIdx : Nat) (S : Entry)
     (nS : Tree.Node)
     (hconfig : HardBCaseConfig ns p cause k spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) child _j childIdx _jIdx _nj frames
       _childBorn _jBorn)
     (hreal : HardBRealFrames ns p spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) placed hplace frames)
     (hS : (generatedRib ns (cause, k)).entries[sIdx]? = some S)
     (_hsne : sIdx ≠ _jIdx)
     (hSP : S.parent = ↑(child.parent).toNat)
     (_hchain : IndexedAncestor (generatedRib ns (cause, k)).entries sIdx _jIdx)
     (hsBorn : frames[sIdx + 1]? = some sBorn)
     (hnS : ns[S.node]? = some nS)
     (a b : Nat) (aE bE : Entry) (aBorn bBorn : Bone)
     (haE : (generatedRib ns (cause, k)).entries[a]? = some aE)
     (hbE : (generatedRib ns (cause, k)).entries[b]? = some bE)
     (hpar : bE.parent = (a : Int))
     (hchainS : IndexedAncestor (generatedRib ns (cause, k)).entries sIdx b)
     (hframesA : frames[a + 1]? = some aBorn)
     (hframesB : frames[b + 1]? = some bBorn)
     (hQa : (aE.depth % 2 = 1 → DescOddBound sBorn aBorn) ∧
       (aE.depth % 2 = 0 → DescEvenBound sBorn aBorn))
     (hbodd : bE.depth % 2 ≠ 0) :
     (bE.depth % 2 = 1 → DescOddBound sBorn bBorn) ∧
       (bE.depth % 2 = 0 → DescEvenBound sBorn bBorn) := by
   have hmodA := Nat.mod_lt aE.depth (by decide : 0 < 2)
   have hmodB := Nat.mod_lt bE.depth (by decide : 0 < 2)
   have hbodd1 : bE.depth % 2 = 1 := by omega
   refine ⟨fun _ => ?_, fun h => absurd h hbodd⟩
   let r := effectivePlacedInput ns (measuredSideLength p ribs)
     (generatedRib ns (cause, k))
   let E := (generatedRib ns (cause, k)).entries
   have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw _hrun
   have hSmem : (S, sIdx) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hS
   have hSodd := descEnv_sOdd ns p raw _hrun ribs _hg cause k _hsource _hcause
     spine placed hplace _env child _j childIdx _jIdx _nj frames _childBorn
     _jBorn sBorn sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
   obtain ⟨sPos, pPos, pE, hpEGet, hpEven, hpPosOrd, hsPos, hSt0v, hSt1v, hspanPos,
     hgap, hfall, hH1, hhl⟩ :=
     descEnv_sSetup ns p raw _hrun ribs _hg cause k _hsource _hcause spine placed
       hplace _env child _j childIdx _jIdx _nj frames _childBorn _jBorn sBorn
       sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
   obtain ⟨hchild, _hj, hodd, _hjlt, _hnj, _hlen, _hchildBorn, _hjBorn, _hspan⟩ :=
     hconfig
   obtain ⟨frames0, hshape0, hsub⟩ := hreal
   obtain ⟨hlen0, _hroot0, hrecords0⟩ := hshape0
   have hSt1 : sBorn.t1 =
       Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (E.length + 1 : Nat) := hSt1v
   have hne : ns ≠ [] := by
     intro heq
     simp [heq, children] at _hcause
   have hparameters := successful_slope_parameters ns p raw hne _hrun
   have hcos : 0 ≤ p.cos := hparameters.1
   have hsin1 : 1 ≤ p.sin := hparameters.2
   have hsin0 : 0 < p.sin := by omega
   have hH1' : 1 ≤ r.heights := hH1
   have hhl' : ((E.length + 1 : Nat) : Int) * r.heights ≤ r.length := hhl
   have hHnn : 0 ≤ r.heights := by omega
   have hErLen : r.entries.length = E.length := rfl
   have hbMem : (bE, b) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hbE
   obtain ⟨bDone, bRest, bPrefix, _⟩ := List.eq_append_cons_of_mem hbMem
   obtain ⟨posB, parB, bornB, hfindB, hparLookupB, hbornLookupB, heqB⟩ :=
     hrecords0 bDone bE b bRest bPrefix
   have hbornF0 : frames0[b + 1]? = some bBorn := hsub _ _ hframesB
   have hbornEq : bornB = bBorn := Option.some.inj (hbornLookupB.symm.trans hbornF0)
   have hown : (bE.parent + 1).toNat = a + 1 := by rw [hpar]; omega
   have hparEq : parB = aBorn := by
     have h1 : frames0[(bE.parent + 1).toNat]? = some parB := hparLookupB
     rw [hown] at h1
     have h2 : frames0[a + 1]? = some aBorn := hsub _ _ hframesA
     exact Option.some.inj (h1.symm.trans h2)
   have haMem : (aE, a) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr haE
   have hdepb : bE.depth = aE.depth + 1 :=
     generated_parent_child_depth ns cause k hlink _hcause aE bE a b haMem
       hbMem hpar
   have haeven : aE.depth % 2 = 0 := by omega
   have hQaEven := hQa.2 haeven
   obtain ⟨hAt0, hAt1, hAx0, _hAx1⟩ := hQaEven
   obtain ⟨aDone, aRest, aPrefix, _⟩ := List.eq_append_cons_of_mem haMem
   obtain ⟨posA, parA, bornA, hfindA, hparLookupA, hbornLookupA, heqA⟩ :=
     hrecords0 aDone aE a aRest aPrefix
   have haBornF0 : frames0[a + 1]? = some aBorn := hsub _ _ hframesA
   have haBornEq : bornA = aBorn := Option.some.inj (hbornLookupA.symm.trans haBornF0)
   have hbT1r : bBorn.t1 =
       Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
     rw [← hbornEq, heqB, hparEq]
     exact (depthBone_odd_endpoints p _ bE.depth _ _ _ hbodd).2.1
   have hbT1 : bBorn.t1 =
       Int.fdiv (r.length * (posB.2 + 1 : Nat)) (E.length + 1 : Nat) := by
     have h0 : bBorn.t1 =
         Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
       rw [← hbornEq, heqB, hparEq]
       exact (depthBone_odd_endpoints p _ bE.depth _ _ _ hbodd).2.1
     rw [hErLen] at h0
     exact h0
   have hbT0 : bBorn.t0 = aBorn.t0 := by
     rw [← hbornEq, heqB, hparEq]
     exact (depthBone_odd_endpoints p _ bE.depth _ _ _ hbodd).1
   have haT1 : aBorn.t1 =
       Int.fdiv (r.length * (posA.2 + 1 : Nat)) (E.length + 1 : Nat) := by
     have h0 : aBorn.t1 =
         Int.fdiv (r.length * (posA.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
       rw [← haBornEq, heqA]
       exact (depthBone_even_endpoints p _ aE.depth _ _ _ haeven).2.1
     rw [hErLen] at h0
     exact h0
   have haT0 : aBorn.t0 =
       Int.fdiv (r.length * (posA.2 + 1 : Nat)) (E.length + 1 : Nat) := by
     have h0 : aBorn.t0 =
         Int.fdiv (r.length * (posA.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
       rw [← haBornEq, heqA]
       exact (depthBone_even_endpoints p _ aE.depth _ _ _ haeven).1
     rw [hErLen] at h0
     exact h0
   have hbX0 : bBorn.x0 = aBorn.x0 + Int.fdiv
       ((aBorn.x1 - aBorn.x0) *
         (aBorn.count - processedOddDraws bDone (a + 1))) (aBorn.count + 1) := by
     rw [← hbornEq, heqB, hparEq, hown]
     exact (depthBone_odd_endpoints p _ bE.depth _ _ _ hbodd).2.2.1
   have hbFall : bBorn.x1 - bBorn.x0 = -(run p (bBorn.t1 - bBorn.t0)) := by
     have hlem : (depthBone p
         {parB with drawn := processedOddDraws bDone ((bE.parent + 1).toNat)}
         bE.depth
         (Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
         (children ns bE.node).length (run p r.heights + 3)).x1 =
         (depthBone p
         {parB with drawn := processedOddDraws bDone ((bE.parent + 1).toNat)}
         bE.depth
         (Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
         (children ns bE.node).length (run p r.heights + 3)).x0 - run p
         ((Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) -
           parB.t0) :=
       (depthBone_odd_endpoints p _ bE.depth _ _ _ hbodd).2.2.2
     have e1 : (depthBone p
         {parB with drawn := processedOddDraws bDone ((bE.parent + 1).toNat)}
         bE.depth
         (Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
         (children ns bE.node).length (run p r.heights + 3)) = bBorn :=
       heqB.symm.trans hbornEq
     rw [e1] at hlem
     have hparT0 : parB.t0 = aBorn.t0 := by rw [hparEq]
     rw [hbT1r.symm, hparT0, ← hbT0] at hlem
     omega
   have hEqA : (depthBone p
       {parA with drawn := processedOddDraws aDone (aE.parent + 1).toNat} aE.depth
       (Int.fdiv (r.length * (posA.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
       (children ns aE.node).length (run p r.heights + 3)) = aBorn :=
     heqA.symm.trans haBornEq
   have hreserve := even_native_reservation p
     {parA with drawn := processedOddDraws aDone (aE.parent + 1).toNat} aE.depth
     (Int.fdiv (r.length * (posA.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
     (children ns aE.node).length (run p r.heights + 3) haeven
   rw [hEqA] at hreserve
   have hcount : aBorn.count = ((children ns aE.node).length : Int) := by
     rw [← haBornEq, heqA]
     simp [depthBone, haeven]
   have hdrawBound := generated_current_odd_prefix_draw_bound ns cause k hlink
     _hcause bDone bE b bRest bPrefix aE a haMem hpar hbodd
   have hdraw : processedOddDraws bDone (a + 1) + 1 ≤ aBorn.count := by
     rw [hcount]
     exact hdrawBound
   have hmargin : 0 ≤ run p r.heights + 3 := by
     have hrunNN : 0 ≤ run p r.heights :=
       Int.fdiv_nonneg (Int.mul_nonneg hHnn hcos) (Int.le_of_lt hsin0)
     omega
   have hstartGap : bBorn.x0 + (run p r.heights + 3) ≤ aBorn.x0 := by
     rw [hbX0]
     exact descEnv_attach_start_margin aBorn.x0 aBorn.x1 aBorn.count
       (processedOddDraws bDone (a + 1)) (run p r.heights + 3)
       hreserve.1 hmargin hreserve.2 hdraw
   have haEq : aBorn.t0 = aBorn.t1 := haT0.trans haT1.symm
   have hSb0 : bBorn.x0 + (run p r.heights + 3) ≤
       descLineOf sBorn bBorn.t0 := by
     have h1 : bBorn.t0 = aBorn.t1 := hbT0.trans haEq
     rw [h1]
     omega
   have hchainAB : IndexedAncestor E a b :=
     IndexedAncestor.edge _ _ bE hbE hpar
   have hposAB : posA.2 < posB.2 := by
     have hord := generated_parent_child_order ns cause k aE bE
       a b haMem hbMem hpar posA posB hfindA hfindB
     exact (hord.1 haeven)
   have hposBS : posB.2 < sPos.2 := by
     have hord := generated_ancestor_order ns cause k S bE
       sIdx b hSmem hbMem hchainS sPos posB hsPos hfindB
     exact (hord.2 hSodd)
   have hslotAB : Int.fdiv (r.length * (posA.2 + 1 : Nat)) (E.length + 1 : Nat) +
       r.heights ≤ Int.fdiv (r.length * (posB.2 + 1 : Nat)) (E.length + 1 : Nat) := by
     have hlen : 0 < ((E.length + 1 : Nat) : Int) := by omega
     have hlt : (posA.2 + 1 : Nat) + 1 ≤ (posB.2 + 1 : Nat) := by omega
     exact ordinal_slots_gap r.length ((E.length + 1 : Nat) : Int) r.heights
       ((posA.2 + 1 : Nat) : Int) ((posB.2 + 1 : Nat) : Int) hlen hHnn hhl' (by omega)
   have hslotBS : Int.fdiv (r.length * (posB.2 + 1 : Nat)) (E.length + 1 : Nat) +
       r.heights ≤ Int.fdiv (r.length * (sPos.2 + 1 : Nat)) (E.length + 1 : Nat) := by
     have hlen : 0 < ((E.length + 1 : Nat) : Int) := by omega
     have hlt : (posB.2 + 1 : Nat) + 1 ≤ (sPos.2 + 1 : Nat) := by omega
     exact ordinal_slots_gap r.length ((E.length + 1 : Nat) : Int) r.heights
       ((posB.2 + 1 : Nat) : Int) ((sPos.2 + 1 : Nat) : Int) hlen hHnn hhl' (by omega)
   have hTimePos : 0 < bBorn.t1 - bBorn.t0 := by omega
   have hTimeLo : sBorn.t0 ≤ bBorn.t0 := by omega
   have hTimeHi : bBorn.t1 ≤ sBorn.t1 := by omega
   refine ⟨hTimePos, hTimeLo, hTimeHi, ?_⟩
   intro t ht0 ht1
   have hSr : sBorn.x1 - sBorn.x0 = -(run p (sBorn.t1 - sBorn.t0)) := hfall
   have hSbt0 : descLineOf sBorn bBorn.t0 = sBorn.x0 + Int.fdiv
       (-(run p (sBorn.t1 - sBorn.t0) * (bBorn.t0 - sBorn.t0)))
       (sBorn.t1 - sBorn.t0) := by
     simp only [descLineOf]
     rw [hSr, Int.neg_mul]
   have hSt : descLineOf sBorn t = sBorn.x0 + Int.fdiv
       (-(run p (sBorn.t1 - sBorn.t0) * (t - sBorn.t0)))
       (sBorn.t1 - sBorn.t0) := by
     simp only [descLineOf]
     rw [hSr, Int.neg_mul]
   have hbt : descLineOf bBorn t = bBorn.x0 + Int.fdiv
       (-(run p (bBorn.t1 - bBorn.t0) * (t - bBorn.t0)))
       (bBorn.t1 - bBorn.t0) := by
     simp only [descLineOf]
     rw [hbFall, Int.neg_mul]
   have hdtNN : 0 ≤ t - bBorn.t0 := by omega
   have hdtLe : t - bBorn.t0 ≤ bBorn.t1 - bBorn.t0 := by omega
   have hSdrop := descEnv_line_drop p hcos hsin1 sBorn.x0 sBorn.t0
     (sBorn.t1 - sBorn.t0) bBorn.t0 t hspanPos (by omega) (by omega)
   have hbfall := descEnv_fall_lb p hcos hsin1 (bBorn.t1 - bBorn.t0)
     (t - bBorn.t0) hTimePos hdtNN hdtLe
   have hmargin3 : 3 ≤ run p r.heights + 3 := by
     have hrunNN : 0 ≤ run p r.heights :=
       Int.fdiv_nonneg (Int.mul_nonneg hHnn hcos) (Int.le_of_lt hsin0)
     omega
   omega
 set_option maxHeartbeats 1000000 in
 /-- Ancestor-chain induction for the envelope invariant: the sibling `S`
 itself satisfies the odd bound (`descEnv_base`), direct children transport
 from `S`, and deeper edges transport from the induction hypothesis for the
 parent via `descEnv_step_even` / `descEnv_step_odd`. Intermediate birth
 frames exist by the executed length (`frames.length = E.length + 1`); the
 target descendant's lookups are the caller's. -/
 private theorem descEnv_induct (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout)
     (_hrun : layout ns p = .ok raw)
     (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
     (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
     (hplace : place ns p spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) = .ok placed)
     (_env : IshikawaEnvFrames ns p
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))))
     (child _j : Entry) (childIdx _jIdx : Nat) (_nj : Tree.Node)
     (frames : List Bone) (_childBorn _jBorn sBorn : Bone) (sIdx : Nat) (S : Entry)
     (nS : Tree.Node)
     (hconfig : HardBCaseConfig ns p cause k spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) child _j childIdx _jIdx _nj frames
       _childBorn _jBorn)
     (hreal : HardBRealFrames ns p spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) placed hplace frames)
     (hS : (generatedRib ns (cause, k)).entries[sIdx]? = some S)
     (_hsne : sIdx ≠ _jIdx)
     (hSP : S.parent = ↑(child.parent).toNat)
     (_hchain : IndexedAncestor (generatedRib ns (cause, k)).entries sIdx _jIdx)
     (hsBorn : frames[sIdx + 1]? = some sBorn)
     (hnS : ns[S.node]? = some nS) :
     ∀ (b : Nat) (_hchain : IndexedAncestor (generatedRib ns (cause, k)).entries sIdx b)
       (bE : Entry) (bBorn : Bone),
       (generatedRib ns (cause, k)).entries[b]? = some bE →
       frames[b + 1]? = some bBorn →
       ((bE.depth % 2 = 1 → DescOddBound sBorn bBorn) ∧
         (bE.depth % 2 = 0 → DescEvenBound sBorn bBorn)) := by
   let r := effectivePlacedInput ns (measuredSideLength p ribs)
     (generatedRib ns (cause, k))
   let E := (generatedRib ns (cause, k)).entries
   have hErLen : r.entries.length = E.length := rfl
   have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw _hrun
   have hflen : frames.length = E.length + 1 := by
     obtain ⟨_, _, _, _, _, hlen, _, _, _⟩ := hconfig
     have hlen' : frames.length = r.entries.length + 1 := hlen
     omega
   intro b hchain
   refine IndexedAncestor.rec (motive := fun b _ => ∀ (bE : Entry) (bBorn : Bone),
     E[b]? = some bE →
     frames[b + 1]? = some bBorn →
     ((bE.depth % 2 = 1 → DescOddBound sBorn bBorn) ∧
       (bE.depth % 2 = 0 → DescEvenBound sBorn bBorn))) ?_ ?_ hchain
   · intro tgt ch hch hp bE bBorn hbE hbBorn
     have heq : bE = ch := Option.some.inj (hbE.symm.trans hch)
     subst heq
     have hSmem : (S, sIdx) ∈ E.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hS
     have hSodd := descEnv_sOdd ns p raw _hrun ribs _hg cause k _hsource _hcause
       spine placed hplace _env child _j childIdx _jIdx _nj frames _childBorn
       _jBorn sBorn sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
     have hmodS := Nat.mod_lt S.depth (by decide : 0 < 2)
     have hS1 : S.depth % 2 = 1 := by omega
     have hbase := descEnv_base ns p raw _hrun ribs _hg cause k _hsource _hcause
       spine placed hplace _env child _j childIdx _jIdx _nj frames _childBorn
       _jBorn sBorn sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
     have hQS : ((S.depth % 2 = 1 → DescOddBound sBorn sBorn) ∧
         (S.depth % 2 = 0 → DescEvenBound sBorn sBorn)) :=
       ⟨fun _ => hbase, fun h => absurd h hSodd⟩
     have hdepb : bE.depth = S.depth + 1 :=
       generated_parent_child_depth ns cause k hlink _hcause S bE sIdx
         tgt hSmem (List.mem_zipIdx_iff_getElem?.mpr hch) hp
     have hmodC := Nat.mod_lt bE.depth (by decide : 0 < 2)
     have hbeven : bE.depth % 2 = 0 := by omega
     exact descEnv_step_even ns p raw _hrun ribs _hg cause k _hsource _hcause
       spine placed hplace _env child _j childIdx _jIdx _nj frames _childBorn
       _jBorn sBorn sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
       sIdx tgt S bE sBorn bBorn hS hch hp
       (IndexedAncestor.edge _ _ bE hch hp) hsBorn hbBorn hQS hbeven
   · intro mid c hab ch hch hp ih bE bBorn hbE hbBorn
     have heq : bE = ch := Option.some.inj (hbE.symm.trans hch)
     subst heq
     obtain ⟨midE, hmidE⟩ := descEnv_chain_entry E sIdx mid hab
     obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hmidE
     have hlt' : mid + 1 < frames.length := by omega
     have hmidF : frames[mid + 1]? = some frames[mid + 1] :=
       List.getElem?_eq_getElem hlt'
     have hQmid := ih midE _ hmidE hmidF
     by_cases heven : bE.depth % 2 = 0
     · exact descEnv_step_even ns p raw _hrun ribs _hg cause k _hsource _hcause
         spine placed hplace _env child _j childIdx _jIdx _nj frames _childBorn
         _jBorn sBorn sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
         mid c midE bE _ bBorn hmidE hch hp
         (IndexedAncestor.tail hab bE hch hp) hmidF hbBorn hQmid heven
     · have hne : bE.depth % 2 ≠ 0 := heven
       exact descEnv_step_odd ns p raw _hrun ribs _hg cause k _hsource _hcause
         spine placed hplace _env child _j childIdx _jIdx _nj frames _childBorn
         _jBorn sBorn sIdx S nS hconfig hreal hS _hsne hSP _hchain hsBorn hnS
         mid c midE bE _ bBorn hmidE hch hp
         (IndexedAncestor.tail hab bE hch hp) hmidF hbBorn hQmid hne

 /-- The residual `HardBDeeperDescEnvelope` holds on the executed rib, with no
 residual hypothesis: time containment plus the sibling-line bound reach every
 indexed descendant by `descEnv_induct`; the endpoint cases discharge the
 envelope conjunction (odd needs the self-line identity via exact division). -/
 theorem hardBDeeperDescEnvelope (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout)
     (_hrun : layout ns p = .ok raw)
     (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
     (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
     (hplace : place ns p spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) = .ok placed)
     (_env : IshikawaEnvFrames ns p
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k)))) :
     HardBDeeperDescEnvelope ns p raw _hrun ribs _hg cause k _hsource _hcause
       spine placed hplace _env := by
   intro child j childIdx jIdx nj frames childBorn jBorn sBorn sIdx S nS
     hconfig hreal hS hsne hSP hchain hsBorn hnS
   let r := effectivePlacedInput ns (measuredSideLength p ribs)
     (generatedRib ns (cause, k))
   let E := (generatedRib ns (cause, k)).entries
   have hErLen : r.entries.length = E.length := rfl
   have hjMem : (j, jIdx) ∈ E.zipIdx := by
     obtain ⟨_, hj, _, _, _, _, _, _, _⟩ := hconfig
     exact hj
   have hjE : E[jIdx]? = some j := List.mem_zipIdx_iff_getElem?.mp hjMem
   have hjBorn : frames[jIdx + 1]? = some jBorn := by
     obtain ⟨_, _, _, _, _, _, _, hjB, _⟩ := hconfig
     exact hjB
   have hDb := descEnv_induct ns p raw _hrun ribs _hg cause k _hsource _hcause
     spine placed hplace _env child j childIdx jIdx nj frames childBorn jBorn
     sBorn sIdx S nS hconfig hreal hS hsne hSP hchain hsBorn hnS jIdx hchain j
     jBorn hjE hjBorn
   by_cases hjodd : j.depth % 2 = 1
   · obtain ⟨hspan, hlo, hhi, hline⟩ := hDb.1 hjodd
     refine ⟨by omega, hhi, ?_⟩
     have hne : jBorn.t1 - jBorn.t0 ≠ 0 := by omega
     have hmul := Int.mul_fdiv_cancel (jBorn.x1 - jBorn.x0) hne
     have hself : descLineOf jBorn jBorn.t1 = jBorn.x1 := by
       simp only [descLineOf]
       omega
     have hlj := hline jBorn.t1 (by omega) (by omega)
     rw [hself] at hlj
     exact hlj
   · have hmod := Nat.mod_lt j.depth (by decide : 0 < 2)
     have hjeven : j.depth % 2 = 0 := by omega
     obtain ⟨hlo, hhi, _, hx1⟩ := hDb.2 hjeven
     exact ⟨hlo, hhi, hx1⟩

 /-- `HardBDeeperEnvTransport` with no residual hypothesis, via
 `hardBDeeperEnvTransport''` plus the proved envelope. -/
 theorem hardBDeeperEnvTransport''' (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout)
     (_hrun : layout ns p = .ok raw)
     (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
     (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
     (hplace : place ns p spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) = .ok placed)
     (_env : IshikawaEnvFrames ns p
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k)))) :
     HardBDeeperEnvTransport ns p raw _hrun ribs _hg cause k _hsource _hcause
       spine placed hplace _env :=
   hardBDeeperEnvTransport'' ns p raw _hrun ribs _hg cause k _hsource _hcause
     spine placed hplace _env
     (hardBDeeperDescEnvelope ns p raw _hrun ribs _hg cause k _hsource _hcause
       spine placed hplace _env)

end Elegant.Ishikawa

import Elegant.Kinds.IshikawaDescRouteClearance
import Elegant.IshikawaDeeperGapOnlyProof
import Elegant.Chart.Scale

set_option autoImplicit false
open Elegant
namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-! ### Descendant frame gap over executed birth frames

Proves `DescendantFrameGap` (from `Elegant.Kinds.IshikawaDescRouteClearance`):
for the executed birth frames of the placed rib, a strict descendant `J` of
an odd-depth entry `I` satisfies the fall equation for `I` and the
interpolated reservation gap. All statements speak of executed birth frames
only (`BirthFramesShape`-style premises); nothing quantifies over an
arbitrary genealogy.

Proof outline: one-step lemmas for a single birth step (even child,
odd child), then induction on `IndexedAncestor` with a parity-dispatched
domination motive, then the gap conclusion per parity.
-/

/-- Slope parameters from a successful layout (local copy of the private
`IshikawaClearanceFacts.successful_slope_parameters`). -/
private theorem dfg_slope_parameters (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hne : ns ≠ []) (hrun : layout ns p = .ok raw) :
    0 ≤ p.cos ∧ 1 ≤ p.sin := by
  cases ns with
  | nil => exact False.elim (hne rfl)
  | cons head rest =>
    unfold layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    split at hrun
    · simp only [bind, Except.bind] at hrun
      cases hrun
    · split at hrun
      · simp only [bind, Except.bind] at hrun
        cases hrun
      · rename_i hparameters
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hparameters
        omega

/-- Even parent depth (local copy of the private
`IshikawaClearanceFacts.parent_depth_even`). -/
private theorem dfg_parent_depth_even (parent child : Nat) (hd : child = parent + 1)
    (hodd : child % 2 ≠ 0) : parent % 2 = 0 := by
  have hm := Nat.mod_lt parent (by decide : 0 < 2)
  omega

/-- Slope-residual upper bound for `run` (local copy of the private
`IshikawaClearanceHardBClose.sin_run_le`). -/
private theorem dfg_sin_run_le (p : Params) (x : Int) (_hx : 0 ≤ x)
    (_hcos : 0 ≤ p.cos) (hsin : 1 ≤ p.sin) :
    p.sin * run p x ≤ x * p.cos := by
  unfold run
  have h := Int.mul_fdiv_add_fmod (x * p.cos) p.sin
  have h2 := Int.fmod_nonneg_of_pos (x * p.cos) (show (0 : Int) < p.sin by omega)
  omega

/-- Slope-residual lower bound for `run` (local copy of the private
`IshikawaClearanceHardBClose.sin_run_ge`). -/
private theorem dfg_sin_run_ge (p : Params) (x : Int) (_hx : 0 ≤ x)
    (_hcos : 0 ≤ p.cos) (hsin : 1 ≤ p.sin) :
    x * p.cos - p.sin + 1 ≤ p.sin * run p x := by
  unfold run
  have h := Int.mul_fdiv_add_fmod (x * p.cos) p.sin
  have h2 := Int.fmod_lt_of_pos (x * p.cos) (show (0 : Int) < p.sin by omega)
  omega

set_option maxHeartbeats 1000000 in
/-- One falling bone-line drops at most `run + 1` over any sub-interval.
Pure floor arithmetic about a single line (local copy of the private
`descEnv_line_drop`). -/
private theorem dfg_line_drop (p : Params) (hcos : 0 ≤ p.cos)
    (hsin : 1 ≤ p.sin) (x0 t0 Sp u v : Int) (hSp : 0 < Sp)
    (_hlo : t0 ≤ u) (huv : u ≤ v) :
    (x0 + Int.fdiv (-(run p Sp * (u - t0))) Sp) -
      (x0 + Int.fdiv (-(run p Sp * (v - t0))) Sp) ≤ run p (v - u) + 1 := by
  have hsin0 : 0 < p.sin := by omega
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
    dfg_sin_run_le p Sp (by omega) hcos hsin
  have hrunD : (v - u) * p.cos - p.sin + 1 ≤ p.sin * run p (v - u) :=
    dfg_sin_run_ge p (v - u) (by omega) hcos hsin
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
Pure floor arithmetic about a single falling line (local copy of the private
`descEnv_fall_lb`). -/
private theorem dfg_fall_lb (p : Params) (hcos : 0 ≤ p.cos)
    (hsin : 1 ≤ p.sin) (Sd b : Int) (hSd : 0 < Sd)
    (hb0 : 0 ≤ b) (hbSd : b ≤ Sd) :
    run p b - 1 ≤ -(Int.fdiv (-(run p Sd * b)) Sd) := by
  have hsin0 : 0 < p.sin := by omega
  have hge : Sd * p.cos - p.sin + 1 ≤ p.sin * run p Sd :=
    dfg_sin_run_ge p Sd (by omega) hcos hsin
  have hle : p.sin * run p b ≤ b * p.cos :=
    dfg_sin_run_le p b hb0 hcos hsin
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
    Elegant.Chart.fdiv_le_of_le_mul hSd hbridge
  omega

private theorem dfg_native_reservation (p : Params) (par : Bone) (depth : Nat)
     (t : Int) (count : Nat) (margin : Int) (hd : depth % 2 = 0) :
     0 < (depthBone p par depth t count margin).count + 1 ∧
     (((depthBone p par depth t count margin).count + 1) * margin ≤
       (depthBone p par depth t count margin).x0 -
         (depthBone p par depth t count margin).x1) := by
   have hc : (depthBone p par depth t count margin).count = (count : Int) := by
     unfold depthBone
     split <;> rfl
   have he := (depthBone_even_endpoints p par depth t count margin hd).2.2
   have hr : ((count : Int) + 1) * margin ≤ boneLength p count margin :=
     Int.le_max_right _ _
   constructor
   · rw [hc]
     omega
   · rw [hc, he]
     omega
 /-- Odd-birth attachment margin (local copy of the private
 `IshikawaClearanceFacts.attachment_start_margin`). -/
private theorem dfg_attach_start_margin (left right count drawn margin : Int)
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
  have hquot := Elegant.Chart.fdiv_le_of_le_mul hden hbound
  omega


/-- Ancestor chains compose. -/
private theorem dfg_trans {E : List Entry} {a b c : Nat}
    (hab : IndexedAncestor E a b) (hbc : IndexedAncestor E b c) :
    IndexedAncestor E a c := by
  induction hbc with
  | edge _ e he hp => exact IndexedAncestor.tail hab e he hp
  | tail _ e he hp ih => exact IndexedAncestor.tail ih e he hp

/-- Exact division of a negated product (floor of an exact multiple). -/
private theorem dfg_fdiv_exact_neg_mul (R S : Int) (hS : 0 < S) :
    Int.fdiv (-(R * S)) S = -R := by
  have e : S * (-R) = -(R * S) := by
    rw [Int.mul_neg, Int.mul_comm S R]
  have h1 : -R ≤ Int.fdiv (-(R * S)) S :=
    Elegant.Chart.le_fdiv_of_mul_le hS (by omega)
  have h2 : Int.fdiv (-(R * S)) S ≤ -R :=
    Elegant.Chart.fdiv_le_of_le_mul hS (by omega)
  omega

/-- Interpolated bone-line value at ordinate `t`, matching the even-birth
attachment shape (`depthBone`). -/
def dfgLineOf (b : Bone) (t : Int) : Int :=
  b.x0 + Int.fdiv ((b.x1 - b.x0) * (t - b.t0)) (b.t1 - b.t0)

/-- Domination invariant for an odd descendant bone: positive span inside the
ancestor span, plus pointwise line domination over its own span. -/
def dfgOddBound (S b : Bone) : Prop :=
  0 < b.t1 - b.t0 ∧ S.t0 ≤ b.t0 ∧ b.t1 ≤ S.t1 ∧
    ∀ t, b.t0 ≤ t → t ≤ b.t1 → dfgLineOf b t ≤ dfgLineOf S t

/-- Domination invariant for an even descendant bone: its (point) span lies
inside the ancestor span and both ends lie on or left of the ancestor line. -/
def dfgEvenBound (S b : Bone) : Prop :=
  S.t0 ≤ b.t1 ∧ b.t1 ≤ S.t1 ∧
    b.x0 ≤ dfgLineOf S b.t1 ∧ b.x1 ≤ dfgLineOf S b.t1

/-- Parity-dispatched domination invariant for a descendant bone. -/
def dfgBound (S : Bone) (e : Entry) (b : Bone) : Prop :=
  (e.depth % 2 = 1 → dfgOddBound S b) ∧
    (e.depth % 2 = 0 → dfgEvenBound S b)

/-- Every generated-rib entry node is a valid node. Induction on entry depth,
mirroring the parent-chase of `frames_entry_node_gt_cause` but concluding
node validity from the executed birth records. -/
private theorem dfg_entry_node_valid (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0)
    (frames : List Bone)
    (hlen : frames.length =
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).entries.length + 1)
    (hrecords : ∀ (done : List (Entry × Nat)) (e : Entry) (idx : Nat)
      (rest : List (Entry × Nat)),
      (generatedRib ns (cause, k)).entries.zipIdx = done ++ (e, idx) :: rest →
      ∃ (pos : Nat × Nat) (parent born : Bone),
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k))).order.zipIdx.find?
          (fun v => v.1 == idx) = some pos ∧
        frames[(e.parent + 1).toNat]? = some parent ∧
        frames[idx + 1]? = some born ∧
        born = depthBone p
          { parent with drawn := processedOddDraws done (e.parent + 1).toNat }
          e.depth (Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
            (generatedRib ns (cause, k))).length * (pos.2 + 1 : Nat))
            ((effectivePlacedInput ns (measuredSideLength p ribs)
              (generatedRib ns (cause, k))).entries.length + 1 : Nat))
          (children ns e.node).length (run p (effectivePlacedInput ns
            (measuredSideLength p ribs)
            (generatedRib ns (cause, k))).heights + 3)) :
    ∀ (e : Entry) (idx : Nat),
      (e, idx) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
      ∃ n, ns[e.node]? = some n := by
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hErLen : (effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))).entries.length =
      (generatedRib ns (cause, k)).entries.length := rfl
  suffices key : ∀ d (e : Entry) (idx : Nat), e.depth = d →
      (e, idx) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
      ∃ n, ns[e.node]? = some n by
    exact fun e idx he => key e.depth e idx rfl he
  intro d
  induction d with
  | zero =>
    intro e idx hd her
    by_cases hroot : e.parent = -1
    · have hn := generated_root_child_membership ns cause k e idx her hroot
      have hlt : e.node < ns.length :=
        List.mem_range.mp (List.mem_filter.mp hn).1
      exact ⟨_, List.getElem?_eq_getElem hlt⟩
    · obtain ⟨done, rest, hpre, _⟩ := List.eq_append_cons_of_mem her
      obtain ⟨_pos, _parB, _bornB, _hposF, hparF, _hbornF, _hbornEq⟩ :=
        hrecords done e idx rest hpre
      have hlt : (e.parent + 1).toNat < frames.length :=
        (List.getElem?_eq_some_iff.mp hparF).1
      rw [hlen, hErLen] at hlt
      have hge : 0 ≤ e.parent := by
        have hlb := generated_entry_parent_lower_bound ns cause k e idx her
        omega
      have hbound : (e.parent).toNat <
          (generatedRib ns (cause, k)).entries.length := by omega
      obtain ⟨pE, hpEGet⟩ : ∃ pE,
          (generatedRib ns (cause, k)).entries[(e.parent).toNat]? = some pE :=
        ⟨_, List.getElem?_eq_getElem hbound⟩
      have hpmem : (pE, (e.parent).toNat) ∈
          (generatedRib ns (cause, k)).entries.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hpEGet
      have hparEq : e.parent = (((e.parent).toNat : Nat) : Int) := by omega
      have hdepth := generated_parent_child_depth ns cause k hlink hcause
        pE e (e.parent).toNat idx hpmem her hparEq
      omega
  | succ d ih =>
    intro e idx hd her
    by_cases hroot : e.parent = -1
    · have hn := generated_root_child_membership ns cause k e idx her hroot
      have hlt : e.node < ns.length :=
        List.mem_range.mp (List.mem_filter.mp hn).1
      exact ⟨_, List.getElem?_eq_getElem hlt⟩
    · obtain ⟨done, rest, hpre, _⟩ := List.eq_append_cons_of_mem her
      obtain ⟨_pos, _parB, _bornB, _hposF, hparF, _hbornF, _hbornEq⟩ :=
        hrecords done e idx rest hpre
      have hlt : (e.parent + 1).toNat < frames.length :=
        (List.getElem?_eq_some_iff.mp hparF).1
      rw [hlen, hErLen] at hlt
      have hge : 0 ≤ e.parent := by
        have hlb := generated_entry_parent_lower_bound ns cause k e idx her
        omega
      have hbound : (e.parent).toNat <
          (generatedRib ns (cause, k)).entries.length := by omega
      obtain ⟨pE, hpEGet⟩ : ∃ pE,
          (generatedRib ns (cause, k)).entries[(e.parent).toNat]? = some pE :=
        ⟨_, List.getElem?_eq_getElem hbound⟩
      have hpmem : (pE, (e.parent).toNat) ∈
          (generatedRib ns (cause, k)).entries.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hpEGet
      have hparEq : e.parent = (((e.parent).toNat : Nat) : Int) := by omega
      have hdepth := generated_parent_child_depth ns cause k hlink hcause
        pE e (e.parent).toNat idx hpmem her hparEq
      have hpd : pE.depth = d := by omega
      obtain ⟨n, hn⟩ := ih pE (e.parent).toNat hpd hpmem
      have hcmem := generated_parent_child_membership ns cause k pE e
        (e.parent).toNat idx hpmem her hparEq
      have hltN : e.node < ns.length :=
        List.mem_range.mp (List.mem_filter.mp hcmem).1
      exact ⟨_, List.getElem?_eq_getElem hltN⟩

/-- Executed odd-draw budget: the drawn counter of any birth prefix is bounded
by the owner node's child count (pure frames version via
`generated_prefix_odd_child_count_le`). -/
private theorem dfg_drawn_le (ns : List Tree.Node)
    (cause k : Nat) (hlink : Tree.link ns = true)
    (hcause : cause ∈ children ns 0)
    (done rest : List (Entry × Nat))
    (hprefix : (generatedRib ns (cause, k)).entries.zipIdx = done ++ rest)
    (owner ownerNode : Nat)
    (howner : (owner = 0 ∧ ownerNode = cause) ∨
      ∃ parentEntry parentIdx,
        (parentEntry, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx ∧
        owner = parentIdx + 1 ∧ ownerNode = parentEntry.node) :
    processedOddDraws done owner ≤ ((children ns ownerNode).length : Int) := by
  have hnat := generated_prefix_odd_child_count_le ns cause k hlink hcause
    done rest hprefix owner ownerNode howner
  unfold processedOddDraws
  omega

/-- Slot package for the odd entry `I`: order positions, slot equations, span,
gap, fall, height bound, and reservation budget, all from the executed records.
Mirrors `descEnv_sSetup` with `I` itself as the base (no sibling config). -/
private theorem dfg_slot_setup (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0)
    (eI : Entry) (idxI : Nat)
    (hmemI : (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : eI.depth % 2 ≠ 0)
    (frames : List Bone)
    (hlen : frames.length =
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).entries.length + 1)
    (hrecords : ∀ (done : List (Entry × Nat)) (e : Entry) (idx : Nat)
      (rest : List (Entry × Nat)),
      (generatedRib ns (cause, k)).entries.zipIdx = done ++ (e, idx) :: rest →
      ∃ (pos : Nat × Nat) (parent born : Bone),
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k))).order.zipIdx.find?
          (fun v => v.1 == idx) = some pos ∧
        frames[(e.parent + 1).toNat]? = some parent ∧
        frames[idx + 1]? = some born ∧
        born = depthBone p
          { parent with drawn := processedOddDraws done (e.parent + 1).toNat }
          e.depth (Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
            (generatedRib ns (cause, k))).length * (pos.2 + 1 : Nat))
            ((effectivePlacedInput ns (measuredSideLength p ribs)
              (generatedRib ns (cause, k))).entries.length + 1 : Nat))
          (children ns e.node).length (run p (effectivePlacedInput ns
            (measuredSideLength p ribs)
            (generatedRib ns (cause, k))).heights + 3))
    (fI : Bone) (hlookI : frames[idxI + 1]? = some fI) :
    ∃ (posI posP : Nat × Nat) (pE : Entry) (parI : Bone),
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).order.zipIdx.find?
        (fun v => v.1 == idxI) = some posI ∧
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).order.zipIdx.find?
        (fun v => v.1 == (eI.parent).toNat) = some posP ∧
      (pE, (eI.parent).toNat) ∈ (generatedRib ns (cause, k)).entries.zipIdx ∧
      pE.depth % 2 = 0 ∧
      frames[(eI.parent + 1).toNat]? = some parI ∧
      fI.t0 = Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).length * (posP.2 + 1 : Nat))
        (((generatedRib ns (cause, k)).entries.length + 1 : Nat) : Int) ∧
      fI.t1 = Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).length * (posI.2 + 1 : Nat))
        (((generatedRib ns (cause, k)).entries.length + 1 : Nat) : Int) ∧
      fI.x1 - fI.x0 = -run p (fI.t1 - fI.t0) ∧
      fI.t0 < fI.t1 ∧
      fI.x1 ≤ fI.x0 ∧
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
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hne : ns ≠ [] := by
    intro heq
    simp [heq, children] at hcause
  have hparams := dfg_slope_parameters ns p raw hne hrun
  have hcos : 0 ≤ p.cos := hparams.1
  have hsin0 : 0 < p.sin := by have h1 := hparams.2; omega
  have hHr : r.heights = (generatedRib ns (cause, k)).heights := rfl
  have hErLen : r.entries.length = E.length := rfl
  obtain ⟨doneI, restI, hpreI, _⟩ := List.eq_append_cons_of_mem hmemI
  obtain ⟨posI, parI, bornI, hfindI, hparI, hbornI, heqI⟩ :=
    hrecords doneI eI idxI restI hpreI
  have hbornIeq : bornI = fI := Option.some.inj (hbornI.symm.trans hlookI)
  have hClb : -1 ≤ eI.parent :=
    generated_entry_parent_lower_bound ns cause k eI idxI hmemI
  have hrootFalse : eI.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink hcause eI idxI hmemI heq
    omega
  have hCParNat : eI.parent = (((eI.parent).toNat : Nat) : Int) := by omega
  have hown1 : (eI.parent + 1).toNat = (eI.parent).toNat + 1 := by omega
  rw [hown1] at hparI
  have hlen0 : frames.length = r.entries.length + 1 := hlen
  have hpELT : (eI.parent).toNat < E.length := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hparI
    omega
  obtain ⟨pE, hpEGet⟩ : ∃ pE, E[(eI.parent).toNat]? = some pE :=
    ⟨_, List.getElem?_eq_getElem hpELT⟩
  have hpmemP : (pE, (eI.parent).toNat) ∈ E.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hpEGet
  have hdepthI := generated_parent_child_depth ns cause k hlink hcause
    pE eI (eI.parent).toNat idxI hpmemP hmemI hCParNat
  have hpeven : pE.depth % 2 = 0 :=
    dfg_parent_depth_even pE.depth eI.depth hdepthI hodd
  obtain ⟨doneP, restP, hpreP, _⟩ := List.eq_append_cons_of_mem hpmemP
  obtain ⟨posP, _parP, bornP, hfindP, _hparP, hbornP, heqP⟩ :=
    hrecords doneP pE (eI.parent).toNat restP hpreP
  have hparIeq : parI = bornP := by
    have h1 : frames[(eI.parent).toNat + 1]? = some parI := hparI
    exact Option.some.inj (h1.symm.trans hbornP)
  have hfIt0 : fI.t0 = parI.t0 := by
    rw [← hbornIeq, heqI]
    exact (depthBone_odd_endpoints p _ eI.depth _ _ _ hodd).1
  have hfIt1 : fI.t1 =
      Int.fdiv (r.length * (posI.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [← hbornIeq, heqI]
    exact (depthBone_odd_endpoints p _ eI.depth _ _ _ hodd).2.1
  have hparPt0 : parI.t0 =
      Int.fdiv (r.length * (posP.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hparIeq, heqP]
    exact (depthBone_even_endpoints p _ pE.depth _ _ _ hpeven).1
  have hparPt1 : parI.t1 =
      Int.fdiv (r.length * (posP.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hparIeq, heqP]
    exact (depthBone_even_endpoints p _ pE.depth _ _ _ hpeven).2.1
  have hfIx1 : fI.x1 = fI.x0 - run p (fI.t1 - parI.t0) := by
    rw [← hbornIeq, heqI, (depthBone_odd_endpoints p _ eI.depth _ _ _ hodd).2.1]
    simpa using (depthBone_odd_endpoints p _ eI.depth _ _ _ hodd).2.2.2
  have hordIP := generated_parent_child_order ns cause k pE eI
    (eI.parent).toNat idxI hpmemP hmemI hCParNat posP posI hfindP hfindI
  have hposLT : posP.2 < posI.2 := (hordIP.1 hpeven)
  obtain ⟨nI, hnI⟩ := dfg_entry_node_valid ns p raw hrun ribs hg cause k
    hsource hcause frames hlen hrecords eI idxI hmemI
  have hmemN : nI ∈ ns := List.mem_of_getElem? hnI
  have hdims := successful_node_dimensions ns p raw hrun nI hmemN
  have hHbound := measured_entry_height_bound ns E eI
    (List.fst_mem_of_mem_zipIdx hmemI) nI hnI
  have hH1 : 1 ≤ r.heights := by
    have hgen : r.heights = (generatedRib ns (cause, k)).heights := rfl
    have hrib := (generated_rib_fields ns cause k).2.2.2
    have hEfold : E.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 =
        (generatedRib ns (cause, k)).entries.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := rfl
    have hd1 : 1 ≤ nI.height := hdims.2
    omega
  have hHnn : 0 ≤ r.heights := by omega
  have hbudget : (((E.length + 1 : Nat) : Int) * r.heights ≤ r.length) := by
    have hmemI' : (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
      hmemI
    have hneE : (generatedRib ns (cause, k)).entries.isEmpty = false := by
      cases hentries : (generatedRib ns (cause, k)).entries with
      | nil =>
        rw [hentries] at hmemI'
        exact absurd hmemI' (by simp)
      | cons _ _ => rfl
    have hb := generated_reservation_budget ns p ribs hg
      (generatedRib ns (cause, k)) hsource hneE
    have hden : ((E.length + 1 : Nat) : Int) =
      (((generatedRib ns (cause, k)).entries.length + 1 : Nat) : Int) := rfl
    have hHr2 : r.heights = (generatedRib ns (cause, k)).heights := rfl
    rw [hden, hHr2]
    exact hb
  have hslotGap : Int.fdiv (r.length * (posP.2 + 1 : Nat))
      (r.entries.length + 1 : Nat) + r.heights ≤
      Int.fdiv (r.length * (posI.2 + 1 : Nat))
      (r.entries.length + 1 : Nat) := by
    have hlenD : 0 < ((r.entries.length + 1 : Nat) : Int) := by omega
    have hlt : (posP.2 + 1 : Nat) + 1 ≤ (posI.2 + 1 : Nat) := by omega
    have hErLen2 : r.entries.length =
        (generatedRib ns (cause, k)).entries.length := rfl
    exact ordinal_slots_gap r.length ((r.entries.length + 1 : Nat) : Int)
      r.heights ((posP.2 + 1 : Nat) : Int) ((posI.2 + 1 : Nat) : Int) hlenD hHnn
      (by rw [hErLen2, hHr]; exact hbudget) (by omega)
  have hfIt0slot : fI.t0 = Int.fdiv (r.length * (posP.2 + 1 : Nat))
      (((E.length + 1 : Nat) : Int)) := by
    rw [hfIt0, hparPt0, hErLen]
  have hfIt1slot : fI.t1 = Int.fdiv (r.length * (posI.2 + 1 : Nat))
      (((E.length + 1 : Nat) : Int)) := by
    rw [hfIt1, hErLen]
  have hslotGapE : Int.fdiv (r.length * (posP.2 + 1 : Nat))
      (((E.length + 1 : Nat) : Int)) + r.heights ≤
      Int.fdiv (r.length * (posI.2 + 1 : Nat))
      (((E.length + 1 : Nat) : Int)) := by
    rw [← hErLen]
    exact hslotGap
  have hspan : fI.t0 < fI.t1 := by omega
  have hfall : fI.x1 - fI.x0 = -run p (fI.t1 - fI.t0) := by
    rw [hfIx1, hfIt0]
    omega
  have hxle : fI.x1 ≤ fI.x0 := by
    have hrunNN : 0 ≤ run p (fI.t1 - fI.t0) :=
      Int.fdiv_nonneg (Int.mul_nonneg (by omega) hcos) (Int.le_of_lt hsin0)
    omega
  have hparIfin : frames[(eI.parent + 1).toNat]? = some parI := by
    rw [hown1]
    exact hparI
  exact ⟨posI, posP, pE, parI, hfindI, hfindP, hpmemP, hpeven, hparIfin,
    hfIt0slot, hfIt1slot, hfall, hspan, hxle, hH1, hbudget⟩

 /-- Time containment of any descendant bone inside the odd entry's span.
 Direct from ancestor order plus slot gaps (no induction). -/
 private theorem dfg_contain (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
     (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
     (_hcause : cause ∈ children ns 0)
     (eI : Entry) (idxI : Nat) (fI : Bone)
     (hmemI : (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hodd : eI.depth % 2 ≠ 0)
     (posI posP : Nat × Nat) (pE : Entry)
     (hfindI : (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).order.zipIdx.find?
       (fun v => v.1 == idxI) = some posI)
     (hfindP : (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).order.zipIdx.find?
       (fun v => v.1 == (eI.parent).toNat) = some posP)
     (hpmemP : (pE, (eI.parent).toNat) ∈
       (generatedRib ns (cause, k)).entries.zipIdx)
     (hpeven : pE.depth % 2 = 0)
     (hfIt0slot : fI.t0 = Int.fdiv ((effectivePlacedInput ns
       (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posP.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int))
     (hfIt1slot : fI.t1 = Int.fdiv ((effectivePlacedInput ns
       (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posI.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int))
     (hHnn : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights)
     (hbl : ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) *
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights ≤
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).length)
     (b : Nat) (bE : Entry) (bBorn : Bone) (posB : Nat × Nat)
     (hmemB : (bE, b) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hfindB : (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).order.zipIdx.find?
       (fun v => v.1 == b) = some posB)
     (hchainB : IndexedAncestor (generatedRib ns (cause, k)).entries idxI b)
     (hslotB : bBorn.t1 = Int.fdiv ((effectivePlacedInput ns
       (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posB.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int)) :
     fI.t0 ≤ bBorn.t1 ∧ bBorn.t1 ≤ fI.t1 := by
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hrootFalse : eI.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink _hcause eI idxI hmemI heq
    omega
  have hCParNat : eI.parent = (((eI.parent).toNat : Nat) : Int) := by
    have hlb := generated_entry_parent_lower_bound ns cause k eI idxI hmemI
    omega
  have hmemIget : (generatedRib ns (cause, k)).entries[idxI]? = some eI :=
     List.mem_zipIdx_iff_getElem?.mp hmemI
  have hchainPI : IndexedAncestor (generatedRib ns (cause, k)).entries
       (eI.parent).toNat b :=
     dfg_trans (IndexedAncestor.edge _ _ eI hmemIget hCParNat) hchainB
  have hordU := generated_ancestor_order ns cause k eI bE idxI b
     hmemI hmemB hchainB posI posB hfindI hfindB
  have hposBU : posB.2 < posI.2 := hordU.2 hodd
  have hslotU : Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posB.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) +
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights ≤
       Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posI.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) := by
     have hlenD : 0 < (((((generatedRib ns (cause, k)).entries.length + 1 : Nat))) : Int) := by
       omega
     have hlt : (posB.2 + 1 : Nat) + 1 ≤ (posI.2 + 1 : Nat) := by omega
     exact ordinal_slots_gap _ _ _ ((posB.2 + 1 : Nat) : Int)
       ((posI.2 + 1 : Nat) : Int) hlenD hHnn hbl (by omega)
  have hordL := generated_ancestor_order ns cause k pE bE (eI.parent).toNat b
     hpmemP hmemB hchainPI posP posB hfindP hfindB
  have hposLB : posP.2 < posB.2 := hordL.1 hpeven
  have hslotL : Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posP.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) +
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights ≤
       Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posB.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) := by
     have hlenD : 0 < (((((generatedRib ns (cause, k)).entries.length + 1 : Nat))) : Int) := by
       omega
     have hlt : (posP.2 + 1 : Nat) + 1 ≤ (posB.2 + 1 : Nat) := by omega
     exact ordinal_slots_gap _ _ _ ((posP.2 + 1 : Nat) : Int)
       ((posB.2 + 1 : Nat) : Int) hlenD hHnn hbl (by omega)
  omega

 /-- Peel the last ancestor edge: every chain ends in a parent index that is
 either the start or chained itself. Cases-based so the middle index never
 needs a name at the use site. -/
 private theorem dfg_parent_chain {E : List Entry} {a c : Nat}
     (h : IndexedAncestor E a c) (cE : Entry) (hc : E[c]? = some cE) :
     ∃ b : Nat, cE.parent = (b : Int) ∧ (b = a ∨ IndexedAncestor E a b) := by
   cases h with
   | edge _ cE' hc' hpar =>
     have hcEeq : cE' = cE := Option.some.inj (hc'.symm.trans hc)
     have hparC : cE.parent = (a : Int) := by
       rw [← hcEeq]
       exact hpar
     exact ⟨a, hparC, Or.inl rfl⟩
   | tail hab cE' hc' hpar =>
     have hcEeq : cE' = cE := Option.some.inj (hc'.symm.trans hc)
     refine ⟨_, ?_, Or.inr hab⟩
     rw [← hcEeq]
     exact hpar

 /-- Executed birth facts for an odd child of an even bone: slot equations,
 attachment equation, fall, slot gap, drawn budget, and native reservation.
 No chain hypotheses needed. -/
 private theorem dfg_odd_child_facts (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
     (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
     (_hcause : cause ∈ children ns 0)
     (hHnn : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights)
     (hbl : ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) *
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights ≤
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).length)
     (frames : List Bone)
     (_hlen : frames.length =
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).entries.length + 1)
     (hrecords : ∀ (done : List (Entry × Nat)) (e : Entry) (idx : Nat)
       (rest : List (Entry × Nat)),
       (generatedRib ns (cause, k)).entries.zipIdx = done ++ (e, idx) :: rest →
       ∃ (pos : Nat × Nat) (parent born : Bone),
         (effectivePlacedInput ns (measuredSideLength p ribs)
           (generatedRib ns (cause, k))).order.zipIdx.find?
           (fun v => v.1 == idx) = some pos ∧
         frames[(e.parent + 1).toNat]? = some parent ∧
         frames[idx + 1]? = some born ∧
         born = depthBone p
           { parent with drawn := processedOddDraws done (e.parent + 1).toNat }
           e.depth (Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
             (generatedRib ns (cause, k))).length * (pos.2 + 1 : Nat))
             ((effectivePlacedInput ns (measuredSideLength p ribs)
               (generatedRib ns (cause, k))).entries.length + 1 : Nat))
           (children ns e.node).length (run p (effectivePlacedInput ns
             (measuredSideLength p ribs)
             (generatedRib ns (cause, k))).heights + 3))
     (b c : Nat) (bE cE : Entry) (bBorn cBorn : Bone)
     (hmemB : (bE, b) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hmemC : (cE, c) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hpar : cE.parent = (b : Int))
     (hframesB : frames[b + 1]? = some bBorn)
     (hframesC : frames[c + 1]? = some cBorn)
     (hoddC : cE.depth % 2 ≠ 0) :
     ∃ (posB posC : Nat × Nat),
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).order.zipIdx.find?
         (fun v => v.1 == b) = some posB ∧
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).order.zipIdx.find?
         (fun v => v.1 == c) = some posC ∧
       bBorn.t0 = bBorn.t1 ∧
       bBorn.count = ((children ns bE.node).length : Int) ∧
       cBorn.t0 = bBorn.t0 ∧
       cBorn.t1 = Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).length * (posC.2 + 1 : Nat))
         ((effectivePlacedInput ns (measuredSideLength p ribs)
           (generatedRib ns (cause, k))).entries.length + 1 : Nat) ∧
       (∃ drawn : Int,
         cBorn.x0 = bBorn.x0 + Int.fdiv ((bBorn.x1 - bBorn.x0) *
           (bBorn.count - drawn)) (bBorn.count + 1) ∧
         drawn + 1 ≤ bBorn.count ∧
         (bBorn.count + 1) * (run p (effectivePlacedInput ns
           (measuredSideLength p ribs)
           (generatedRib ns (cause, k))).heights + 3) ≤
           bBorn.x0 - bBorn.x1) ∧
       cBorn.x1 - cBorn.x0 = -run p (cBorn.t1 - bBorn.t0) ∧
       bBorn.t1 + (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights ≤ cBorn.t1 ∧
       bBorn.t1 = Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).length * (posB.2 + 1 : Nat))
         ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) ∧
       cBorn.t1 = Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).length * (posC.2 + 1 : Nat))
         ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) := by
   have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
   let r := effectivePlacedInput ns (measuredSideLength p ribs)
     (generatedRib ns (cause, k))
   let E := (generatedRib ns (cause, k)).entries
   have hErLen : r.entries.length = E.length := rfl
   obtain ⟨doneB, restB, hpreB, _⟩ := List.eq_append_cons_of_mem hmemB
   obtain ⟨posB, parB, bornB, hfindB, hparB, hbornB, heqB⟩ :=
     hrecords doneB bE b restB hpreB
   have hbornBeq : bornB = bBorn := Option.some.inj (hbornB.symm.trans hframesB)
   have hdepb : cE.depth = bE.depth + 1 :=
     generated_parent_child_depth ns cause k hlink _hcause bE cE b c
       hmemB hmemC hpar
   have hbeven : bE.depth % 2 = 0 := by
     have hm := Nat.mod_lt bE.depth (by decide : 0 < 2)
     have hm2 := Nat.mod_lt cE.depth (by decide : 0 < 2)
     omega
   have hBt0r : bBorn.t0 = Int.fdiv (r.length * (posB.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     rw [← hbornBeq, heqB]
     exact (depthBone_even_endpoints p _ bE.depth _ _ _ hbeven).1
   have hBt1r : bBorn.t1 = Int.fdiv (r.length * (posB.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     rw [← hbornBeq, heqB]
     exact (depthBone_even_endpoints p _ bE.depth _ _ _ hbeven).2.1
   have hBpt : bBorn.t0 = bBorn.t1 := hBt0r.trans hBt1r.symm
   have hBcount : bBorn.count = ((children ns bE.node).length : Int) := by
     rw [← hbornBeq, heqB]
     unfold depthBone
     split <;> rfl
   obtain ⟨doneC, restC, hpreC, _⟩ := List.eq_append_cons_of_mem hmemC
   obtain ⟨posC, parC, bornC, hfindC, hparC, hbornC, heqC⟩ :=
     hrecords doneC cE c restC hpreC
   have hbornCeq : bornC = cBorn := Option.some.inj (hbornC.symm.trans hframesC)
   have hownC : (cE.parent + 1).toNat = b + 1 := by rw [hpar]; omega
   rw [hownC] at hparC
   have hparCeq : parC = bBorn := Option.some.inj (hparC.symm.trans hframesB)
   have hCt0 : cBorn.t0 = bBorn.t0 := by
     rw [← hbornCeq, heqC, hparCeq]
     exact (depthBone_odd_endpoints p _ cE.depth _ _ _ hoddC).1
   have hCt1r : cBorn.t1 = Int.fdiv (r.length * (posC.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     rw [← hbornCeq, heqC]
     exact (depthBone_odd_endpoints p _ cE.depth _ _ _ hoddC).2.1
   have hCx1 : cBorn.x1 = cBorn.x0 - run p (cBorn.t1 - bBorn.t0) := by
     rw [hCt1r, ← hbornCeq, heqC, hparCeq]
     exact (depthBone_odd_endpoints p _ cE.depth _ _ _ hoddC).2.2.2
   have hCfall : cBorn.x1 - cBorn.x0 = -run p (cBorn.t1 - bBorn.t0) := by omega
   have hdrawn : processedOddDraws doneC (cE.parent + 1).toNat + 1 ≤
       bBorn.count := by
     have hpreC2 : (generatedRib ns (cause, k)).entries.zipIdx =
         (doneC ++ [(cE, c)]) ++ restC :=
       hpreC.trans (List.append_assoc doneC [(cE, c)] restC).symm
     have hnat := dfg_drawn_le ns cause k hlink _hcause (doneC ++ [(cE, c)])
       restC hpreC2 (cE.parent + 1).toNat bE.node
       (Or.inr ⟨bE, b, hmemB, hownC, rfl⟩)
     have hstep : processedOddDraws doneC ((cE.parent + 1).toNat) + 1 =
         processedOddDraws (doneC ++ [(cE, c)]) ((cE.parent + 1).toNat) := by
       rw [processedOddDraws_append_one]
       simp [hoddC]
     rw [hstep, hBcount]
     exact hnat
   have hCx0 : cBorn.x0 = bBorn.x0 + Int.fdiv ((bBorn.x1 - bBorn.x0) *
       (bBorn.count - processedOddDraws doneC (cE.parent + 1).toNat))
       (bBorn.count + 1) := by
     rw [← hbornCeq, heqC, hparCeq]
     exact (depthBone_odd_endpoints p _ cE.depth _ _ _ hoddC).2.2.1
   have hres := dfg_native_reservation p
       {parB with drawn := processedOddDraws doneB (bE.parent + 1).toNat}
       bE.depth (Int.fdiv (r.length * (posB.2 + 1 : Nat))
         (r.entries.length + 1 : Nat)) (children ns bE.node).length
       (run p r.heights + 3) hbeven
   rw [← heqB, hbornBeq] at hres
   have hordBC := generated_parent_child_order ns cause k bE cE b c
     hmemB hmemC hpar posB posC hfindB hfindC
   have hposBC : posB.2 < posC.2 := hordBC.1 hbeven
   have hslotGapBCr : Int.fdiv (r.length * (posB.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) + r.heights ≤
       Int.fdiv (r.length * (posC.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     have hlenD : 0 < ((r.entries.length + 1 : Nat) : Int) := by omega
     have hlt : (posB.2 + 1 : Nat) + 1 ≤ (posC.2 + 1 : Nat) := by omega
     exact ordinal_slots_gap r.length ((r.entries.length + 1 : Nat) : Int)
       r.heights ((posB.2 + 1 : Nat) : Int) ((posC.2 + 1 : Nat) : Int)
       hlenD hHnn hbl (by omega)
   have hslotGapBC : bBorn.t1 + r.heights ≤ cBorn.t1 := by
     rw [hBt1r, hCt1r]
     exact hslotGapBCr
   have hslotB_E : bBorn.t1 = Int.fdiv (r.length * (posB.2 + 1 : Nat))
       ((((E.length + 1 : Nat)) : Int)) := by
     rw [hBt1r, hErLen]
   have hCt1_E : cBorn.t1 = Int.fdiv (r.length * (posC.2 + 1 : Nat))
       ((((E.length + 1 : Nat)) : Int)) := by
     rw [hCt1r, hErLen]
   exact ⟨posB, posC, hfindB, hfindC, hBpt, hBcount, hCt0, hCt1r,
     ⟨processedOddDraws doneC (cE.parent + 1).toNat, hCx0, hdrawn, hres.2⟩,
     hCfall, hslotGapBC, hslotB_E, hCt1_E⟩

 /-- One-birth transport for an even child: time containment via order and
 slot gaps; the start interpolates exactly on the parent odd line, the end
 runs horizontally left. -/
 private theorem dfg_step_even (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
     (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
     (hcause : cause ∈ children ns 0)
     (eI : Entry) (idxI : Nat) (fI : Bone)
     (hmemI : (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hodd : eI.depth % 2 ≠ 0)
     (posI posP : Nat × Nat) (pE : Entry)
     (hfindI : (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).order.zipIdx.find?
       (fun v => v.1 == idxI) = some posI)
     (hfindP : (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).order.zipIdx.find?
       (fun v => v.1 == (eI.parent).toNat) = some posP)
     (hpmemP : (pE, (eI.parent).toNat) ∈
       (generatedRib ns (cause, k)).entries.zipIdx)
     (hpeven : pE.depth % 2 = 0)
     (hfIt0slot : fI.t0 = Int.fdiv ((effectivePlacedInput ns
       (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posP.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int))
     (hfIt1slot : fI.t1 = Int.fdiv ((effectivePlacedInput ns
       (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posI.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int))
     (hHnn : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights)
     (hbl : ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) *
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights ≤
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).length)
     (hcos : 0 ≤ p.cos) (hsin1 : 1 ≤ p.sin)
     (frames : List Bone)
     (hlen : frames.length =
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).entries.length + 1)
     (hrecords : ∀ (done : List (Entry × Nat)) (e : Entry) (idx : Nat)
       (rest : List (Entry × Nat)),
       (generatedRib ns (cause, k)).entries.zipIdx = done ++ (e, idx) :: rest →
       ∃ (pos : Nat × Nat) (parent born : Bone),
         (effectivePlacedInput ns (measuredSideLength p ribs)
           (generatedRib ns (cause, k))).order.zipIdx.find?
           (fun v => v.1 == idx) = some pos ∧
         frames[(e.parent + 1).toNat]? = some parent ∧
         frames[idx + 1]? = some born ∧
         born = depthBone p
           { parent with drawn := processedOddDraws done (e.parent + 1).toNat }
           e.depth (Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
             (generatedRib ns (cause, k))).length * (pos.2 + 1 : Nat))
             ((effectivePlacedInput ns (measuredSideLength p ribs)
               (generatedRib ns (cause, k))).entries.length + 1 : Nat))
           (children ns e.node).length (run p (effectivePlacedInput ns
             (measuredSideLength p ribs)
             (generatedRib ns (cause, k))).heights + 3))
     (a b : Nat) (aE bE : Entry) (aBorn bBorn : Bone)
     (hmemA : (aE, a) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hmemB : (bE, b) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hpar : bE.parent = (a : Int))
     (hdomA : dfgOddBound fI aBorn)
     (hframesA : frames[a + 1]? = some aBorn)
     (hframesB : frames[b + 1]? = some bBorn)
     (hbeven : bE.depth % 2 = 0)
     (hchainB : IndexedAncestor (generatedRib ns (cause, k)).entries idxI b) :
     dfgEvenBound fI bBorn := by
   have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
   let r := effectivePlacedInput ns (measuredSideLength p ribs)
     (generatedRib ns (cause, k))
   let E := (generatedRib ns (cause, k)).entries
   have hErLen : r.entries.length = E.length := rfl
   obtain ⟨doneB, restB, hpreB, _⟩ := List.eq_append_cons_of_mem hmemB
   obtain ⟨posB, parB, bornB, hfindB, hparB, hbornB, heqB⟩ :=
     hrecords doneB bE b restB hpreB
   have hbornBeq : bornB = bBorn := Option.some.inj (hbornB.symm.trans hframesB)
   have hownB : (bE.parent + 1).toNat = a + 1 := by rw [hpar]; omega
   rw [hownB] at hparB
   have hparBeq : parB = aBorn := Option.some.inj (hparB.symm.trans hframesA)
   have hdepb : bE.depth = aE.depth + 1 :=
     generated_parent_child_depth ns cause k hlink hcause aE bE a b
       hmemA hmemB hpar
   have haodd1 : aE.depth % 2 = 1 := by
     have hm := Nat.mod_lt aE.depth (by decide : 0 < 2)
     have hm2 := Nat.mod_lt bE.depth (by decide : 0 < 2)
     omega
   have haoddNe : aE.depth % 2 ≠ 0 := by omega
   obtain ⟨doneA, restA, hpreA, _⟩ := List.eq_append_cons_of_mem hmemA
   obtain ⟨posA, parA, bornA, hfindA, hparA, hbornA, heqA⟩ :=
     hrecords doneA aE a restA hpreA
   have hbornAeq : bornA = aBorn := Option.some.inj (hbornA.symm.trans hframesA)
   have haRootFalse : aE.parent ≠ -1 := by
     intro heq
     have hd := generated_root_depth ns cause k hlink hcause aE a hmemA heq
     omega
   have haLb : -1 ≤ aE.parent :=
     generated_entry_parent_lower_bound ns cause k aE a hmemA
   have haParEq : aE.parent = (((aE.parent).toNat : Nat) : Int) := by omega
   have haown : (aE.parent + 1).toNat = (aE.parent).toNat + 1 := by omega
   rw [haown] at hparA
   have hgbound : (aE.parent).toNat < E.length := by
     have h1 := (List.getElem?_eq_some_iff.mp hparA).1
     have h1r : (aE.parent).toNat + 1 < r.entries.length + 1 := by
       rw [hlen] at h1
       exact h1
     rw [hErLen] at h1r
     omega
   obtain ⟨gE, hgEGet⟩ : ∃ gE, E[(aE.parent).toNat]? = some gE :=
     ⟨_, List.getElem?_eq_getElem hgbound⟩
   have hmemG : (gE, (aE.parent).toNat) ∈ E.zipIdx :=
     List.mem_zipIdx_iff_getElem?.mpr hgEGet
   obtain ⟨doneG, restG, hpreG, _⟩ := List.eq_append_cons_of_mem hmemG
   obtain ⟨posG, parG, bornG, hfindG, hparG, hbornG, heqG⟩ :=
     hrecords doneG gE (aE.parent).toNat restG hpreG
   have hparAeq : parA = bornG := Option.some.inj (hparA.symm.trans hbornG)
   have hdepga : aE.depth = gE.depth + 1 :=
     generated_parent_child_depth ns cause k hlink hcause gE aE _ a
       hmemG hmemA haParEq
   have hgeven : gE.depth % 2 = 0 := dfg_parent_depth_even _ _ hdepga haoddNe
   have hBt1r : bBorn.t1 = Int.fdiv (r.length * (posB.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     rw [← hbornBeq, heqB, hparBeq]
     exact (depthBone_even_endpoints p _ bE.depth _ _ _ hbeven).2.1
   have haT1r : aBorn.t1 = Int.fdiv (r.length * (posA.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     rw [← hbornAeq, heqA]
     exact (depthBone_odd_endpoints p _ aE.depth _ _ _ haoddNe).2.1
   have haT0 : aBorn.t0 = bornG.t0 := by
     rw [← hbornAeq, heqA, hparAeq]
     exact (depthBone_odd_endpoints p _ aE.depth _ _ _ haoddNe).1
   have hgT0r : bornG.t0 = Int.fdiv (r.length * (posG.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     rw [heqG]
     exact (depthBone_even_endpoints p _ gE.depth _ _ _ hgeven).1
   have hbX0 : bBorn.x0 = aBorn.x0 + Int.fdiv ((aBorn.x1 - aBorn.x0) *
       (Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat) -
         aBorn.t0)) (aBorn.t1 - aBorn.t0) := by
     have hsl : r.length = (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).length := rfl
     have hse : r.entries.length = (effectivePlacedInput ns
         (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).entries.length := rfl
     rw [← hbornBeq, heqB, hparBeq, hsl, hse]
     simp [depthBone, hbeven]
   have hbX1 : bBorn.x1 = bBorn.x0 - boneLength p (children ns bE.node).length
       (run p r.heights + 3) := by
     rw [← hbornBeq, heqB, hparBeq]
     exact (depthBone_even_endpoints p _ bE.depth _ _ _ hbeven).2.2
   have hordAB := generated_parent_child_order ns cause k aE bE a b
     hmemA hmemB hpar posA posB hfindA hfindB
   have hposAB : posB.2 < posA.2 := hordAB.2 haoddNe
   have hchainGB : IndexedAncestor E (aE.parent).toNat b :=
     dfg_trans (IndexedAncestor.edge _ _ aE
       (List.mem_zipIdx_iff_getElem?.mp hmemA) haParEq)
       (IndexedAncestor.edge _ _ bE
         (List.mem_zipIdx_iff_getElem?.mp hmemB) hpar)
   have hordGB := generated_ancestor_order ns cause k gE bE (aE.parent).toNat b
     hmemG hmemB hchainGB posG posB hfindG hfindB
   have hposGB : posG.2 < posB.2 := hordGB.1 hgeven
   have hgapGB : Int.fdiv (r.length * (posG.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) + r.heights ≤
       Int.fdiv (r.length * (posB.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     have hlenD : 0 < ((r.entries.length + 1 : Nat) : Int) := by omega
     have hlt : (posG.2 + 1 : Nat) + 1 ≤ (posB.2 + 1 : Nat) := by omega
     exact ordinal_slots_gap r.length ((r.entries.length + 1 : Nat) : Int)
       r.heights ((posG.2 + 1 : Nat) : Int) ((posB.2 + 1 : Nat) : Int)
       hlenD hHnn hbl (by omega)
   have hgapBA : Int.fdiv (r.length * (posB.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) + r.heights ≤
       Int.fdiv (r.length * (posA.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     have hlenD : 0 < ((r.entries.length + 1 : Nat) : Int) := by omega
     have hlt : (posB.2 + 1 : Nat) + 1 ≤ (posA.2 + 1 : Nat) := by omega
     exact ordinal_slots_gap r.length ((r.entries.length + 1 : Nat) : Int)
       r.heights ((posB.2 + 1 : Nat) : Int) ((posA.2 + 1 : Nat) : Int)
       hlenD hHnn hbl (by omega)
   have hslotB_E : bBorn.t1 = Int.fdiv (r.length * (posB.2 + 1 : Nat))
       ((((E.length + 1 : Nat)) : Int)) := by
     rw [hBt1r, hErLen]
   have hcont := dfg_contain ns p raw hrun ribs hg cause k hsource hcause
     eI idxI fI hmemI hodd posI posP pE hfindI hfindP hpmemP hpeven
     hfIt0slot hfIt1slot hHnn hbl b bE bBorn posB hmemB hfindB hchainB hslotB_E
   have hslotInLo : aBorn.t0 ≤ Int.fdiv (r.length * (posB.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) := by
     have h1 : aBorn.t0 = (r.length * ↑(posG.snd + 1)).fdiv ↑(r.entries.length + 1) := by
       rw [haT0, hgT0r]
     have hnn : 0 ≤ r.heights := hHnn
     have hle : (r.length * ↑(posG.snd + 1)).fdiv ↑(r.entries.length + 1) ≤
         (r.length * ↑(posG.snd + 1)).fdiv ↑(r.entries.length + 1) + r.heights := by
       omega
     rw [h1]
     exact Int.le_trans hle hgapGB
   have hslotInHi : Int.fdiv (r.length * (posB.2 + 1 : Nat))
       (r.entries.length + 1 : Nat) ≤ aBorn.t1 := by
     have hnn : 0 ≤ r.heights := hHnn
     have hle : Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat) ≤
         Int.fdiv (r.length * (posB.2 + 1 : Nat)) (r.entries.length + 1 : Nat) + r.heights := by
       omega
     rw [haT1r]
     exact Int.le_trans hle hgapBA
   have hline := hdomA.2.2.2 _ hslotInLo hslotInHi
   have hx0line : bBorn.x0 = dfgLineOf aBorn
       (Int.fdiv (r.length * (posB.2 + 1 : Nat))
         (r.entries.length + 1 : Nat)) := by
     rw [hbX0]
     simp only [dfgLineOf]
   have hBLnn : 0 ≤ boneLength p (children ns bE.node).length
       (run p r.heights + 3) := by
     have hsin0 : 0 < p.sin := by have h1 := hsin1; omega
     have hrunNN : 0 ≤ run p r.heights :=
       Int.fdiv_nonneg (Int.mul_nonneg hHnn hcos) (Int.le_of_lt hsin0)
     have h3 : 0 ≤ (((children ns bE.node).length : Int) + 1) *
         (run p r.heights + 3) :=
       Int.mul_nonneg (by omega) (by omega)
     have h4 : (((children ns bE.node).length : Int) + 1) *
         (run p r.heights + 3) ≤
         boneLength p ((children ns bE.node).length) (run p r.heights + 3) :=
       Int.le_max_right _ _
     omega
   refine ⟨?_, ?_, ?_, ?_⟩
   · omega
   · omega
   · rw [hBt1r, hx0line]
     exact hline
   · rw [hBt1r, hbX1, hx0line]
     omega

 /-- Transported gap for an odd child: the attachment margin minus the two
 floor roundings (one downward line drop, one upward fall bound). -/
 private theorem dfg_odd_line_gap (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout) (_hrun : layout ns p = .ok raw)
     (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
     (_hcause : cause ∈ children ns 0)
     (hcos : 0 ≤ p.cos) (hsin1 : 1 ≤ p.sin)
     (hHnn : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights)
     (hH1 : 1 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights)
     (fI : Bone)
     (hfIfall : fI.x1 - fI.x0 = -run p (fI.t1 - fI.t0))
     (hspanI : 0 < fI.t1 - fI.t0)
     (bBorn cBorn : Bone)
     (hBpt : bBorn.t0 = bBorn.t1)
     (hBx0le : bBorn.x0 ≤ dfgLineOf fI bBorn.t1)
     (hCt0 : cBorn.t0 = bBorn.t0)
     (drawn : Int)
     (hCx0 : cBorn.x0 = bBorn.x0 + Int.fdiv ((bBorn.x1 - bBorn.x0) *
       (bBorn.count - drawn)) (bBorn.count + 1))
     (hdrawn : drawn + 1 ≤ bBorn.count)
    (hres : (bBorn.count + 1) * (run p (effectivePlacedInput ns
      (measuredSideLength p ribs)
      (generatedRib ns (cause, k))).heights + 3) ≤ bBorn.x0 - bBorn.x1)
    (hcount : 0 < bBorn.count + 1)
     (hCfall : cBorn.x1 - cBorn.x0 = -run p (cBorn.t1 - bBorn.t0))
     (hgapBC : bBorn.t1 + (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights ≤ cBorn.t1)
     (hslotBge : fI.t0 ≤ bBorn.t1)
     (_hslotCle : cBorn.t1 ≤ fI.t1) :
     ∀ t, cBorn.t0 ≤ t → t ≤ cBorn.t1 →
       (run p (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights + 3) - 2 ≤
         dfgLineOf fI t - dfgLineOf cBorn t := by
   intro t ht0 ht1
   have hsin0 : 0 < p.sin := by have h1 := hsin1; omega
   have hseg_nn : 0 ≤ t - bBorn.t1 := by omega
   have hseg_le : t - bBorn.t1 ≤ cBorn.t1 - bBorn.t1 := by omega
   have hSd_pos : 0 < cBorn.t1 - bBorn.t1 := by omega
   have hmarginNN : 0 ≤ run p (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights + 3 := by
     have hrunNN : 0 ≤ run p (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights :=
       Int.fdiv_nonneg (Int.mul_nonneg hHnn hcos) (Int.le_of_lt hsin0)
     omega
   have hden : 0 < bBorn.count + 1 := hcount
   have hattach := dfg_attach_start_margin bBorn.x0 bBorn.x1 bBorn.count drawn
     (run p (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights + 3) hden hmarginNN hres hdrawn
   have hmargin : cBorn.x0 + (run p (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights + 3) ≤ bBorn.x0 := by omega
   have hdrop := dfg_line_drop p hcos hsin1 fI.x0 fI.t0 (fI.t1 - fI.t0)
     bBorn.t1 t (by omega) hslotBge (by omega)
   have eI1 : dfgLineOf fI bBorn.t1 = fI.x0 +
       Int.fdiv (-(run p (fI.t1 - fI.t0) * (bBorn.t1 - fI.t0)))
         (fI.t1 - fI.t0) := by
     unfold dfgLineOf
     rw [hfIfall, Int.neg_mul]
   have eI2 : dfgLineOf fI t = fI.x0 +
       Int.fdiv (-(run p (fI.t1 - fI.t0) * (t - fI.t0))) (fI.t1 - fI.t0) := by
     unfold dfgLineOf
     rw [hfIfall, Int.neg_mul]
   have hdropL : dfgLineOf fI bBorn.t1 - dfgLineOf fI t ≤
       run p (t - bBorn.t1) + 1 := by omega
   have hfall := dfg_fall_lb p hcos hsin1 (cBorn.t1 - bBorn.t1) (t - bBorn.t1)
     hSd_pos hseg_nn hseg_le
   have eC : dfgLineOf cBorn t = cBorn.x0 +
       Int.fdiv (-(run p (cBorn.t1 - bBorn.t1) * (t - bBorn.t1)))
         (cBorn.t1 - bBorn.t1) := by
     unfold dfgLineOf
     rw [hCfall, hCt0, hBpt, Int.neg_mul]
   omega

 /-- One-birth transport for an odd child: span, containment, and pointwise
 domination from the even parent's endpoints plus the transported gap. -/
 private theorem dfg_step_odd (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
     (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
     (hcause : cause ∈ children ns 0)
     (eI : Entry) (idxI : Nat) (fI : Bone)
     (hmemI : (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hodd : eI.depth % 2 ≠ 0)
     (posI posP : Nat × Nat) (pE : Entry)
     (hfindI : (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).order.zipIdx.find?
       (fun v => v.1 == idxI) = some posI)
     (hfindP : (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).order.zipIdx.find?
       (fun v => v.1 == (eI.parent).toNat) = some posP)
     (hpmemP : (pE, (eI.parent).toNat) ∈
       (generatedRib ns (cause, k)).entries.zipIdx)
     (hpeven : pE.depth % 2 = 0)
     (hfIt0slot : fI.t0 = Int.fdiv ((effectivePlacedInput ns
       (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posP.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int))
     (hfIt1slot : fI.t1 = Int.fdiv ((effectivePlacedInput ns
       (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posI.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int))
     (hfIfall : fI.x1 - fI.x0 = -run p (fI.t1 - fI.t0))
     (hspanI : 0 < fI.t1 - fI.t0)
     (hHnn : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights)
     (hH1 : 1 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights)
     (hbl : ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) *
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights ≤
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).length)
     (hcos : 0 ≤ p.cos) (hsin1 : 1 ≤ p.sin)
     (frames : List Bone)
     (hlen : frames.length =
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).entries.length + 1)
     (hrecords : ∀ (done : List (Entry × Nat)) (e : Entry) (idx : Nat)
       (rest : List (Entry × Nat)),
       (generatedRib ns (cause, k)).entries.zipIdx = done ++ (e, idx) :: rest →
       ∃ (pos : Nat × Nat) (parent born : Bone),
         (effectivePlacedInput ns (measuredSideLength p ribs)
           (generatedRib ns (cause, k))).order.zipIdx.find?
           (fun v => v.1 == idx) = some pos ∧
         frames[(e.parent + 1).toNat]? = some parent ∧
         frames[idx + 1]? = some born ∧
         born = depthBone p
           { parent with drawn := processedOddDraws done (e.parent + 1).toNat }
           e.depth (Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
             (generatedRib ns (cause, k))).length * (pos.2 + 1 : Nat))
             ((effectivePlacedInput ns (measuredSideLength p ribs)
               (generatedRib ns (cause, k))).entries.length + 1 : Nat))
           (children ns e.node).length (run p (effectivePlacedInput ns
             (measuredSideLength p ribs)
             (generatedRib ns (cause, k))).heights + 3))
     (b c : Nat) (bE cE : Entry) (bBorn cBorn : Bone)
     (hmemB : (bE, b) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hmemC : (cE, c) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hpar : cE.parent = (b : Int))
     (hdomB : dfgEvenBound fI bBorn)
     (hframesB : frames[b + 1]? = some bBorn)
     (hframesC : frames[c + 1]? = some cBorn)
     (hoddC : cE.depth % 2 ≠ 0)
     (hchainC : IndexedAncestor (generatedRib ns (cause, k)).entries idxI c) :
     dfgOddBound fI cBorn := by
   obtain ⟨posB, posC, hfindB, hfindC, hBpt, hBcount, hCt0, hCt1r, hex,
       hCfall, hslotGapBC, hslotB_E, hCt1_E⟩ :=
     dfg_odd_child_facts ns p raw hrun ribs hg cause k hsource hcause hHnn
       hbl frames hlen hrecords b c bE cE bBorn cBorn hmemB hmemC hpar
       hframesB hframesC hoddC
   obtain ⟨drawn, hCx0, hdrawn, hres⟩ := hex
   have hcont := dfg_contain ns p raw hrun ribs hg cause k hsource hcause
     eI idxI fI hmemI hodd posI posP pE hfindI hfindP hpmemP hpeven
     hfIt0slot hfIt1slot hHnn hbl c cE cBorn posC hmemC hfindC hchainC hCt1_E
   have hspanC : 0 < cBorn.t1 - cBorn.t0 := by omega
   have hgap := dfg_odd_line_gap ns p raw hrun ribs hg cause k hsource hcause
     hcos hsin1 hHnn hH1 fI hfIfall hspanI bBorn cBorn hBpt hdomB.2.2.1 hCt0
     drawn hCx0 hdrawn hres (by omega) hCfall hslotGapBC hdomB.1 hcont.2
   have hmarginNN : 0 ≤ run p (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights + 3 := by
     have hsin0 : 0 < p.sin := by have h1 := hsin1; omega
     have hrunNN : 0 ≤ run p (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights :=
       Int.fdiv_nonneg (Int.mul_nonneg hHnn hcos) (Int.le_of_lt hsin0)
     omega
   have hdomB1 : fI.t0 ≤ bBorn.t1 := hdomB.1
   have hRnn : 0 ≤ run p (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights := by
     have hsin0 : 0 < p.sin := by have h1 := hsin1; omega
     exact Int.fdiv_nonneg (Int.mul_nonneg hHnn hcos) (Int.le_of_lt hsin0)
   refine ⟨?_, ?_, ?_, ?_⟩
   · exact hspanC
   · omega
   · exact hcont.2
   · intro t ht0 ht1
     have h := hgap t ht0 ht1
     omega

 /-- Domination for every descendant bone by induction on entry depth
 (not on the chain): the peel helper keeps every index explicit. -/
 private theorem dfg_bound_of_chain (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
     (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
     (hcause : cause ∈ children ns 0)
     (eI : Entry) (idxI : Nat) (fI : Bone)
     (hmemI : (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
     (hodd : eI.depth % 2 ≠ 0)
     (posI posP : Nat × Nat) (pE : Entry)
     (hfindI : (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).order.zipIdx.find?
       (fun v => v.1 == idxI) = some posI)
     (hfindP : (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).order.zipIdx.find?
       (fun v => v.1 == (eI.parent).toNat) = some posP)
     (hpmemP : (pE, (eI.parent).toNat) ∈
       (generatedRib ns (cause, k)).entries.zipIdx)
     (hpeven : pE.depth % 2 = 0)
     (hfIt0slot : fI.t0 = Int.fdiv ((effectivePlacedInput ns
       (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posP.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int))
     (hfIt1slot : fI.t1 = Int.fdiv ((effectivePlacedInput ns
       (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).length * (posI.2 + 1 : Nat))
       ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int))
     (hfIfall : fI.x1 - fI.x0 = -run p (fI.t1 - fI.t0))
     (hspan : fI.t0 < fI.t1)
     (hHnn : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights)
     (hH1 : 1 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
       (generatedRib ns (cause, k))).heights)
     (hbl : ((((generatedRib ns (cause, k)).entries.length + 1 : Nat)) : Int) *
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).heights ≤
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).length)
     (hcos : 0 ≤ p.cos) (hsin1 : 1 ≤ p.sin)
     (frames : List Bone)
     (hlen : frames.length =
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))).entries.length + 1)
     (hrecords : ∀ (done : List (Entry × Nat)) (e : Entry) (idx : Nat)
       (rest : List (Entry × Nat)),
       (generatedRib ns (cause, k)).entries.zipIdx = done ++ (e, idx) :: rest →
       ∃ (pos : Nat × Nat) (parent born : Bone),
         (effectivePlacedInput ns (measuredSideLength p ribs)
           (generatedRib ns (cause, k))).order.zipIdx.find?
           (fun v => v.1 == idx) = some pos ∧
         frames[(e.parent + 1).toNat]? = some parent ∧
         frames[idx + 1]? = some born ∧
         born = depthBone p
           { parent with drawn := processedOddDraws done (e.parent + 1).toNat }
           e.depth (Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
             (generatedRib ns (cause, k))).length * (pos.2 + 1 : Nat))
             ((effectivePlacedInput ns (measuredSideLength p ribs)
               (generatedRib ns (cause, k))).entries.length + 1 : Nat))
           (children ns e.node).length (run p (effectivePlacedInput ns
             (measuredSideLength p ribs)
             (generatedRib ns (cause, k))).heights + 3))
     (hlookI : frames[idxI + 1]? = some fI) :
     ∀ (d b : Nat) (bE : Entry) (bBorn : Bone),
       bE.depth = d → (bE, b) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
       IndexedAncestor (generatedRib ns (cause, k)).entries idxI b →
       frames[b + 1]? = some bBorn → dfgBound fI bE bBorn := by
   have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
   have hspanI : 0 < fI.t1 - fI.t0 := by omega
   intro d
   induction d with
   | zero =>
       intro b bE bBorn hd hmem hchainB hlook
       obtain ⟨pmid, hparBmid, hor⟩ := dfg_parent_chain hchainB bE
         (List.mem_zipIdx_iff_getElem?.mp hmem)
       have hlbP : -1 ≤ bE.parent :=
         generated_entry_parent_lower_bound ns cause k bE b hmem
       have hownP : (bE.parent + 1).toNat = pmid + 1 := by rw [hparBmid]; omega
       obtain ⟨doneB, restB, hpreB, _⟩ := List.eq_append_cons_of_mem hmem
       obtain ⟨posB, parB, bornB, hfindB, hparB, hbornB, heqB⟩ :=
         hrecords doneB bE b restB hpreB
       rw [hownP] at hparB
       have hpltB : pmid <
           (generatedRib ns (cause, k)).entries.length := by
         have h1 := (List.getElem?_eq_some_iff.mp hparB).1
         rw [hlen] at h1
         have hErLen : (effectivePlacedInput ns (measuredSideLength p ribs)
           (generatedRib ns (cause, k))).entries.length =
           (generatedRib ns (cause, k)).entries.length := rfl
         omega
       obtain ⟨pE', hpE'⟩ : ∃ pE',
           (generatedRib ns (cause, k)).entries[pmid]? = some pE' :=
         ⟨_, List.getElem?_eq_getElem hpltB⟩
       have hmemP : (pE', pmid) ∈
           (generatedRib ns (cause, k)).entries.zipIdx :=
         List.mem_zipIdx_iff_getElem?.mpr hpE'
       have hparP : bE.parent = ((pmid : Nat) : Int) := hparBmid
       have hdepb : bE.depth = pE'.depth + 1 :=
         generated_parent_child_depth ns cause k hlink hcause pE' bE pmid b
           hmemP hmem hparP
       omega
   | succ d ih =>
       intro b bE bBorn hd hmem hchainB hlook
       obtain ⟨doneB, restB, hpreB, _⟩ := List.eq_append_cons_of_mem hmem
       obtain ⟨posB, parB, bornB, hfindB, hparB, hbornB, heqB⟩ :=
         hrecords doneB bE b restB hpreB
       have hbornBeq : bornB = bBorn := Option.some.inj (hbornB.symm.trans hlook)
       obtain ⟨pmid, hparBmid, hor⟩ := dfg_parent_chain hchainB bE
         (List.mem_zipIdx_iff_getElem?.mp hmem)
       have hownP : (bE.parent + 1).toNat = pmid + 1 := by rw [hparBmid]; omega
       rw [hownP] at hparB
       have hpltB : pmid <
           (generatedRib ns (cause, k)).entries.length := by
         have h1 := (List.getElem?_eq_some_iff.mp hparB).1
         rw [hlen] at h1
         have hErLen : (effectivePlacedInput ns (measuredSideLength p ribs)
           (generatedRib ns (cause, k))).entries.length =
           (generatedRib ns (cause, k)).entries.length := rfl
         omega
       obtain ⟨pE', hpE'⟩ : ∃ pE',
           (generatedRib ns (cause, k)).entries[pmid]? = some pE' :=
         ⟨_, List.getElem?_eq_getElem hpltB⟩
       have hmemP : (pE', pmid) ∈
           (generatedRib ns (cause, k)).entries.zipIdx :=
         List.mem_zipIdx_iff_getElem?.mpr hpE'
       have hlookPbound : pmid + 1 < frames.length := by
         have h1 := (List.getElem?_eq_some_iff.mp hparB).1
         omega
       obtain ⟨pBorn, hlookP⟩ : ∃ pBorn, frames[pmid + 1]? = some pBorn :=
         ⟨_, List.getElem?_eq_getElem hlookPbound⟩
       have hparBeq : parB = pBorn := Option.some.inj (hparB.symm.trans hlookP)
       have hparP : bE.parent = ((pmid : Nat) : Int) := hparBmid
       have hdepb : bE.depth = pE'.depth + 1 :=
         generated_parent_child_depth ns cause k hlink hcause pE' bE pmid b
           hmemP hmem hparP
       have hdomP : dfgBound fI pE' pBorn := by
         rcases hor with rfl | hchainP
         · have hmemIget : (generatedRib ns (cause, k)).entries[pmid]? =
               some eI := List.mem_zipIdx_iff_getElem?.mp hmemI
           have hpeEq : pE' = eI :=
             Option.some.inj (hpE'.symm.trans hmemIget)
           have hpbEq : pBorn = fI := Option.some.inj (hlookP.symm.trans hlookI)
           have hodd1 : eI.depth % 2 = 1 := by
             have hm := Nat.mod_lt eI.depth (by decide : 0 < 2)
             omega
           rw [hpeEq, hpbEq]
           constructor
           · intro _
             exact ⟨hspanI, Int.le_refl _, Int.le_refl _,
               fun t _ _ => Int.le_refl _⟩
           · intro heven
             omega
         · have hpd : pE'.depth = d := by omega
           exact ih pmid pE' pBorn hpd hmemP hchainP hlookP
       by_cases hevenB : bE.depth % 2 = 0
       · have hpodd1 : pE'.depth % 2 = 1 := by
           have hm := Nat.mod_lt pE'.depth (by decide : 0 < 2)
           have hm2 := Nat.mod_lt bE.depth (by decide : 0 < 2)
           omega
         exact ⟨fun h => absurd h (by omega), fun _ => dfg_step_even ns p raw hrun ribs hg cause k hsource hcause
           eI idxI fI hmemI hodd posI posP pE hfindI hfindP hpmemP hpeven
           hfIt0slot hfIt1slot hHnn hbl hcos hsin1 frames hlen hrecords
           pmid b pE' bE pBorn bBorn hmemP hmem hparBmid (hdomP.1 hpodd1)
           hlookP hlook hevenB hchainB⟩
       · have hoddB : bE.depth % 2 ≠ 0 := by omega
         have hpeven' : pE'.depth % 2 = 0 :=
           dfg_parent_depth_even _ _ hdepb hoddB
         exact ⟨fun _ => dfg_step_odd ns p raw hrun ribs hg cause k hsource hcause
           eI idxI fI hmemI hodd posI posP pE hfindI hfindP hpmemP hpeven
           hfIt0slot hfIt1slot hfIfall hspanI hHnn hH1 hbl hcos hsin1
           frames hlen hrecords pmid b pE' bE pBorn bBorn hmemP hmem
           hparBmid (hdomP.2 hpeven') hlookP hlook hoddB hchainB, fun h => absurd h hoddB⟩

 /-- The executed descendant frame gap: fall equation plus interpolated
 reservation for strict descendants of an odd entry. -/
 theorem descendantFrameGap (ns : List Tree.Node) (p : Params)
     (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
     (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
     (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
     (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
     (hplace : place ns p spine
       (effectivePlacedInput ns (measuredSideLength p ribs)
         (generatedRib ns (cause, k))) = .ok placed) :
     DescendantFrameGap ns p raw hrun ribs hg cause k hsource hcause
       spine placed hplace := by
   intro eI eJ idxI idxJ frames fI fJ hmemI hmemJ hchain hodd hlen _hroot
     hrecords hlookI hlookJ
   let r := effectivePlacedInput ns (measuredSideLength p ribs)
     (generatedRib ns (cause, k))
   let E := (generatedRib ns (cause, k)).entries
   obtain ⟨posI, posP, pE, parI, hfindI, hfindP, hpmemP, hpeven, _hparI,
       hfIt0slot, hfIt1slot, hfIfall, hspan, hxle, hH1, hbudget⟩ :=
     dfg_slot_setup ns p raw hrun ribs hg cause k hsource hcause eI idxI
       hmemI hodd frames hlen hrecords fI hlookI
   have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
   have hne : ns ≠ [] := by
     intro heq
     simp [heq, children] at hcause
   have hparams := dfg_slope_parameters ns p raw hne hrun
   have hcos : 0 ≤ p.cos := hparams.1
   have hsin1 : 1 ≤ p.sin := hparams.2
   have hHnn : 0 ≤ r.heights := Int.le_trans (by decide : (0 : Int) ≤ 1) hH1
   have hkey := dfg_bound_of_chain ns p raw hrun ribs hg cause k hsource hcause
     eI idxI fI hmemI hodd posI posP pE hfindI hfindP hpmemP hpeven
     hfIt0slot hfIt1slot hfIfall hspan hHnn hH1 hbudget hcos hsin1
     frames hlen hrecords hlookI
   refine ⟨?_, ?_, ?_, ?_⟩
   · exact hspan
   · exact hxle
   · omega
   · by_cases hevenJ : eJ.depth % 2 = 0
     · have hQ := hkey eJ.depth idxJ eJ fJ rfl hmemJ hchain hlookJ
       have hE := hQ.2 hevenJ
       obtain ⟨doneJ, restJ, hpreJ, _⟩ := List.eq_append_cons_of_mem hmemJ
       obtain ⟨posJ, parJ, bornJ, hfindJ, hparJ, hbornJ, heqJ⟩ :=
         hrecords doneJ eJ idxJ restJ hpreJ
       have hbornJeq : bornJ = fJ := Option.some.inj (hbornJ.symm.trans hlookJ)
       have hres := dfg_native_reservation p
         {parJ with drawn := processedOddDraws doneJ (eJ.parent + 1).toNat}
         eJ.depth (Int.fdiv (r.length * (posJ.2 + 1 : Nat))
           (r.entries.length + 1 : Nat)) (children ns eJ.node).length
         (run p r.heights + 3) hevenJ
       rw [← heqJ, hbornJeq] at hres
       have hx0u : fJ.x0 ≤ fI.x0 + Int.fdiv ((fI.x1 - fI.x0) *
           (fJ.t1 - fI.t0)) (fI.t1 - fI.t0) := (hQ.2 hevenJ).2.2.1
       have hresV : 0 < fJ.count + 1 ∧
           (fJ.count + 1) * (run p (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))).heights + 3) ≤
           fJ.x0 - fJ.x1 := hres
       have hRnnV : 0 ≤ run p (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))).heights := by
         have hsin0 : 0 < p.sin := by have h1 := hsin1; omega
         exact Int.fdiv_nonneg (Int.mul_nonneg (Int.le_trans (by decide : (0 : Int) ≤ 1) hH1) hcos) (Int.le_of_lt hsin0)
       have hMnn : 0 ≤ run p (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))).heights + 3 := by
         omega
       have h1c : (1 : Int) ≤ fJ.count + 1 := by omega
       have hMge := Int.mul_le_mul_of_nonneg_right h1c hMnn
       simp only [Int.one_mul] at hMge
       omega
     · have hoddJ : eJ.depth % 2 = 1 := by
         have hm := Nat.mod_lt eJ.depth (by decide : 0 < 2)
         omega
       obtain ⟨b, hparB, hor⟩ := dfg_parent_chain hchain eJ
         (List.mem_zipIdx_iff_getElem?.mp hmemJ)
       have hlbJ : -1 ≤ eJ.parent :=
         generated_entry_parent_lower_bound ns cause k eJ idxJ hmemJ
       have hownJ : (eJ.parent + 1).toNat = b + 1 := by rw [hparB]; omega
       obtain ⟨doneJ, restJ, hpreJ, _⟩ := List.eq_append_cons_of_mem hmemJ
       obtain ⟨posJ, parJ, bornJ, hfindJ, hparJ, hbornJ, heqJ⟩ :=
         hrecords doneJ eJ idxJ restJ hpreJ
       rw [hownJ] at hparJ
       have hbornJeq : bornJ = fJ := Option.some.inj (hbornJ.symm.trans hlookJ)
       have hpltJ : b < E.length := by
         have h1 := (List.getElem?_eq_some_iff.mp hparJ).1
         have h1r : b + 1 < r.entries.length + 1 := by
           rw [hlen] at h1
           exact h1
         have hErLen : r.entries.length = E.length := rfl
         rw [hErLen] at h1r
         omega
       obtain ⟨bE, hbEGet⟩ : ∃ bE, E[b]? = some bE :=
         ⟨_, List.getElem?_eq_getElem hpltJ⟩
       have hmemB : (bE, b) ∈ E.zipIdx :=
         List.mem_zipIdx_iff_getElem?.mpr hbEGet
       have hlookPbound : b + 1 < frames.length := by
         have h1 := (List.getElem?_eq_some_iff.mp hparJ).1
         omega
       obtain ⟨bBorn, hlookB⟩ : ∃ bBorn, frames[b + 1]? = some bBorn :=
         ⟨_, List.getElem?_eq_getElem hlookPbound⟩
       have hparBeq : parJ = bBorn := Option.some.inj (hparJ.symm.trans hlookB)
       have hdepb : eJ.depth = bE.depth + 1 :=
         generated_parent_child_depth ns cause k hlink hcause bE eJ b idxJ
           hmemB hmemJ hparB
       have hbeven : bE.depth % 2 = 0 := dfg_parent_depth_even _ _ hdepb
         (by omega)
       rcases hor with rfl | hchainP
       · have hdepbI : eJ.depth = eI.depth + 1 :=
           generated_parent_child_depth ns cause k hlink hcause eI eJ b
             idxJ hmemI hmemJ hparB
         omega
       · have hQp := hkey bE.depth b bE bBorn rfl hmemB hchainP hlookB
         have hdomB := hQp.2 hbeven
         obtain ⟨posB, posC, hfindB, hfindC, hBpt, hBcount, hCt0, hCt1r, hex,
             hCfall, hslotGapBC, hslotB_E, hCt1_E⟩ :=
           dfg_odd_child_facts ns p raw hrun ribs hg cause k hsource hcause
             hHnn hbudget frames hlen hrecords b idxJ bE eJ bBorn fJ hmemB hmemJ
             hparB hlookB hlookJ (by omega)
         obtain ⟨drawn, hCx0, hdrawn, hres⟩ := hex
         have hchainC : IndexedAncestor E idxI idxJ :=
           dfg_trans hchainP (IndexedAncestor.edge _ _ eJ
             (List.mem_zipIdx_iff_getElem?.mp hmemJ) hparB)
         have hcontC := dfg_contain ns p raw hrun ribs hg cause k hsource
           hcause eI idxI fI hmemI hodd posI posP pE hfindI hfindP hpmemP
           hpeven hfIt0slot hfIt1slot hHnn hbudget idxJ eJ fJ posC hmemJ hfindC
           hchainC hCt1_E
         have ht0le : fJ.t0 ≤ fJ.t1 := by omega
         have hspanI : 0 < fI.t1 - fI.t0 := by have h := hspan; omega
         have hgapT1 := dfg_odd_line_gap ns p raw hrun ribs hg cause k
           hsource hcause hcos hsin1 hHnn hH1 fI hfIfall hspanI bBorn fJ
           hBpt hdomB.2.2.1 hCt0 drawn hCx0 hdrawn hres (by omega) hCfall hslotGapBC
           hdomB.1 hcontC.2 fJ.t1 ht0le (Int.le_refl _)
         have hexact : dfgLineOf fJ fJ.t1 = fJ.x1 := by
           unfold dfgLineOf
           have hnnV : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))).heights := hHnn
           have hSpos : 0 < fJ.t1 - bBorn.t1 := by omega
           rw [hCfall, hCt0, hBpt, Int.neg_mul, dfg_fdiv_exact_neg_mul _ _ hSpos]
           have hR : run p (fJ.t1 - bBorn.t0) = run p (fJ.t1 - bBorn.t1) := by
             rw [hBpt]
           omega
         have hfin : (run p (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))).heights + 3) - 2 ≤
             (fI.x0 + Int.fdiv ((fI.x1 - fI.x0) * (fJ.t1 - fI.t0))
               (fI.t1 - fI.t0)) - fJ.x1 := by
           have h1 := hgapT1
           rw [hexact] at h1
           exact h1
         omega

 end Elegant.Kinds.IshikawaFinal

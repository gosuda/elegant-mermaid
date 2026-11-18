import Elegant.IshikawaClearanceHard

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-- Master diagonal of the cause route: `x`-coordinate at parameter `t`.
Matches `IshikawaClearanceHardB.masterX` definitionally. -/
def envMasterX (r : Rib) (p : Params) (t : Int) : Int :=
  Int.fdiv ((-run p r.length) * t) r.length

/-- The ENV invariant for the bones born while executing `place`: every
entry-born bone's left end `x1` stays at least `run p r.heights + 1` left of
the master diagonal at its own `t1`. Quantified over the birth frames of a
successful run (`drawn` pinned by `processedOddDraws`), not over the
unrestricted `IndexedBoneGenealogy`, whose `draw` rule allows `drawn` values
that no execution produces and for which the bound is false. -/
def IshikawaEnvInvariant (ns : List Tree.Node) (p : Params) (r : Rib) : Prop :=
  ∃ frames : List Bone,
    frames.length = r.entries.length + 1 ∧
    frames[0]? = some ({ x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length } : Bone) ∧
    ∀ (idx : Nat) (b : Bone), 0 < idx → idx < r.entries.length + 1 →
      frames[idx]? = some b →
      b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1)

section IshikawaClearanceHardAHelpers

private theorem fdiv_bounds (a d : Int) (hd : 0 < d) :
    d * Int.fdiv a d ≤ a ∧ a < d * Int.fdiv a d + d := by
  have h := Int.mul_fdiv_add_fmod a d
  have hf := Int.fmod_nonneg_of_pos a hd
  have hlt := Int.fmod_lt_of_pos a hd
  omega

private theorem run_bounds (p : Params) (x : Int) (hx : 0 ≤ x) (hcos : 0 ≤ p.cos)
    (hsin : 0 < p.sin) :
    p.sin * run p x ≤ x * p.cos ∧ x * p.cos < p.sin * (run p x + 1) := by
  unfold run
  have hnum : 0 ≤ x * p.cos := Int.mul_nonneg hx hcos
  have hb := fdiv_bounds (x * p.cos) p.sin hsin
  have hmul : p.sin * ((x * p.cos).fdiv p.sin + 1) =
      p.sin * (x * p.cos).fdiv p.sin + p.sin := by
    rw [Int.mul_add, Int.mul_one]
  rw [hmul]
  omega

private theorem mul_lt_cancel {s a b : Int} (hs : 0 < s) (h : s * a < s * b) : a < b := by
  rcases Int.lt_trichotomy a b with hc | hc | hc
  · exact hc
  · subst hc
    omega
  · exfalso
    have h2 := Int.mul_lt_mul_of_pos_left hc hs
    omega

/-- The master diagonal decreases by at least `run p w - 2` and at most
`run p w + 1` over any window of width `w ≤ L`: floor rounding loses at
most two and gains at most one per window. This is the arithmetic core of
the ENV induction. -/
theorem master_line_step (p : Params) (L t0 w : Int)
    (hL : 0 < L) (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin)
    (hw0 : 0 ≤ w) (hwL : w ≤ L) :
    run p w - 2 ≤
      Int.fdiv ((-run p L) * t0) L - Int.fdiv ((-run p L) * (t0 + w)) L ∧
    Int.fdiv ((-run p L) * t0) L - Int.fdiv ((-run p L) * (t0 + w)) L ≤
      run p w + 1 := by
  by_cases hzero : w = 0
  · subst hzero
    have hzero_run : run p 0 = 0 := by simp [run]
    rw [hzero_run]
    simp only [Int.add_zero, Int.zero_add]
    omega
  have hwpos : 0 < w := by omega
  have hbL := run_bounds p L (Int.le_of_lt hL) hcos hsin
  have hbW := run_bounds p w hw0 hcos hsin
  have hcrossLo : L * run p w - w + 1 ≤ run p L * w := by
    have h1' : p.sin * (L * run p w) ≤ (w * p.cos) * L := by
      have h := Int.mul_le_mul_of_nonneg_left hbW.1 (Int.le_of_lt hL)
      rw [← Int.mul_assoc L p.sin (run p w), Int.mul_comm L p.sin,
        Int.mul_assoc p.sin L (run p w)] at h
      rw [← Int.mul_assoc L w p.cos, Int.mul_comm L w, Int.mul_assoc w L p.cos,
        Int.mul_comm L p.cos, ← Int.mul_assoc w p.cos L] at h
      exact h
    have h3' : (w * p.cos) * L < p.sin * (run p L + 1) * w := by
      have h := Int.mul_lt_mul_of_pos_right hbL.2 hwpos
      rw [Int.mul_comm (L * p.cos) w, Int.mul_comm L p.cos,
        ← Int.mul_assoc w p.cos L] at h
      exact h
    have hnorm : p.sin * (run p L + 1) * w = p.sin * (w * run p L) + p.sin * w := by
      calc p.sin * (run p L + 1) * w
          = (p.sin * run p L + p.sin * 1) * w := by rw [Int.mul_add]
        _ = p.sin * run p L * w + p.sin * 1 * w := by rw [Int.add_mul]
        _ = p.sin * (w * run p L) + p.sin * w := by
              congr 1
              · rw [Int.mul_assoc, Int.mul_comm (run p L) w, ← Int.mul_assoc]
              · rw [Int.mul_one]
    have h7' : p.sin * (L * run p w) < p.sin * (w * run p L) + p.sin * w := by omega
    have hlt : p.sin * (L * run p w - w) < p.sin * (w * run p L) := by
      have e : p.sin * (L * run p w - w) = p.sin * (L * run p w) - p.sin * w := by
        rw [Int.mul_sub]
      rw [e]
      omega
    have h9 := mul_lt_cancel hsin hlt
    have hcomm : w * run p L = run p L * w := Int.mul_comm _ _
    omega
  have hcrossHi : run p L * w ≤ L * run p w + L := by
    have h1 : p.sin * run p L * w ≤ L * p.cos * w :=
      Int.mul_le_mul_of_nonneg_right hbL.1 hw0
    have h2 : L * p.cos * w = w * p.cos * L := by
      rw [Int.mul_comm (L * p.cos) w, Int.mul_comm L p.cos, ← Int.mul_assoc w p.cos L]
    have h3 : (w * p.cos) * L < (p.sin * (run p w + 1)) * L :=
      Int.mul_lt_mul_of_pos_right hbW.2 hL
    have h4 : (p.sin * (run p w + 1)) * L = p.sin * (L * (run p w + 1)) := by
      rw [← Int.mul_assoc p.sin L (run p w + 1),
        Int.mul_comm (p.sin * (run p w + 1)) L, ← Int.mul_assoc L p.sin (run p w + 1),
        Int.mul_comm L p.sin]
    have h5 : p.sin * run p L * w = p.sin * (run p L * w) := by
      rw [Int.mul_assoc]
    rw [h5, h2] at h1
    rw [h4] at h3
    have hA : p.sin * (run p L * w) ≤ p.sin * (L * (run p w + 1)) := by omega
    have hA' := Int.le_of_mul_le_mul_left hA hsin
    rw [Int.mul_add, Int.mul_one] at hA'
    exact hA'
  have hm0 := fdiv_bounds ((-run p L) * t0) L hL
  have hm1 := fdiv_bounds ((-run p L) * (t0 + w)) L hL
  have hAB : (-run p L) * t0 - (-run p L) * (t0 + w) = run p L * w := by
    rw [← Int.mul_sub]
    have hsub : t0 - (t0 + w) = -w := by omega
    rw [hsub, Int.mul_neg, Int.neg_mul, Int.neg_neg]
  have hDlo : run p L * w - L + 1 ≤
      L * (Int.fdiv ((-run p L) * t0) L - Int.fdiv ((-run p L) * (t0 + w)) L) := by
    rw [Int.mul_sub]
    omega
  have hDhi : L * (Int.fdiv ((-run p L) * t0) L - Int.fdiv ((-run p L) * (t0 + w)) L) ≤
      run p L * w + L - 1 := by
    rw [Int.mul_sub]
    omega
  have hge : L * (run p w - 2) ≤
      L * (Int.fdiv ((-run p L) * t0) L - Int.fdiv ((-run p L) * (t0 + w)) L) := by
    have e1 : L * (run p w - 2) = L * run p w - L * 2 := by rw [Int.mul_sub]
    rw [e1]
    omega
  have hle : L * (Int.fdiv ((-run p L) * t0) L - Int.fdiv ((-run p L) * (t0 + w)) L) ≤
      L * (run p w + 2) - 1 := by
    have e2 : L * (run p w + 2) = L * run p w + L * 2 := by rw [Int.mul_add]
    omega
  constructor
  · exact Int.le_of_mul_le_mul_left hge hL
  · have hlt : L * (Int.fdiv ((-run p L) * t0) L - Int.fdiv ((-run p L) * (t0 + w)) L) <
        L * (run p w + 2) := by omega
    have hless := Int.lt_of_mul_lt_mul_left hlt (by omega : 0 ≤ L)
    omega

/-- Entry slots are strictly increasing in the entry position: two positions
`a < c` give strictly increasing floors because the rib length is at least
the slot denominator. -/
private theorem slot_strict (L d : Int) (hL : 0 < L) (hd : 0 < d) (hLd : d ≤ L)
    (a c : Nat) (hac : a < c) :
    Int.fdiv (L * (a + 1 : Nat)) d < Int.fdiv (L * (c + 1 : Nat)) d := by
  have hstep : Int.fdiv (L * (a + 1 : Nat)) d + 1 ≤ Int.fdiv (L * (a + 1 : Nat) + d) d := by
    have h1 := fdiv_bounds (L * (a + 1 : Nat)) d hd
    have h2 := fdiv_bounds (L * (a + 1 : Nat) + d) d hd
    have hlt : d * Int.fdiv (L * (a + 1 : Nat)) d <
        d * Int.fdiv (L * (a + 1 : Nat) + d) d := by omega
    exact Int.lt_of_mul_lt_mul_left hlt (by omega)
  have hmono : Int.fdiv (L * (a + 1 : Nat) + d) d ≤ Int.fdiv (L * (c + 1 : Nat)) d := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ d by omega),
      Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ d by omega)]
    refine Int.ediv_le_ediv (by omega) ?_
    have h1 : L * ↑(a + 1) + d ≤ L * ↑(a + 1) + L := by omega
    have h2 : L * ↑(a + 1) + L = L * ↑(a + 1) + L * 1 := by
      rw [Int.mul_one]
    have h3 : L * ↑(a + 1) + L * 1 = L * (↑(a + 1) + 1) := by
      rw [← Int.mul_add]
    have h4 : L * (↑(a + 1) + 1) ≤ L * ↑(c + 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hL)
    omega
  omega

/-- The even branch of `depthBone` ignores the parity selector beyond its
branch choice, so any two even depths, and any two `drawn` fields, give the
same bone. -/
private theorem depthBone_even_congr' (p : Params) (par : Bone) (δ : Int) (d d' : Nat)
    (t count margin : Int) (hd : d % 2 = 0) (hd' : d' % 2 = 0) :
    depthBone p { par with drawn := δ } d t count margin = depthBone p par d' t count margin := by
  have h1 : ((d : Nat) % 2 != 0) = false := by rw [hd]; decide
  have h2 : ((d' : Nat) % 2 != 0) = false := by rw [hd']; decide
  simp only [depthBone, h1, h2, Bool.false_eq_true, ite_false]

/-- The odd branch of `depthBone` ignores the parity selector beyond its
branch choice, so any two odd depths give the same bone. -/
private theorem depthBone_even_congr (p : Params) (par : Bone) (δ : Int) (d d' : Nat)
    (t count margin : Int) (hd : d % 2 = 0) (hd' : d' % 2 = 0) :
    depthBone p par d t count margin = depthBone p { par with drawn := δ } d' t count margin := by
  have h1 : ((d : Nat) % 2 != 0) = false := by rw [hd]; decide
  have h2 : ((d' : Nat) % 2 != 0) = false := by rw [hd']; decide
  simp only [depthBone, h1, h2, Bool.false_eq_true, ite_false]

/-- The odd branch of `depthBone` ignores the parity selector beyond its
branch choice, so any two odd depths give the same bone. -/
private theorem depthBone_odd_congr (p : Params) (par : Bone) (d d' : Nat) (t count margin : Int)
    (hd : d % 2 ≠ 0) (hd' : d' % 2 ≠ 0) :
    depthBone p par d t count margin = depthBone p par d' t count margin := by
  have hm : d % 2 = 1 := by omega
  have hm' : d' % 2 = 1 := by omega
  simp only [depthBone, show ((d : Nat) % 2 != 0) = true from by rw [hm]; decide,
    show ((d' : Nat) % 2 != 0) = true from by rw [hm']; decide, ite_true]

end IshikawaClearanceHardAHelpers

/-- Odd-step arithmetic (child of an **even** parent bone): the attachment
point stays on the master diagonal's left, and the diagonal end keeps the
ENV margin. This is the per-child core of `ishikawa_env_invariant`; its two
conjuncts reduce to `attachment_start_margin`, `master_line_step`, and the
fdiv alignment corner described in `EnvEvenStep`. -/
def EnvStepOdd (r : Rib) (p : Params) : Prop :=
  ∀ (par : Bone) (drawn slot : Int) (count : Nat),
    0 < r.length → par.t0 = par.t1 → 0 < par.count + 1 →
    (par.count + 1) * (run p r.heights + 3) ≤ par.x0 - par.x1 →
    drawn + 1 ≤ par.count → par.t0 ≤ slot → slot ≤ r.length →
    par.x0 ≤ envMasterX r p par.t0 + 2 →
    let b := depthBone p { par with drawn := drawn } 1 slot count (run p r.heights + 3)
    b.x0 ≤ envMasterX r p b.t0 + 2 ∧
    b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1)

/-- Even-step arithmetic (child of an **odd** parent bone): the interpolated
attachment stays within two of the master diagonal at the child's slot, and
the reserved bone end keeps the ENV margin. The `x0` conjunct is the
extrapolation bound `M - B ≥ -2` of the plan; it holds for every executed
generated rib (numerically verified over the corpus) but its proof needs the
fdiv alignment corner analysis `fdiv (-run p s * Δ) s + envMasterX r p t0 -
envMasterX r p (t0 + Δ) ≤ 0` for `0 ≤ Δ ≤ s ≤ r.length`, which
`master_line_step` misses by exactly one floor unit. -/
def EnvStepEven (r : Rib) (p : Params) : Prop :=
  ∀ (par : Bone) (slot : Int) (count : Nat),
    0 < r.length → par.t0 < par.t1 →
    par.x1 = par.x0 - run p (par.t1 - par.t0) →
    par.t0 ≤ slot → slot ≤ par.t1 →
    par.x0 ≤ envMasterX r p par.t0 + 2 →
    let b := depthBone p par 2 slot count (run p r.heights + 3)
    b.x0 ≤ envMasterX r p b.t0 + 2 ∧
    b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1)

/-! ### Corrected invariant: birth-chain reserve slack

The raw `EnvStepOdd` / `EnvStepEven` premises are false for executed ribs
(`IshikawaEnvSteps.exec_step_odd_false`, `exec_step_even_false`).  The
numerical study behind this repair (Python simulations of the executed
`place` semantics, ~107k born bones over trees up to five nodes, nineteen
`cos`/`sin` profiles, `L` to 35):

* every executed bone satisfies the **tight** attachment bound
  `par.x0 ≤ envMasterX r p par.t0` (worst case exactly tight);
* the fdiv corner premise of `EnvStepEvenAligned` fails by one unit on 24
  of 65790 executed even children, so no corner premise can discharge the
  even step; instead a diagonal parent either *is* the rib root (window
  `[0, r.length]`, where the corner is an exact equality) or was born by an
  odd step and therefore carries at least three units of reserve room
  `par.x0 + 3 ≤ envMasterX r p par.t0`, which absorbs the corrected
  two-unit corner gap of `corner2`;
* a degenerate parent (born by an even step) carries its full reserve
  `(par.count + 1) * (run p r.heights + 3) ≤ par.x0 - par.x1`, and
  `attachment_start_margin` turns that reserve into both the tight child
  bound and the ENV margin.

`ParentBoneSlack` is exactly this induction-carried premise; the corrected
steps conclude it for the child bone, so `ishikawa_env_invariant` runs
without any step premise. -/

/-- The slack premise carried along the birth chain: tight attachment side,
window sanity, the reserve for degenerate (even-born) bones, and the route
equation with root-exact-or-three-room for diagonal (odd-born or root)
bones. -/
def ParentBoneSlack (r : Rib) (p : Params) (par : Bone) : Prop :=
  0 ≤ par.t0 ∧
    par.t0 ≤ par.t1 ∧
    par.x0 ≤ envMasterX r p par.t0 ∧
    (par.t0 = par.t1 → (par.count + 1) * (run p r.heights + 3) ≤ par.x0 - par.x1) ∧
    (par.t0 < par.t1 →
      par.x1 = par.x0 - run p (par.t1 - par.t0) ∧
        ((par.t0 = 0 ∧ par.x1 = -run p r.length ∧ par.t1 = r.length) ∨
          par.x0 + 3 ≤ envMasterX r p par.t0))

/-- Corrected odd step: the parent is degenerate with its reserve carried by
`ParentBoneSlack`; the conclusion keeps the ENV pair and makes the child a
fresh slack parent. -/
def EnvStepOddSlack (r : Rib) (p : Params) : Prop :=
  ∀ (par : Bone) (drawn slot : Int) (count : Nat),
    0 < r.length → par.t0 = par.t1 → 0 < par.count + 1 →
    drawn + 1 ≤ par.count → par.t0 < slot → slot ≤ r.length →
    ParentBoneSlack r p par →
    let b := depthBone p { par with drawn := drawn } 1 slot count (run p r.heights + 3)
    b.x0 ≤ envMasterX r p b.t0 + 2 ∧
      b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1) ∧
      ParentBoneSlack r p b

/-- Corrected even step: the parent is diagonal; the corner analysis is
replaced by the root-exact shape or the three-unit birth-chain room. -/
def EnvStepEvenSlack (r : Rib) (p : Params) : Prop :=
  ∀ (par : Bone) (slot : Int) (count : Nat),
    0 < r.length → par.t0 < par.t1 → par.t1 ≤ r.length →
    par.t0 ≤ slot → slot ≤ par.t1 →
    ParentBoneSlack r p par →
    let b := depthBone p par 2 slot count (run p r.heights + 3)
    b.x0 ≤ envMasterX r p b.t0 + 2 ∧
      b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1) ∧
      ParentBoneSlack r p b

private theorem run_nonneg_hard (p : Params) (x : Int) (hx : 0 ≤ x) (hcos : 0 ≤ p.cos)
    (hsin : 0 < p.sin) : 0 ≤ run p x := by
  by_cases hneg : run p x < 0
  · exfalso
    have hb := run_bounds p x hx hcos hsin
    rw [Int.mul_add] at hb
    have h1 : p.sin * run p x ≤ p.sin * -1 :=
      Int.mul_le_mul_of_nonneg_left (by omega : run p x ≤ -1) (Int.le_of_lt hsin)
    rw [Int.mul_neg, Int.mul_one] at h1
    have h2 : 0 ≤ x * p.cos := Int.mul_nonneg hx hcos
    omega
  · omega

/-- The master diagonal's floored descent is superadditive in the offset. -/
private theorem master_drop_super (p : Params) (L t0 d : Int) (hL : 0 < L) :
    Int.fdiv ((-run p L) * t0) L + Int.fdiv ((-run p L) * d) L ≤
      Int.fdiv ((-run p L) * (t0 + d)) L := by
  have hb1 := fdiv_bounds ((-run p L) * t0) L hL
  have hb2 := fdiv_bounds ((-run p L) * d) L hL
  have hsplit : (-run p L) * t0 + (-run p L) * d = (-run p L) * (t0 + d) := by
    rw [← Int.mul_add]
  have hle : L * (Int.fdiv ((-run p L) * t0) L + Int.fdiv ((-run p L) * d) L)
      ≤ (-run p L) * (t0 + d) := by
    have hexp : L * (Int.fdiv ((-run p L) * t0) L + Int.fdiv ((-run p L) * d) L) =
        L * Int.fdiv ((-run p L) * t0) L + L * Int.fdiv ((-run p L) * d) L := by
      rw [Int.mul_add]
    rw [hexp]
    omega
  exact Chart.le_fdiv_of_mul_le hL hle

/-- The corrected corner: a child window's floored descent over its own
offset `d` is at most the master diagonal's floored descent over the same
offset plus two units.  The raw corner (gap zero) is false on some executed
even children, missing exactly one unit; the two-unit gap is what the
three-unit birth-chain room absorbs. -/
private theorem corner2 (p : Params) (s L d : Int)
    (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin) (hs : 0 < s) (hsL : s ≤ L) (hds : d ≤ s)
    (hd : 0 ≤ d) :
    Int.fdiv ((-run p s) * d) s ≤ Int.fdiv ((-run p L) * d) L + 2 := by
  have has : 0 ≤ s := Int.le_of_lt hs
  have hL0 : 0 ≤ L := Int.le_of_lt (Int.lt_of_lt_of_le hs hsL)
  have hLpos : 0 < L := Int.lt_of_lt_of_le hs hsL
  have hbs := run_bounds p s has hcos hsin
  have hbb := run_bounds p L hL0 hcos hsin
  have hb1 := fdiv_bounds ((-run p s) * d) s hs
  have hb2 := fdiv_bounds ((-run p L) * d) L hLpos
  -- the child window's per-unit fall dominates the master's
  have g2 : s * run p L ≤ L * run p s + L - 1 := by
    have t1 : s * (p.sin * run p L) ≤ s * (L * p.cos) :=
      Int.mul_le_mul_of_nonneg_left hbb.1 has
    have t2 : L * (s * p.cos) < L * (p.sin * (run p s + 1)) :=
      Int.mul_lt_mul_of_pos_left hbs.2 hLpos
    have heq : s * (L * p.cos) = L * (s * p.cos) := by
      rw [← Int.mul_assoc s L p.cos, Int.mul_comm s L, Int.mul_assoc L s p.cos]
    rw [← heq] at t2
    rw [Int.mul_comm s (p.sin * run p L), Int.mul_assoc,
      Int.mul_comm (run p L) s] at t1
    rw [← Int.mul_assoc L p.sin (run p s + 1), Int.mul_comm L p.sin,
      Int.mul_assoc p.sin L (run p s + 1), Int.mul_add L (run p s) 1,
      Int.mul_one] at t2
    have t3 : p.sin * (s * run p L) < p.sin * (L * run p s + L) := by omega
    have t4 : s * run p L < L * run p s + L :=
      Int.lt_of_mul_lt_mul_left t3 (Int.le_of_lt hsin)
    omega
  have hsuL : L * (s * Int.fdiv ((-run p s) * d) s) ≤ -(L * (run p s * d)) := by
    have h := Int.mul_le_mul_of_nonneg_left hb1.1 hL0
    have n2 : L * ((-run p s) * d) = -(L * (run p s * d)) := by
      rw [Int.neg_mul, Int.mul_neg]
    rw [n2] at h
    exact h
  have hlvS : -(s * (run p L * d)) < L * (s * Int.fdiv ((-run p L) * d) L) + L * s := by
    have h := Int.mul_lt_mul_of_pos_left hb2.2 hs
    rw [Int.mul_add] at h
    rw [Int.mul_comm s L] at h
    have n1 : s * ((-run p L) * d) = -(s * (run p L * d)) := by
      rw [Int.neg_mul, Int.mul_neg]
    have hswap : s * (L * Int.fdiv ((-run p L) * d) L) =
        L * (s * Int.fdiv ((-run p L) * d) L) := by
      rw [← Int.mul_assoc, Int.mul_comm s L, Int.mul_assoc]
    rw [n1, hswap] at h
    exact h
  have hcross : s * (run p L * d) ≤ L * (run p s * d) + L * d - d := by
    have h := Int.mul_le_mul_of_nonneg_left g2 hd
    rw [Int.mul_comm d (L * run p s + L - 1), Int.sub_mul, Int.add_mul, Int.one_mul] at h
    have e1 : d * (s * run p L) = s * (run p L * d) := by
      rw [← Int.mul_assoc, Int.mul_comm d s, Int.mul_assoc, Int.mul_comm d (run p L)]
    have e2 : (L * run p s) * d = L * (run p s * d) := by
      rw [Int.mul_assoc]
    rw [e1, e2] at h
    exact h
  have hds' : d ≤ s := hds
  have hiv : L * d ≤ L * s := Int.mul_le_mul_of_nonneg_left hds' hL0
  have hU2 : L * (s * Int.fdiv ((-run p s) * d) s) <
      L * (s * Int.fdiv ((-run p L) * d) L) + 2 * (L * s) := by omega
  have hpack : s * (Int.fdiv ((-run p L) * d) L + 2) =
      s * Int.fdiv ((-run p L) * d) L + 2 * s := by
    rw [Int.mul_add, Int.mul_comm 2 s]
  have hpackL : L * (s * (Int.fdiv ((-run p L) * d) L + 2)) =
      L * (s * Int.fdiv ((-run p L) * d) L) + 2 * (L * s) := by
    rw [hpack, Int.mul_add,
      ← Int.mul_assoc L 2 s, Int.mul_comm L 2, Int.mul_assoc 2 L s]
  rw [← hpackL] at hU2
  have hA := Int.lt_of_mul_lt_mul_left hU2 (Int.le_of_lt hLpos)
  have hB := Int.lt_of_mul_lt_mul_left hA (Int.le_of_lt hs)
  omega

/-- The corrected odd step holds for every degenerate parent that carries
the birth-chain slack: the reserve turns the attachment into a full margin
left of the parent start, and the master-line bound pays for the rest. -/
theorem env_step_odd_slack (r : Rib) (p : Params)
    (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin) (hH : 0 ≤ r.heights) :
    EnvStepOddSlack r p := by
  intro par drawn slot count hlen hdeg hcount hdrawn hstrict hslotL hslack
  obtain ⟨ht0nn, _, htight, hresC, _⟩ := hslack
  have hres := hresC hdeg
  dsimp only
  have hHnn : 0 ≤ run p r.heights := run_nonneg_hard p r.heights hH hcos hsin
  have hmargin : 0 ≤ run p r.heights + 3 := by omega
  have hd := depthBone_odd_endpoints p ({ par with drawn := drawn } : Bone) 1 slot count
    (run p r.heights + 3) (by decide : (1 : Nat) % 2 ≠ 0)
  obtain ⟨ht0, ht1, hx0b, hx1b⟩ := hd
  have e0 : ({ par with drawn := drawn } : Bone).x0 = par.x0 := rfl
  have e1 : ({ par with drawn := drawn } : Bone).t0 = par.t0 := rfl
  have e2 : ({ par with drawn := drawn } : Bone).x1 = par.x1 := rfl
  have e3 : ({ par with drawn := drawn } : Bone).count = par.count := rfl
  have e4 : ({ par with drawn := drawn } : Bone).drawn = drawn := rfl
  rw [e0, e2, e3, e4] at hx0b
  rw [e0, e1] at hx1b
  rw [e1] at ht0
  have k1 : 0 ≤ par.x0 - par.x1 := by
    have := Int.mul_nonneg (Int.le_of_lt hcount) hmargin
    omega
  have k3 : (par.x0 - par.x1) * 1 ≤ (par.x0 - par.x1) * (par.count - drawn) :=
    Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ par.count - drawn by omega) k1
  simp only [Int.mul_one] at k3
  have hnum : (par.x1 - par.x0) * (par.count - drawn) ≤ (par.count + 1) * 0 := by
    rw [Int.mul_zero]
    have k2 : (par.x1 - par.x0) * (par.count - drawn)
        = -((par.x0 - par.x1) * (par.count - drawn)) := by
      rw [show par.x1 - par.x0 = -(par.x0 - par.x1) from by omega, Int.neg_mul]
    omega
  have hfall : Int.fdiv ((par.x1 - par.x0) * (par.count - drawn)) (par.count + 1) ≤ 0 :=
    Chart.fdiv_le_of_le_mul hcount hnum
  have ham := attachment_start_margin par.x0 par.x1 par.count drawn (run p r.heights + 3)
    hcount hmargin hres hdrawn
  have hw0 : 0 ≤ slot - par.t0 := by omega
  have hwL : slot - par.t0 ≤ r.length := by omega
  have hmls := master_line_step p r.length par.t0 (slot - par.t0) hlen hcos hsin hw0 hwL
  have eslot : par.t0 + (slot - par.t0) = slot := by omega
  rw [eslot] at hmls
  refine ⟨?_, ?_, ⟨ht0nn, ?_, ?_, ?_, ?_⟩⟩
  · rw [hx0b, ht0]
    omega
  · rw [hx1b, ht1, hx0b]
    simp only [envMasterX] at htight ⊢
    omega
  · rw [ht1]
    omega
  · rw [ht0, hx0b]
    omega
  · intro hdeg'
    rw [ht0, ht1] at hdeg'
    exact absurd hdeg' (by omega)
  · intro _
    refine ⟨?_, ?_⟩
    · rw [ht1, ht0]
      exact hx1b
    · rw [ht0, hx0b]
      omega

/-- The corrected even step holds for every diagonal parent carrying the
birth-chain slack: the root's window coincides with the master diagonal
exactly, and an odd-born parent's three reserve units absorb the corrected
corner gap. -/
theorem env_step_even_slack (r : Rib) (p : Params)
    (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin) (hH : 0 ≤ r.heights) :
    EnvStepEvenSlack r p := by
  intro par slot count hlen hdiag hlen2 hslot0 hslot1 hslack
  obtain ⟨ht0nn, _, htight, _, hdiagC⟩ := hslack
  obtain ⟨hroute, hroom⟩ := hdiagC hdiag
  dsimp only
  have hmargin : 0 ≤ run p r.heights + 3 := by
    have h := run_nonneg_hard p r.heights hH hcos hsin
    omega
  have hlen' : 0 < par.t1 - par.t0 := by omega
  have hsmL : par.t1 - par.t0 ≤ r.length := by omega
  have hd' : 0 ≤ slot - par.t0 := by omega
  have hb := depthBone_even_endpoints p par 2 slot count (run p r.heights + 3)
    (by decide : (2 : Nat) % 2 = 0)
  obtain ⟨ht0, ht1, hx1e⟩ := hb
  have h2even : ((2 : Nat) % 2 != 0) = false := by decide
  have hx0e : (depthBone p par 2 slot count (run p r.heights + 3)).x0 =
      par.x0 + Int.fdiv ((par.x1 - par.x0) * (slot - par.t0)) (par.t1 - par.t0) := by
    simp only [depthBone, h2even, Bool.false_eq_true, ite_false]
  have hnum : (par.x1 - par.x0) * (slot - par.t0) =
      (-run p (par.t1 - par.t0)) * (slot - par.t0) := by
    rw [show par.x1 - par.x0 = -run p (par.t1 - par.t0) from by omega]
  rw [hnum] at hx0e
  have hbx0 : (depthBone p par 2 slot count (run p r.heights + 3)).x0
      ≤ envMasterX r p slot := by
    rw [hx0e]
    obtain ⟨hz0, hx1L, ht1L⟩ | hroom3 := hroom
    · have hsL : par.t1 - par.t0 = r.length := by rw [ht1L, hz0, Int.sub_zero]
      have hpx0 : par.x0 = 0 := by
        rw [hz0, ht1L, Int.sub_zero] at hroute
        rw [hx1L] at hroute
        omega
      rw [hsL, hz0, Int.sub_zero, hpx0, Int.zero_add]
      simp only [envMasterX]
      omega
    · have hc := corner2 p (par.t1 - par.t0) r.length (slot - par.t0) hcos hsin
        hlen' hsmL (by omega) hd'
      have hmd := master_drop_super p r.length par.t0 (slot - par.t0) hlen
      have eslot : par.t0 + (slot - par.t0) = slot := by omega
      rw [eslot] at hmd
      simp only [envMasterX] at htight hroom3 hmd ⊢
      omega
  have hb2 := boneLength_margin p count (run p r.heights + 3) hmargin
  have hbc : (depthBone p par 2 slot count (run p r.heights + 3)).count = count := by
    simp only [depthBone, h2even, Bool.false_eq_true, ite_false]
  have hbl : ((count : Int) + 1) * (run p r.heights + 3)
      ≤ boneLength p count (run p r.heights + 3) :=
    Int.le_max_right _ _
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [ht0]
    omega
  · rw [hx1e, ht1]
    omega
  · rw [ht0]
    omega
  · rw [ht0, ht1]
    omega
  · rw [ht0]
    exact hbx0
  · intro _
    rw [hx1e, hbc]
    omega
  · intro habs
    rw [ht0, ht1] at habs
    exact absurd habs (by omega)

/-- ENV invariant for a generated rib: every bone born while `place` executes
keeps its diagonal end `run p r.heights + 1` left of the master line. -/
theorem ishikawa_env_invariant (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hcause : cause ∈ children ns 0) (hrib : generatedRib ns (cause, k) ∈ ribs)
    (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed) :
    IshikawaEnvInvariant ns p
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) := by
  obtain ⟨r, hrdef⟩ : ∃ r, r = effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k)) := ⟨_, rfl⟩
  rw [← hrdef] at hplace ⊢
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hcauseLt : cause < ns.length := List.mem_range.mp (List.mem_filter.mp hcause).1
  have hne : ns ≠ [] := by
    intro hnil
    rw [hnil] at hcauseLt
    exact Nat.not_lt_zero _ hcauseLt
  have hparameters := successful_slope_parameters ns p raw hne hrun
  have hcos : 0 ≤ p.cos := hparameters.1
  have hsin : 0 < p.sin := Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) hparameters.2
  obtain ⟨frames, hlength, hrootFrame, hrecords, _⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  refine ⟨frames, hlength, hrootFrame, ?_⟩
  have hentriesEq : r.entries = (generatedRib ns (cause, k)).entries := by rw [hrdef]; rfl
  have src_mem : ∀ (e : Entry) (i : Nat),
      (e, i) ∈ r.entries.zipIdx → (e, i) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
    fun e i h => hentriesEq ▸ h
  have slotMono : ∀ (a c : Nat), a ≤ c → 0 ≤ r.length →
      Int.fdiv (r.length * (a + 1 : Nat)) (r.entries.length + 1 : Nat) ≤
        Int.fdiv (r.length * (c + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    intro a c hac hlen
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega : 0 ≤ ((r.entries.length + 1 : Nat) : Int)),
      Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
    refine Int.ediv_le_ediv (by omega) ?_
    exact Int.mul_le_mul_of_nonneg_left (by omega) hlen
  have key : ∀ (d : Nat) (e : Entry) (idx : Nat) (b : Bone),
      (e, idx) ∈ r.entries.zipIdx → e.depth = d → idx < r.entries.length →
      frames[idx + 1]? = some b →
      ParentBoneSlack r p b ∧
      b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1) := by
    intro d
    induction d with
    | zero =>
      intro e idx b hmem hdepth hlt hframe
      by_cases hroot : e.parent = -1
      · have hd2 := generated_root_depth ns cause k hlink hcause e idx
          (src_mem e idx hmem) hroot
        omega
      · obtain ⟨doneE, restE, hprefixE, _⟩ := List.eq_append_cons_of_mem hmem
        obtain ⟨_, _, _, _, hparentFrame, _, _⟩ :=
          hrecords doneE e idx restE hprefixE
        have hownerLt : (e.parent + 1).toNat < frames.length :=
          (List.getElem?_eq_some_iff.mp hparentFrame).1
        have hlb := generated_entry_parent_lower_bound ns cause k e idx (src_mem e idx hmem)
        have hge : 0 ≤ e.parent := by omega
        have hownEq : (e.parent + 1).toNat = e.parent.toNat + 1 := by
          omega
        have hparentLt : e.parent.toNat < r.entries.length := by omega
        have heP : (r.entries[e.parent.toNat]'hparentLt, e.parent.toNat) ∈ r.entries.zipIdx :=
          List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hparentLt)
        have hd := generated_parent_child_depth ns cause k hlink hcause
          (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
          (src_mem _ _ heP) (src_mem e idx hmem) (by rw [Int.toNat_of_nonneg hge])
        omega
    | succ d ihd =>
      intro e idx b hmem hdepth hlt hframe
      obtain ⟨doneE, restE, hprefixE, _⟩ := List.eq_append_cons_of_mem hmem
      obtain ⟨pos, parentFrame, born, hpos, hparentFrame, hbornLookup, hborn⟩ :=
        hrecords doneE e idx restE hprefixE
      have hbf : b = born := Option.some.inj (hframe.symm.trans hbornLookup)
      obtain ⟨slot, hslot⟩ : ∃ slot : Int,
          slot = Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) :=
        ⟨_, rfl⟩
      rw [← hslot] at hborn
      have hownerLt : (e.parent + 1).toNat < frames.length :=
        (List.getElem?_eq_some_iff.mp hparentFrame).1
      have hmemSrc : e ∈ (generatedRib ns (cause, k)).entries :=
        List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp (src_mem e idx hmem))
      by_cases hroot : e.parent = -1
      · -- root child: depth 2, parent frame is the rib root
        have hnodeMem : e.node ∈ children ns cause :=
          generated_root_child_membership ns cause k e idx (src_mem e idx hmem) hroot
        have hnodeLt : e.node < ns.length := List.mem_range.mp (List.mem_filter.mp hnodeMem).1
        have hn : ns[e.node]? = some (ns[e.node]'hnodeLt) := List.getElem?_eq_getElem hnodeLt
        have hdims := successful_node_dimensions ns p raw hrun (ns[e.node]'hnodeLt)
          (List.mem_of_getElem? hn)
        have hheightsEq : r.heights = (generatedRib ns (cause, k)).heights := by
          rw [hrdef]; rfl
        have hheights : 1 ≤ r.heights := by
          rw [hheightsEq, (generated_rib_fields ns cause k).2.2.2]
          have hm := measured_entry_height_bound ns (generatedRib ns (cause, k)).entries e
            hmemSrc (ns[e.node]'hnodeLt) hn
          omega
        have hneEntries : (generatedRib ns (cause, k)).entries.isEmpty = false := by
          cases hentries : (generatedRib ns (cause, k)).entries with
          | nil => rw [hentries] at hmemSrc; exact absurd hmemSrc (by simp)
          | cons child rest => rfl
        have hsource : generatedRib ns (cause, k) ∈ ribs := hrib
        have hbudget := generated_reservation_budget ns p ribs hg
          (generatedRib ns (cause, k)) hsource hneEntries
        have hLd : ((r.entries.length + 1 : Nat) : Int) ≤ r.length := by
          have hc : (0 : Int) ≤ ((r.entries.length + 1 : Nat) : Int) := by omega
          have hmul := Int.mul_le_mul_of_nonneg_left hheights hc
          have h1 : ((r.entries.length + 1 : Nat) : Int) * r.heights ≤ r.length := by
            rw [hentriesEq, hheightsEq, hrdef]
            exact hbudget
          omega
        have hrlen : 0 < r.length := by omega
        have hd2 := generated_root_depth ns cause k hlink hcause e idx
          (src_mem e idx hmem) hroot
        rw [hd2] at hborn
        have hzero : (e.parent + 1).toNat = 0 := by rw [hroot]; rfl
        rw [hzero] at hparentFrame
        have hrootEq : parentFrame =
            ({ x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length } : Bone) :=
          Option.some.inj (hparentFrame.symm.trans hrootFrame)
        have h2n : ((2 : Nat) % 2 != 0) = false := by decide
        have hshape := depthBone_even_endpoints p
          { parentFrame with drawn := processedOddDraws doneE ((e.parent + 1).toNat) } 2 slot
          (children ns e.node).length (run p r.heights + 3) (by decide : (2 : Nat) % 2 = 0)
        rw [← hborn] at hshape
        have hmargin : 0 ≤ run p r.heights :=
          Int.fdiv_nonneg (Int.mul_nonneg (by omega : 0 ≤ r.heights) hcos) (Int.le_of_lt hsin)
        have hbl := boneLength_margin p (children ns e.node).length (run p r.heights + 3)
          (by omega)
        have hbx0 : born.x0 = envMasterX r p slot := by
          rw [hborn, hrootEq]
          simp only [depthBone, h2n, Bool.false_eq_true, ite_false, Int.sub_zero,
            Int.zero_add, envMasterX]
        rw [hbf]
        have hslotNN : 0 ≤ slot := by
          rw [hslot]
          exact Int.fdiv_nonneg
            (Int.mul_nonneg (Int.le_of_lt hrlen)
              (by omega : (0 : Int) ≤ ((pos.2 + 1 : Nat) : Int)))
            (by omega : (0 : Int) ≤ ((r.entries.length + 1 : Nat) : Int))
        have hbc : born.count = ((children ns e.node).length : Int) := by
          rw [hborn, hrootEq]
          simp only [depthBone, h2n, Bool.false_eq_true, ite_false]
        have hbl2 : (((children ns e.node).length : Int) + 1) * (run p r.heights + 3)
            ≤ boneLength p (children ns e.node).length (run p r.heights + 3) :=
          Int.le_max_right _ _
        refine ⟨?_, by rw [hshape.2.1, hshape.2.2, hbx0]; omega⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hshape.1]; exact hslotNN
        · exact Int.le_of_eq (hshape.1.trans hshape.2.1.symm)
        · rw [hshape.1, hbx0]; exact Int.le_of_eq rfl
        · intro hdeg
          rw [hshape.1, hshape.2.1] at hdeg
          rw [hbc, hshape.2.2]; omega
        · intro habs
          rw [hshape.1, hshape.2.1] at habs
          exact absurd habs (by omega)
      · -- non-root child
        have hlb := generated_entry_parent_lower_bound ns cause k e idx (src_mem e idx hmem)
        have hge : 0 ≤ e.parent := by omega
        have hownEq : (e.parent + 1).toNat = e.parent.toNat + 1 := by
          omega
        have hparEq : e.parent = (e.parent.toNat : Int) := (Int.toNat_of_nonneg hge).symm
        have hparentLt : e.parent.toNat < r.entries.length := by omega
        have hparentLookup : r.entries[e.parent.toNat]? =
            some (r.entries[e.parent.toNat]'hparentLt) := List.getElem?_eq_getElem hparentLt
        have heP : (r.entries[e.parent.toNat]'hparentLt, e.parent.toNat) ∈ r.entries.zipIdx :=
          List.mem_zipIdx_iff_getElem?.mpr hparentLookup
        obtain ⟨doneP, restP, hprefixP, _⟩ := List.eq_append_cons_of_mem heP
        obtain ⟨posP, grandFrame, parentBorn, hposP, hgrandFrame, hparentBornLookup, hparentBorn⟩ :=
          hrecords doneP (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat restP hprefixP
        rw [hownEq] at hparentFrame
        have hPB : parentBorn = parentFrame :=
          Option.some.inj (hparentBornLookup.symm.trans hparentFrame)
        have hd := generated_parent_child_depth ns cause k hlink hcause
          (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
          (src_mem _ _ heP) (src_mem e idx hmem) hparEq
        have hdepthPar : (r.entries[e.parent.toNat]'hparentLt).depth = d := by omega
        have ihP := ihd (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat parentBorn heP
          hdepthPar hparentLt hparentBornLookup
        rw [hPB] at ihP
        have hnodeMem : e.node ∈ children ns (r.entries[e.parent.toNat]'hparentLt).node :=
          generated_parent_child_membership ns cause k
            (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
            (src_mem _ _ heP) (src_mem e idx hmem) hparEq
        have hnodeLt : e.node < ns.length := List.mem_range.mp (List.mem_filter.mp hnodeMem).1
        have hn : ns[e.node]? = some (ns[e.node]'hnodeLt) := List.getElem?_eq_getElem hnodeLt
        have hdims := successful_node_dimensions ns p raw hrun (ns[e.node]'hnodeLt)
          (List.mem_of_getElem? hn)
        have hheightsEq : r.heights = (generatedRib ns (cause, k)).heights := by rw [hrdef]; rfl
        have hheights : 1 ≤ r.heights := by
          rw [hheightsEq, (generated_rib_fields ns cause k).2.2.2]
          have hm := measured_entry_height_bound ns (generatedRib ns (cause, k)).entries e
            hmemSrc (ns[e.node]'hnodeLt) hn
          omega
        have hneEntries : (generatedRib ns (cause, k)).entries.isEmpty = false := by
          cases hentries : (generatedRib ns (cause, k)).entries with
          | nil => rw [hentries] at hmemSrc; exact absurd hmemSrc (by simp)
          | cons child rest => rfl
        have hsource : generatedRib ns (cause, k) ∈ ribs := hrib
        have hbudget := generated_reservation_budget ns p ribs hg
          (generatedRib ns (cause, k)) hsource hneEntries
        have hLd : ((r.entries.length + 1 : Nat) : Int) ≤ r.length := by
          have hc : (0 : Int) ≤ ((r.entries.length + 1 : Nat) : Int) := by omega
          have hmul := Int.mul_le_mul_of_nonneg_left hheights hc
          have h1 : ((r.entries.length + 1 : Nat) : Int) * r.heights ≤ r.length := by
            rw [hentriesEq, hheightsEq, hrdef]
            exact hbudget
          omega
        have hrlen : 0 < r.length := by omega
        have hslotLen : slot ≤ r.length := by
          have hmemO := List.mem_of_find?_eq_some hpos
          have hgetO := List.mem_zipIdx_iff_getElem?.mp hmemO
          have hposLt : pos.2 < r.order.length := (List.getElem?_eq_some_iff.mp hgetO).1
          have hordLe : r.order.length ≤ r.entries.length := by
            rw [hrdef]
            exact Elegant.Kinds.IshikawaSeparation.generated_effective_order_length_le ns
              (measuredSideLength p ribs) cause k
          calc slot = Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) :=
              hslot
            _ ≤ Int.fdiv (r.length * (r.entries.length + 1 : Nat))
                (r.entries.length + 1 : Nat) := slotMono _ _ (by omega) (Int.le_of_lt hrlen)
            _ = r.length := Int.mul_fdiv_cancel r.length (by omega)
        obtain ⟨slotP, hslotP⟩ : ∃ slotP : Int,
            slotP = Int.fdiv (r.length * (posP.2 + 1 : Nat)) (r.entries.length + 1 : Nat) :=
          ⟨_, rfl⟩
        rw [← hslotP] at hparentBorn
        have horderEq : r.order = (generatedRib ns (cause, k)).order := by rw [hrdef]; rfl
        have hposSrc : (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == idx) =
            some pos := by
          rw [← horderEq]; exact hpos
        have hposPSrc : (generatedRib ns (cause, k)).order.zipIdx.find?
            (fun v => v.1 == e.parent.toNat) = some posP := by
          rw [← horderEq]; exact hposP
        by_cases heven : e.depth % 2 = 0
        · -- even child of an odd parent: EnvStepEven
          have hoddPar : (r.entries[e.parent.toNat]'hparentLt).depth % 2 ≠ 0 := by
            have h2 := hd; have h3 := heven; omega
          have hlbP := generated_entry_parent_lower_bound ns cause k
            (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat (src_mem _ _ heP)
          have hrootP : (r.entries[e.parent.toNat]'hparentLt).parent ≠ -1 := by
            intro hpp
            have hd2 := generated_root_depth ns cause k hlink hcause
              (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat (src_mem _ _ heP) hpp
            omega
          have hgeP : 0 ≤ (r.entries[e.parent.toNat]'hparentLt).parent := by omega
          have hownP : ((r.entries[e.parent.toNat]'hparentLt).parent + 1).toNat =
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat + 1 :=
            by omega
          have hgrandLt : (r.entries[e.parent.toNat]'hparentLt).parent.toNat <
              r.entries.length := by
            have hb := (List.getElem?_eq_some_iff.mp hgrandFrame).1
            omega
          have hgrandLookup : r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]? =
              some (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt) :=
            List.getElem?_eq_getElem hgrandLt
          have heG : (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt,
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat) ∈ r.entries.zipIdx :=
            List.mem_zipIdx_iff_getElem?.mpr hgrandLookup
          obtain ⟨doneG, restG, hprefixG, _⟩ := List.eq_append_cons_of_mem heG
          obtain ⟨posG, ggFrame, grandBorn, hposG, hggFrame, hgrandBornLookup, hgrandBorn⟩ :=
            hrecords doneG
              (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt)
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat restG hprefixG
          obtain ⟨slotG, hslotG⟩ : ∃ slotG : Int,
              slotG = Int.fdiv (r.length * (posG.2 + 1 : Nat)) (r.entries.length + 1 : Nat) :=
            ⟨_, rfl⟩
          rw [← hslotG] at hgrandBorn
          rw [hownP] at hgrandFrame
          have hGF : grandBorn = grandFrame :=
            Option.some.inj (hgrandBornLookup.symm.trans hgrandFrame)
          have hposGSrc : (generatedRib ns (cause, k)).order.zipIdx.find?
              (fun v => v.1 == (r.entries[e.parent.toNat]'hparentLt).parent.toNat) = some posG := by
            rw [← horderEq]; exact hposG
          have hcastP : (r.entries[e.parent.toNat]'hparentLt).parent =
              ((r.entries[e.parent.toNat]'hparentLt).parent.toNat : Int) :=
            (Int.toNat_of_nonneg hgeP).symm
          have hdepthGP := generated_parent_child_depth ns cause k hlink hcause
            (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt)
            (r.entries[e.parent.toNat]'hparentLt)
            (r.entries[e.parent.toNat]'hparentLt).parent.toNat e.parent.toNat
            (src_mem _ _ heG) (src_mem _ _ heP) hcastP
          have hgrandEven : (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).depth % 2 = 0 := by
            have h2 := hdepthGP; have h3 := hoddPar
            have hm := Nat.mod_lt (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).depth (by decide : 0 < 2)
            omega
          have hoddEp := depthBone_odd_endpoints p
            ({ grandFrame with drawn := (processedOddDraws doneP
                ((r.entries[e.parent.toNat]'hparentLt).parent + 1).toNat) } : Bone)
            (r.entries[e.parent.toNat]'hparentLt).depth slotP
            (children ns (r.entries[e.parent.toNat]'hparentLt).node).length
            (run p r.heights + 3) hoddPar
          rw [← hparentBorn, hPB] at hoddEp
          have hevenEpG := depthBone_even_endpoints p
            ({ ggFrame with drawn := (processedOddDraws doneG
                ((r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).parent
                  + 1).toNat) } : Bone)
            (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).depth slotG
            (children ns
              (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).node).length
            (run p r.heights + 3) hgrandEven
          rw [← hgrandBorn, hGF] at hevenEpG
          have hT0G : grandFrame.t0 = slotG := hevenEpG.1
          have hT1P : parentFrame.t1 = slotP := hoddEp.2.1
          have hT0P : parentFrame.t0 = slotG := by
            have h1 : parentFrame.t0 = grandFrame.t0 := hoddEp.1
            rw [h1, hT0G]
          have hPX1 : parentFrame.x1 =
              parentFrame.x0 - run p (parentFrame.t1 - parentFrame.t0) := by
            have h1 : parentFrame.x1 =
                parentFrame.x0 - run p (slotP - grandFrame.t0) := hoddEp.2.2.2
            rw [hT1P, hT0P, h1, hT0G]
          have hchainG : IndexedAncestor (generatedRib ns (cause, k)).entries
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat idx :=
            IndexedAncestor.tail
              (IndexedAncestor.edge
                (r.entries[e.parent.toNat]'hparentLt).parent.toNat e.parent.toNat
                (r.entries[e.parent.toNat]'hparentLt)
                (List.mem_zipIdx_iff_getElem?.mp (src_mem _ _ heP)) hcastP)
              e (List.mem_zipIdx_iff_getElem?.mp (src_mem e idx hmem)) hparEq
          have hordGP := (generated_ancestor_order ns cause k
            (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt)
            (r.entries[e.parent.toNat]'hparentLt)
            (r.entries[e.parent.toNat]'hparentLt).parent.toNat e.parent.toNat
            (src_mem _ _ heG) (src_mem _ _ heP)
            (IndexedAncestor.edge
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat e.parent.toNat
              (r.entries[e.parent.toNat]'hparentLt)
              (List.mem_zipIdx_iff_getElem?.mp (src_mem _ _ heP)) hcastP)
            posG posP hposGSrc hposPSrc).1 hgrandEven
          have hordGC := (generated_ancestor_order ns cause k
            (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt)
            e
            (r.entries[e.parent.toNat]'hparentLt).parent.toNat idx
            (src_mem _ _ heG) (src_mem e idx hmem) hchainG posG pos hposGSrc hposSrc).1
            hgrandEven
          have hordPC := (generated_parent_child_order ns cause k
            (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
            (src_mem _ _ heP) (src_mem e idx hmem) hparEq posP pos hposPSrc hposSrc).2 hoddPar
          have h2even : parentFrame.t0 < parentFrame.t1 := by
            rw [hT0P, hT1P, hslotG, hslotP]
            exact slot_strict r.length ((r.entries.length + 1 : Nat) : Int) hrlen
              (by omega) hLd posG.2 posP.2 hordGP
          have h4even : parentFrame.t0 ≤ slot := by
            rw [hT0P, hslotG, hslot]
            exact slotMono posG.2 pos.2 (by omega) (Int.le_of_lt hrlen)
          have h5even : slot ≤ parentFrame.t1 := by
            rw [hT1P, hslotP, hslot]
            exact slotMono pos.2 posP.2 (by omega) (Int.le_of_lt hrlen)
          have hsmL : parentFrame.t1 ≤ r.length := by
            rw [hT1P, hslotP]
            have hmemOP := List.mem_of_find?_eq_some hposP
            have hgetOP := List.mem_zipIdx_iff_getElem?.mp hmemOP
            have hposPLt : posP.2 < r.order.length := (List.getElem?_eq_some_iff.mp hgetOP).1
            have hordLeP : r.order.length ≤ r.entries.length := by
              rw [hrdef]
              exact Elegant.Kinds.IshikawaSeparation.generated_effective_order_length_le ns
                (measuredSideLength p ribs) cause k
            calc Int.fdiv (r.length * (posP.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
                = slotP := hslotP.symm
              _ ≤ Int.fdiv (r.length * (r.entries.length + 1 : Nat))
                  (r.entries.length + 1 : Nat) := by
                rw [hslotP]
                exact slotMono posP.2 r.entries.length (by omega) (Int.le_of_lt hrlen)
              _ = r.length := Int.mul_fdiv_cancel r.length (by omega)
          have hstepEven := env_step_even_slack r p hcos hsin (by omega)
          obtain ⟨hx0s, hx1s, hslacks⟩ := hstepEven parentFrame slot
            (children ns e.node).length hrlen
            h2even hsmL h4even h5even ihP.1
          have hbornE : born =
              depthBone p parentFrame 2 slot (children ns e.node).length (run p r.heights + 3) := by
            rw [hborn]
            exact depthBone_even_congr' p parentFrame
              (processedOddDraws doneE ((e.parent + 1).toNat)) e.depth 2 slot
              (children ns e.node).length (run p r.heights + 3) heven
              (by decide : (2 : Nat) % 2 = 0)
          rw [← hbornE] at hx0s hx1s hslacks
          rw [hbf]
          exact ⟨hslacks, hx1s⟩
        · -- odd child of an even parent: EnvStepOdd
          have hevenPar : (r.entries[e.parent.toNat]'hparentLt).depth % 2 = 0 := by
            have h2 := hd; have h3 := heven; omega
          have hodd : e.depth % 2 ≠ 0 := by omega
          have hPeven := depthBone_even_endpoints p
            ({ grandFrame with drawn := (processedOddDraws doneP
                ((r.entries[e.parent.toNat]'hparentLt).parent + 1).toNat) } : Bone)
            (r.entries[e.parent.toNat]'hparentLt).depth slotP
            (children ns (r.entries[e.parent.toNat]'hparentLt).node).length
            (run p r.heights + 3) hevenPar
          rw [← hparentBorn, hPB] at hPeven
          have hcountP : parentFrame.count =
              ((children ns (r.entries[e.parent.toNat]'hparentLt).node).length : Int) := by
            rw [← hPB, hparentBorn]
            have hcond : ((r.entries[e.parent.toNat]'hparentLt).depth % 2 != 0) = false := by
              rw [hevenPar]; decide
            simp only [depthBone, hcond, Bool.false_eq_true, ite_false]
          obtain ⟨_, hres2⟩ := even_native_reservation p
            ({ grandFrame with drawn := (processedOddDraws doneP
                ((r.entries[e.parent.toNat]'hparentLt).parent + 1).toNat) } : Bone)
            (r.entries[e.parent.toNat]'hparentLt).depth slotP
            (children ns (r.entries[e.parent.toNat]'hparentLt).node).length
            (run p r.heights + 3) hevenPar
          rw [← hparentBorn, hPB] at hres2
          have hprefixE' : (generatedRib ns (cause, k)).entries.zipIdx =
              doneE ++ (e, idx) :: restE := hentriesEq ▸ hprefixE
          have hdrawBound := generated_current_odd_prefix_draw_bound ns cause k hlink hcause
            doneE e idx restE hprefixE' (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat
            (src_mem _ _ heP) hparEq hodd
          have hordP2 := (generated_parent_child_order ns cause k
            (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
            (src_mem _ _ heP) (src_mem e idx hmem) hparEq posP pos hposPSrc hposSrc).1 hevenPar
          have hstrictP : parentFrame.t0 < slot := by
            rw [hPeven.1, hslotP, hslot]
            exact slot_strict r.length ((r.entries.length + 1 : Nat) : Int) hrlen
              (by omega) hLd posP.2 pos.2 hordP2
          have hstepOdd := env_step_odd_slack r p hcos hsin (by omega)
          obtain ⟨hx0s, hx1s, hslacks⟩ := hstepOdd parentFrame
            (processedOddDraws doneE ((e.parent + 1).toNat)) slot (children ns e.node).length
            hrlen (by rw [hPeven.1, hPeven.2.1])
            (by rw [hcountP]; omega)
            (by rw [hownEq, hcountP]; omega)
            hstrictP hslotLen ihP.1
          have hbornO : born =
              depthBone p { parentFrame with drawn := processedOddDraws doneE ((e.parent + 1).toNat) }
                1 slot (children ns e.node).length (run p r.heights + 3) := by
            rw [hborn]
            exact depthBone_odd_congr p
              ({ parentFrame with drawn := processedOddDraws doneE ((e.parent + 1).toNat) } : Bone)
              e.depth 1 slot (children ns e.node).length (run p r.heights + 3) hodd
              (by decide : (1 : Nat) % 2 ≠ 0)
          rw [← hbornO] at hx0s hx1s hslacks
          rw [hbf]
          exact ⟨hslacks, hx1s⟩
  intro idx b h0idx hidx hframe
  cases hentries : r.entries with
  | nil =>
    rw [hentries] at hidx
    simp only [List.length_nil, Nat.zero_add] at hidx
    omega
  | cons head tail =>
    have hidx2 : idx < tail.length + 1 + 1 := by
      rw [hentries] at hidx
      simpa only [List.length_cons] using hidx
    have hlt' : idx - 1 < r.entries.length := by
      rw [hentries]
      simp only [List.length_cons]
      omega
    have he : (r.entries[idx - 1], idx - 1) ∈ r.entries.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hlt')
    have hidxEq : idx = idx - 1 + 1 := by omega
    rw [hidxEq] at hframe
    exact (key (r.entries[idx - 1].depth) (r.entries[idx - 1]) (idx - 1) b he rfl hlt'
      hframe).2

end Elegant.Ishikawa

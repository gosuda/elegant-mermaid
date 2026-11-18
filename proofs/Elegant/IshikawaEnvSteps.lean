import Elegant.IshikawaClearanceHardA

set_option autoImplicit false

namespace Elegant.Ishikawa

/-! ### Step arithmetic behind `EnvStepOdd` and `EnvStepEven`

`ishikawa_env_invariant` consumes `EnvStepOdd` / `EnvStepEven` as premises.
Both defs quantify over arbitrary parent bones with only the listed
arithmetic hypotheses, and both are **false as stated**: the master diagonal
`envMasterX` floors a slope with denominator `r.length`, a child bone
descends by `run p (slot - par.t0)` over its own window, and the two floors
disagree by one unit at misaligned windows (`master_line_step` loses exactly
the unit the conclusions demand).

This file contains, in order:

1. `envStepOdd_false` / `envStepEven_false`: explicit Lean counterexamples
   (fully checked), showing neither def can be discharged for
   `r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns
   (cause, k))` without a stronger premise on the parent bone.
2. `envStepOdd_holds`: the odd step under the added slot-shifted alignment
   premise `par.x0 + run p (slot - par.t0) ≤ envMasterX r p slot + 2`.
3. `envStepEven_holds`: the even step under the added fdiv alignment corner
   `Int.fdiv ((-run p (par.t1 - par.t0)) * (slot - par.t0)) (par.t1 - par.t0)
   ≤ envMasterX r p slot - envMasterX r p par.t0` (exactly the corner the
   `EnvStepEven` docstring predicted). With the corner, the even step needs
   none of the master-line lemmas.
4. `envStepEven_x0_of_env`: for a diagonal parent obeying the ENV bound at
   its own end, the original `par.x0 ≤ envMasterX + 2` premise is derivable,
   so an executed non-root parent that keeps the ENV end bound satisfies the
   x0 premise automatically (the root bone satisfies it directly).

5. `envStepEven_false_flat_unit` / `envStepOdd_false_flat_unit`: the same
   counterexamples without the witness's unrepresentable fields. `envWitR`
   itself is not a generated rib (`entries = []` forces `heights = 0`, and
   a root child's cause cannot be `0`), but the falsity never touches those
   fields: every rib of positive length is refuted in the flat-unit regime
   (`run p 1 = 0`, `0 < run p r.length`; odd also pins
   `run p r.heights = 0`), which `successful_slope_parameters`
   (`0 ≤ p.cos ∧ 1 ≤ p.sin`) permits.

6. The executed counterexample `exec_*`: on the two-node tree with
   `cos = 1, sin = 2, ribMin = spineBase = 10`, the placed leaf rib
   (length 2, heights 0) refutes both step premises
   (`exec_step_even_false`, `exec_step_odd_false`). The steps are
   therefore false for reachable ribs, and the raw `EnvStepOdd` /
   `EnvStepEven` premise shapes in `ishikawa_env_invariant` are
   unsatisfiable for such runs.

7. `EnvStepOddAligned` / `EnvStepEvenAligned` with `envStepOddAligned` /
   `envStepEvenAligned`: the minimal corrected per-child premise shapes
   (one alignment hypothesis per step), proven unconditionally from
   `envStepOdd_holds` / `envStepEven_holds`. A repaired
   `ishikawa_env_invariant` must carry these shapes; since executed odd
   children violate the odd alignment (see the study below), discharging
   it for executed runs then needs the birth-chain reserve slack, not the
   aligned premise alone.

Numerical study backing the choice of added premises (Python simulation of
the exact `place` semantics, trees up to 5 nodes / depth 4, `L` to 35,
fourteen `cos`/`sin` pairs, ~41k executed rib placements):

* The ENV invariant `b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1)`
  held on every born bone of every executed run.
* The even-step corner held on every executed even child, including children
  of the root bone (whose diagonal IS the master diagonal and satisfies the
  corner with equality).
* The odd-step added premise was violated on a fraction of executed odd
  children (witness tree parents `[_,0,0,1,3]`, `cos=1, sin=2, L=8,
  heights=1`): those children attach far left of the master because the
  parent's reserved segment is longer than the reserve minimum, so no
  premise on `par.x0` alone captures every executed case. The added premises
  are therefore the weakest *arithmetic* repairs; recovering them for all
  executed parents needs the birth-chain structure that the
  `ishikawa_env_invariant` induction itself carries. -/

/-! ### Counterexample witnesses -/

private def envWitP : Params := ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 2⟩

private def envWitR : Rib := ⟨0, false, [], [], 1, 2, []⟩

private theorem envWitR_length : envWitR.length = 2 := rfl

private theorem envWitR_heights : envWitR.heights = 1 := rfl

private theorem fdiv_bounds' (a d : Int) (hd : 0 < d) :
    d * Int.fdiv a d ≤ a ∧ a < d * Int.fdiv a d + d := by
  have h := Int.mul_fdiv_add_fmod a d
  have hf := Int.fmod_nonneg_of_pos a hd
  have hlt := Int.fmod_lt_of_pos a hd
  omega

/-- A floored division is pinned by its two-sided remainder bounds. -/
private theorem fdiv_eq_of_between (a d q : Int) (hd : 0 < d)
    (h1 : d * q ≤ a) (h2 : a < d * q + d) : Int.fdiv a d = q := by
  have hb := fdiv_bounds' a d hd
  have hq : d * q < d * (Int.fdiv a d + 1) := by
    have e : d * (Int.fdiv a d + 1) = d * Int.fdiv a d + d := by
      rw [Int.mul_add, Int.mul_one]
    omega
  have hq2 : d * Int.fdiv a d < d * (q + 1) := by
    have e : d * (q + 1) = d * q + d := by rw [Int.mul_add, Int.mul_one]
    omega
  have l1 : q < Int.fdiv a d + 1 := Int.lt_of_mul_lt_mul_left hq (show 0 ≤ d by omega)
  have l2 : Int.fdiv a d < q + 1 := Int.lt_of_mul_lt_mul_left hq2 (show 0 ≤ d by omega)
  omega

/-- `run envWitP 1 = 0`: the witness profile is too flat to drop one unit
per ordinate. -/
private theorem envWit_run_one : run envWitP 1 = 0 := by
  dsimp only [run, envWitP]
  rw [Int.mul_one]
  exact fdiv_eq_of_between 1 2 0 (by omega) (by omega) (by omega)

/-- `run envWitP 2 = 1`. -/
private theorem envWit_run_two : run envWitP 2 = 1 := by
  dsimp only [run, envWitP]
  rw [Int.mul_one]
  exact fdiv_eq_of_between 2 2 1 (by omega) (by omega) (by omega)

/-- `envMasterX envWitR envWitP 0 = 0`. -/
private theorem envWit_master_zero : envMasterX envWitR envWitP 0 = 0 := by
  dsimp only [envMasterX, envWitR]
  rw [envWit_run_two, Int.mul_zero]
  exact fdiv_eq_of_between 0 2 0 (by omega) (by omega) (by omega)

/-- `envMasterX envWitR envWitP 1 = -1`: the master drops a full unit over
`[0, 1]` although `run envWitP 1 = 0`. -/
private theorem envWit_master_one : envMasterX envWitR envWitP 1 = -1 := by
  dsimp only [envMasterX, envWitR]
  rw [envWit_run_two, Int.mul_one]
  exact fdiv_eq_of_between (-1 : Int) 2 (-1) (by omega) (by omega) (by omega)

/-- `EnvStepOdd` is **false** for the witness rib: the odd child of a flat
parent attaches one margin left of the parent start, does not descend
(`run envWitP 1 = 0`), and yet the master drops a full unit over the same
window, so the child's end sits on the master instead of
`run p r.heights + 1` left of it. -/
theorem envStepOdd_false : ¬ EnvStepOdd envWitR envWitP := by
  intro step
  have h := step ⟨2, 0, -4, 0, 1, 0⟩ 0 1 1
    (by decide)
    (by rfl)
    (by dsimp only; omega)
    (by dsimp only; rw [envWitR_heights, envWit_run_one]; omega)
    (by dsimp only; omega)
    (by dsimp only; omega)
    (by decide)
    (by dsimp only; rw [envWit_master_zero]; omega)
  dsimp only at h
  obtain ⟨_, hx1⟩ := h
  rw [envWitR_heights, envWit_run_one] at hx1
  have hxe : (depthBone envWitP ⟨2, 0, -4, 0, 1, 0⟩ 1 1 ((1 : Nat) : Int) (0 + 3)).x1
      = ((2 : Int) + Int.fdiv (((-4 : Int) - 2) * ((1 : Int) - 0)) ((1 : Int) + 1))
        - run envWitP 1 := by
    have h1odd : ((1 : Nat) % 2 != 0) = true := by decide
    simp only [depthBone, h1odd, ite_true, Int.sub_zero]
  have hf : Int.fdiv (((-4 : Int) - 2) * ((1 : Int) - 0)) ((1 : Int) + 1) = -3 :=
    fdiv_eq_of_between (-6 : Int) 2 (-3) (by omega) (by omega) (by omega)
  rw [hf, envWit_run_one] at hxe
  rw [hxe] at hx1
  have ht1 : (depthBone envWitP ⟨2, 0, -4, 0, 1, 0⟩ 1 1 ((1 : Nat) : Int) (0 + 3)).t1 = 1 := rfl
  rw [ht1, envWit_master_one] at hx1
  omega

/-- `EnvStepEven` is **false** for the witness rib: a diagonal parent whose
window has `run envWitP 1 = 0` stays flat while the master drops a unit, so
the interpolated child sits two units above the master end bound. -/
theorem envStepEven_false : ¬ EnvStepEven envWitR envWitP := by
  intro step
  have h := step ⟨2, 0, 2, 1, 0, 0⟩ 1 0
    (by decide)
    (by dsimp only; omega)
    (by dsimp only; rw [Int.sub_zero, envWit_run_one]; omega)
    (by dsimp only; omega)
    (by dsimp only; omega)
    (by dsimp only; rw [envWit_master_zero]; omega)
  dsimp only at h
  obtain ⟨hx0, _⟩ := h
  rw [envWitR_heights, envWit_run_one, Int.zero_add] at hx0
  have hxe : (depthBone envWitP ⟨2, 0, 2, 1, 0, 0⟩ 2 1 ((0 : Nat) : Int) 3).x0
      = (2 : Int) + Int.fdiv (((2 : Int) - 2) * ((1 : Int) - 0)) ((1 : Int) - 0) := by
    have h2even : ((2 : Nat) % 2 != 0) = false := by decide
    simp only [depthBone, h2even, Bool.false_eq_true, ite_false]
  have hf0 : Int.fdiv (((2 : Int) - 2) * ((1 : Int) - 0)) ((1 : Int) - 0) = 0 := by
    simpa only [Int.sub_self, Int.sub_zero, Int.zero_mul] using
      fdiv_eq_of_between 0 1 0 (by omega) (by omega) (by omega)
  rw [hf0] at hxe
  rw [hxe] at hx0
  have ht0 : (depthBone envWitP ⟨2, 0, 2, 1, 0, 0⟩ 2 1 ((0 : Nat) : Int) 3).t0 = 1 := rfl
  rw [ht0, envWit_master_one] at hx0
  omega

/-! ### Strengthened step facts -/

section StepHelpers

/-- `run` is nonnegative on a nonnegative rise. -/
private theorem run_nonneg' (p : Params) (x : Int) (hx : 0 ≤ x) (hcos : 0 ≤ p.cos)
    (hsin : 0 < p.sin) : 0 ≤ run p x := by
  dsimp only [run]
  exact Int.fdiv_nonneg (Int.mul_nonneg hx hcos) (Int.le_of_lt hsin)

/-- Copied from `IshikawaClearanceFacts.attachment_start_margin` (private
there and in `IshikawaClearanceHard`): with a full reserve between the ends
and at least one draw left, the interpolated attachment is a full margin
left of the parent start. -/
private theorem attach_margin' (left right count drawn margin : Int)
    (hden : 0 < count + 1) (hmargin : 0 ≤ margin)
    (hreserve : (count + 1) * margin ≤ left - right)
    (hrank : 1 ≤ count - drawn) :
    left + Int.fdiv ((right - left) * (count - drawn)) (count + 1) ≤ left - margin := by
  have hspan : 0 ≤ left - right :=
    Int.le_trans (Int.mul_nonneg (Int.le_of_lt hden) hmargin) hreserve
  have hmul := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ count - drawn by omega) hspan
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

end StepHelpers

/-- Odd-step arithmetic under the added slot-shifted alignment premise.
This is the weakest repair that constrains only `par.x0`: the child bone
descends `run p (slot - par.t0)` over its own window, so the parent start
must be within two of the master measured at the child's slot through that
descent. Without it the step is false (`envStepOdd_false`). -/
theorem envStepOdd_holds (r : Rib) (p : Params)
    (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin) (hH : 0 ≤ r.heights)
    (par : Bone) (drawn slot : Int) (count : Nat)
    (hcount : 0 < par.count + 1)
    (hreserve : (par.count + 1) * (run p r.heights + 3) ≤ par.x0 - par.x1)
    (hrank : drawn + 1 ≤ par.count)
    (hslot : par.t0 ≤ slot)
    (hx0 : par.x0 ≤ envMasterX r p par.t0 + 2)
    (hshift : par.x0 + run p (slot - par.t0) ≤ envMasterX r p slot + 2) :
    let b := depthBone p { par with drawn := drawn } 1 slot count (run p r.heights + 3)
    b.x0 ≤ envMasterX r p b.t0 + 2 ∧
    b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1) := by
  dsimp only
  have hmargin : 0 ≤ run p r.heights + 3 := by
    have := run_nonneg' p r.heights hH hcos hsin
    omega
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
  -- the interpolated attachment numerator is nonpositive
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
  rw [hx0b]
  refine ⟨?_, ?_⟩
  · rw [ht0]
    have hle : par.x0 + Int.fdiv ((par.x1 - par.x0) * (par.count - drawn)) (par.count + 1) ≤
        par.x0 := by omega
    omega
  · have ham := attach_margin' par.x0 par.x1 par.count drawn (run p r.heights + 3)
      hcount hmargin hreserve (show 1 ≤ par.count - drawn by omega)
    have hw : 0 ≤ run p (slot - par.t0) :=
      run_nonneg' p (slot - par.t0) (by omega) hcos hsin
    rw [hx1b, ht1]
    have h2 : par.x0 + Int.fdiv ((par.x1 - par.x0) * (par.count - drawn)) (par.count + 1) ≤
        par.x0 - (run p r.heights + 3) := ham
    omega

/-- Even-step arithmetic under the added fdiv alignment corner (the corner
named in the `EnvStepEven` docstring). With the corner premise the even step
needs no master-line lemma at all: the parent's floored interpolation
dominates the master's floored descent over the same window, so the child
attaches within two of the master and its reserved end keeps the ENV
margin. -/
theorem envStepEven_holds (r : Rib) (p : Params)
    (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin) (hH : 0 ≤ r.heights)
    (par : Bone) (slot : Int) (count : Nat)
    (hroute : par.x1 = par.x0 - run p (par.t1 - par.t0))
    (hx0 : par.x0 ≤ envMasterX r p par.t0 + 2)
    (hcorner : Int.fdiv ((-run p (par.t1 - par.t0)) * (slot - par.t0))
        (par.t1 - par.t0) ≤ envMasterX r p slot - envMasterX r p par.t0) :
    let b := depthBone p par 2 slot count (run p r.heights + 3)
    b.x0 ≤ envMasterX r p b.t0 + 2 ∧
    b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1) := by
  dsimp only
  have hmargin : 0 ≤ run p r.heights + 3 := by
    have := run_nonneg' p r.heights hH hcos hsin
    omega
  have hb := depthBone_even_endpoints p par 2 slot count (run p r.heights + 3)
    (by decide : (2 : Nat) % 2 = 0)
  obtain ⟨ht0, ht1, hx1e⟩ := hb
  have h2even : ((2 : Nat) % 2 != 0) = false := by decide
  have hx0e : (depthBone p par 2 slot count (run p r.heights + 3)).x0 =
      par.x0 + Int.fdiv ((par.x1 - par.x0) * (slot - par.t0)) (par.t1 - par.t0) := by
    simp only [depthBone, h2even, Bool.false_eq_true, ite_false]
  have hnum : (par.x1 - par.x0) * (slot - par.t0) =
      -((run p (par.t1 - par.t0)) * (slot - par.t0)) := by
    rw [show par.x1 - par.x0 = -(run p (par.t1 - par.t0)) from by omega, Int.neg_mul]
  rw [hnum] at hx0e
  rw [Int.neg_mul] at hcorner
  rw [hx0e, ht0]
  refine ⟨?_, ?_⟩
  · omega
  · rw [hx1e, ht1]
    have hbone : ((count : Int) + 1) * (run p r.heights + 3) ≤
        boneLength p count (run p r.heights + 3) := Int.le_max_right _ _
    have hge : (run p r.heights + 3) ≤ ((count : Int) + 1) * (run p r.heights + 3) := by
      have h1 := Int.mul_le_mul_of_nonneg_right
        (show (1 : Int) ≤ (count : Int) + 1 from by omega)
        (show (0 : Int) ≤ run p r.heights + 3 from by omega)
      simpa only [Int.one_mul] using h1
    omega

/-- For a diagonal parent that keeps the ENV bound at its own end, the
original even-step x0 premise is derivable from the master-line lower
bound: the parent start is within `1 - run p r.heights` of the master, hence
within two. This is the premise-transfer fact an executed non-root parent
needs; the root bone satisfies the x0 premise directly (`par.x0 = 0`,
`envMasterX r p 0 = 0`). -/
theorem envStepEven_x0_of_env (r : Rib) (p : Params)
    (hL : 0 < r.length) (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin) (hH : 0 ≤ r.heights)
    (par : Bone)
    (hroute : par.x1 = par.x0 - run p (par.t1 - par.t0))
    (hspan0 : 0 ≤ par.t1 - par.t0) (hspanL : par.t1 - par.t0 ≤ r.length)
    (hP2 : par.x1 ≤ envMasterX r p par.t1 - (run p r.heights + 1)) :
    par.x0 ≤ envMasterX r p par.t0 + 2 := by
  dsimp only [envMasterX] at hP2 ⊢
  have hm := master_line_step p r.length par.t0 (par.t1 - par.t0)
    hL hcos hsin hspan0 hspanL
  obtain ⟨hml, _⟩ := hm
  have heq : par.t0 + (par.t1 - par.t0) = par.t1 := by omega
  rw [heq] at hml
  have hrn : 0 ≤ run p r.heights := run_nonneg' p r.heights hH hcos hsin
  have hx0 : par.x0 = par.x1 + run p (par.t1 - par.t0) := by omega
  omega

/-! ### Reachability of the witness and the executed counterexample

`envWitR` itself is not a generated rib: `generatedRib` computes `heights`
as the fold maximum over `entries`, so empty `entries` force
`heights = 0`, and a generated rib's cause is a child of node 0, which
excludes `cause = 0` (node 0 is the root and cannot parent itself). The
falsity, however, never touches those unrepresentable fields: the two
`*_false_flat_unit` theorems refute `EnvStepEven` / `EnvStepOdd` for
*every* rib with a positive length once `run p 1 = 0` and
`0 < run p r.length` (odd additionally pins `run p r.heights = 0`), and
`successful_slope_parameters` permits exactly such profiles
(`0 ≤ p.cos ∧ 1 ≤ p.sin` admits `cos = 1, sin = 2`). The instance below
executes the real pipeline on a two-node tree: rib generation, side-length
measurement, `place`, and `assemblePairs` all succeed, yet both step
premises are false for the placed input. -/

/-- `envMasterX r p 0 = 0` for any positive rib length. -/
private theorem envMasterX_zero (r : Rib) (p : Params) (hL : 0 < r.length) :
    envMasterX r p 0 = 0 := by
  dsimp only [envMasterX]
  rw [Int.mul_zero]
  exact fdiv_eq_of_between 0 r.length 0 hL (by omega) (by omega)

/-- General form of `envStepEven_false`: the counterexample parent needs
nothing from `r.entries`. Any rib of positive length is refuted once the
slope is flat per ordinate (`run p 1 = 0`) while the master still drops
over the full rib (`0 < run p r.length`) — the floor misalignment of a
reachable placed rib. -/
theorem envStepEven_false_flat_unit (r : Rib) (p : Params)
    (hL : 0 < r.length) (hflat : run p 1 = 0) (hdrop : 0 < run p r.length) :
    ¬ EnvStepEven r p := by
  intro step
  have h := step ⟨2, 0, 2, 1, 0, 0⟩ 1 0
    hL
    (by dsimp only; omega)
    (by dsimp only; rw [Int.sub_zero, hflat]; omega)
    (by dsimp only; omega)
    (by dsimp only; omega)
    (by dsimp only; rw [envMasterX_zero r p hL]; omega)
  dsimp only at h
  obtain ⟨hx0, _⟩ := h
  have hxe : (depthBone p ⟨2, 0, 2, 1, 0, 0⟩ 2 1 ((0 : Nat) : Int) (run p r.heights + 3)).x0
      = (2 : Int) + Int.fdiv (((2 : Int) - 2) * ((1 : Int) - 0)) ((1 : Int) - 0) := by
    have h2even : ((2 : Nat) % 2 != 0) = false := by decide
    simp only [depthBone, h2even, Bool.false_eq_true, ite_false]
  have hf0 : Int.fdiv (((2 : Int) - 2) * ((1 : Int) - 0)) ((1 : Int) - 0) = 0 := by
    simpa only [Int.sub_self, Int.sub_zero, Int.zero_mul] using
      fdiv_eq_of_between 0 1 0 (by omega) (by omega) (by omega)
  rw [hf0] at hxe
  rw [hxe] at hx0
  have ht0 : (depthBone p ⟨2, 0, 2, 1, 0, 0⟩ 2 1 ((0 : Nat) : Int) (run p r.heights + 3)).t0
      = 1 := rfl
  rw [ht0] at hx0
  dsimp only [envMasterX] at hx0
  rw [Int.mul_one] at hx0
  have hb := fdiv_bounds' (-(run p r.length)) r.length hL
  have hpos : (0 : Int) ≤ Int.fdiv (-(run p r.length)) r.length := by omega
  have hnonneg : (0 : Int) ≤ r.length * Int.fdiv (-(run p r.length)) r.length :=
    Int.mul_nonneg (by omega) hpos
  exact absurd hb.1 (by omega)

/-- General form of `envStepOdd_false`: a horizontal parent that keeps the
master bound exactly at its start and reserves exactly the minimum sends
its odd child one margin left; with a flat unit slope the child does not
descend while the master drops at least one unit over the window, so the
reserved end sits on the master instead of `run p r.heights + 1` left of
it. Needs no field of `r.entries`. -/
theorem envStepOdd_false_flat_unit (r : Rib) (p : Params)
    (hL : 2 ≤ r.length) (hflat : run p 1 = 0) (hheights : run p r.heights = 0)
    (hdrop : 0 < run p r.length) :
    ¬ EnvStepOdd r p := by
  intro step
  have h := step ⟨2, 0, -4, 0, 1, 0⟩ 0 1 1
    (by omega)
    (by rfl)
    (by dsimp only; omega)
    (by dsimp only; rw [hheights]; omega)
    (by dsimp only; omega)
    (by dsimp only; omega)
    (by omega)
    (by dsimp only; rw [envMasterX_zero r p (by omega)]; omega)
  dsimp only at h
  obtain ⟨_, hx1⟩ := h
  have hxe : (depthBone p ⟨2, 0, -4, 0, 1, 0⟩ 1 1 ((1 : Nat) : Int) (run p r.heights + 3)).x1
      = ((2 : Int) + Int.fdiv (((-4 : Int) - 2) * ((1 : Int) - 0)) ((1 : Int) + 1))
        - run p 1 := by
    have h1odd : ((1 : Nat) % 2 != 0) = true := by decide
    simp only [depthBone, h1odd, ite_true, Int.sub_zero]
  have hf : Int.fdiv (((-4 : Int) - 2) * ((1 : Int) - 0)) ((1 : Int) + 1) = -3 :=
    fdiv_eq_of_between (-6 : Int) 2 (-3) (by omega) (by omega) (by omega)
  rw [hf, hflat] at hxe
  rw [hxe] at hx1
  have ht1 : (depthBone p ⟨2, 0, -4, 0, 1, 0⟩ 1 1 ((1 : Nat) : Int) (run p r.heights + 3)).t1
      = 1 := rfl
  rw [ht1] at hx1
  dsimp only [envMasterX] at hx1
  rw [Int.mul_one, hheights] at hx1
  have hb := fdiv_bounds' (-(run p r.length)) r.length (by omega)
  have hpos : (0 : Int) ≤ Int.fdiv (-(run p r.length)) r.length := by omega
  have hnonneg : (0 : Int) ≤ r.length * Int.fdiv (-(run p r.length)) r.length :=
    Int.mul_nonneg (by omega) hpos
  exact absurd hb.1 (by omega)

/-! ### The executed counterexample

A two-node tree, the valid profile `cos = 1, sin = 2` with
`ribMin = spineBase = 10`: `layout` succeeds, and the placed input of the
sole generated rib (a leaf cause, so `entries = []` and `heights = 0`,
with measured length `10` halved to `2` for the leaf) refutes both step
premises. This is the executed counterexample showing the steps are false
for reachable ribs, not only for the artificial witness rib. -/

private def execP : Params := ⟨10, 10, 1, 1, 1, 1, 0, 0, 1, 2⟩

private def execNs : List Tree.Node := [⟨none, 1, 1⟩, ⟨some 0, 1, 1⟩]

/-- The generated ribs of the executed instance: a single leaf-cause rib. -/
private def execRibs : List Rib := (children execNs 0).zipIdx.map (generatedRib execNs)

/-- The placed input of the executed instance. -/
private def execInput : Rib :=
  effectivePlacedInput execNs (measuredSideLength execP execRibs) (generatedRib execNs (1, 0))

private theorem exec_length : execInput.length = 2 := by rfl

private theorem exec_heights : execInput.heights = 0 := by rfl

private theorem exec_run_one : run execP 1 = 0 := by
  dsimp only [run, execP]
  rw [Int.mul_one]
  exact fdiv_eq_of_between 1 2 0 (by omega) (by omega) (by omega)

private theorem exec_run_two : run execP 2 = 1 := by
  dsimp only [run, execP]
  rw [Int.mul_one]
  exact fdiv_eq_of_between 2 2 1 (by omega) (by omega) (by omega)

private theorem exec_run_zero : run execP 0 = 0 := by
  dsimp only [run, execP]
  rw [Int.zero_mul]
  exact fdiv_eq_of_between 0 2 0 (by omega) (by omega) (by omega)

/-- Node 1 is the sole root child of the instance. -/
private theorem exec_cause : 1 ∈ children execNs 0 := by decide

/-- The generated singleton rib list, matching `ishikawa_env_invariant`'s
`hg`/`hrib` premises. -/
private theorem exec_rib : generatedRib execNs (1, 0) ∈ execRibs := by
  have hr : execRibs = [generatedRib execNs (1, 0)] := rfl
  rw [hr]
  simp


/-- Executed falsity of the even step premise on the placed input. -/
theorem exec_step_even_false : ¬ EnvStepEven execInput execP :=
  envStepEven_false_flat_unit execInput execP
    (by rw [exec_length]; omega)
    exec_run_one
    (by rw [exec_length, exec_run_two]; omega)

/-- Executed falsity of the odd step premise on the placed input. -/
theorem exec_step_odd_false : ¬ EnvStepOdd execInput execP :=
  envStepOdd_false_flat_unit execInput execP
    (by rw [exec_length]; omega)
    exec_run_one
    (by rw [exec_heights]; exact exec_run_zero)
    (by rw [exec_length, exec_run_two]; omega)

/-! ### Minimal corrected invariant: the aligned step premises

Because the raw `EnvStepOdd` / `EnvStepEven` are false for reachable placed
ribs (`exec_step_odd_false`, `exec_step_even_false`),
`ishikawa_env_invariant` cannot carry them at face value. The minimal
corrected per-child premise shapes add exactly one alignment hypothesis per
step, and with it each step holds for every parent. These are the shapes a
repaired `ishikawa_env_invariant` must carry; per the numerical study in
the file header, the odd alignment is violated on a fraction of executed
odd children, so discharging it for executed runs then needs the
birth-chain reserve slack, not the aligned premise alone. -/

/-- Corrected odd step: the parent start shifted by the child's own descent
to the child's slot stays within two of the master at that slot. -/
def EnvStepOddAligned (r : Rib) (p : Params) : Prop :=
  ∀ (par : Bone) (drawn slot : Int) (count : Nat),
    0 < par.count + 1 →
    (par.count + 1) * (run p r.heights + 3) ≤ par.x0 - par.x1 →
    drawn + 1 ≤ par.count → par.t0 ≤ slot →
    par.x0 ≤ envMasterX r p par.t0 + 2 →
    par.x0 + run p (slot - par.t0) ≤ envMasterX r p slot + 2 →
    let b := depthBone p { par with drawn := drawn } 1 slot count (run p r.heights + 3)
    b.x0 ≤ envMasterX r p b.t0 + 2 ∧
    b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1)

/-- Corrected even step: the parent's floored interpolation over its own
window dominates the master's floored descent (the fdiv corner). -/
def EnvStepEvenAligned (r : Rib) (p : Params) : Prop :=
  ∀ (par : Bone) (slot : Int) (count : Nat),
    par.x1 = par.x0 - run p (par.t1 - par.t0) →
    par.x0 ≤ envMasterX r p par.t0 + 2 →
    Int.fdiv ((-run p (par.t1 - par.t0)) * (slot - par.t0)) (par.t1 - par.t0)
      ≤ envMasterX r p slot - envMasterX r p par.t0 →
    let b := depthBone p par 2 slot count (run p r.heights + 3)
    b.x0 ≤ envMasterX r p b.t0 + 2 ∧
    b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1)

/-- The corrected odd step holds unconditionally per parent, given the
slope profile and nonnegative rib heights. -/
theorem envStepOddAligned (r : Rib) (p : Params)
    (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin) (hH : 0 ≤ r.heights) :
    EnvStepOddAligned r p := by
  intro par drawn slot count hcount hreserve hrank hslot hx0 hshift
  exact envStepOdd_holds r p hcos hsin hH par drawn slot count hcount hreserve
    hrank hslot hx0 hshift

/-- The corrected even step holds unconditionally per parent, given the
slope profile and nonnegative rib heights. -/
theorem envStepEvenAligned (r : Rib) (p : Params)
    (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin) (hH : 0 ≤ r.heights) :
    EnvStepEvenAligned r p := by
  intro par slot count hroute hx0 hcorner
  exact envStepEven_holds r p hcos hsin hH par slot count hroute hx0 hcorner

end Elegant.Ishikawa

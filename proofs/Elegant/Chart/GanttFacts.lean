import Elegant.Chart.GanttLayout
import Elegant.Model
import Elegant.Kinds.Gantt

set_option autoImplicit false

namespace Elegant.Chart.Gantt

theorem civilDate_ext (a b : CivilDate)
    (hy : a.year = b.year) (hm : a.month = b.month) (hd : a.day = b.day) : a = b := by
  cases a
  cases b
  simp only [CivilDate.mk.injEq] at *
  exact ⟨hy, hm, hd⟩

theorem civil_era_remainder (year : Int) :
    0 ≤ year - Int.fdiv year 400 * 400 ∧
      year - Int.fdiv year 400 * 400 < 400 := by
  have h := Int.mul_fdiv_add_fmod year 400
  have h0 := Int.fmod_nonneg_of_pos year (show (0 : Int) < 400 by decide)
  have h1 := Int.fmod_lt_of_pos year (show (0 : Int) < 400 by decide)
  omega

theorem civil_year_prefix_bounds (year : Int) (h0 : 0 ≤ year) (h1 : year < 400) :
    0 ≤ year * 365 + Int.fdiv year 4 - Int.fdiv year 100 ∧
      year * 365 + Int.fdiv year 4 - Int.fdiv year 100 ≤ 145731 := by
  simp [Int.fdiv_eq_ediv]
  omega

theorem civil_month_prefix_bounds (month : Int) (h0 : 0 ≤ month) (h1 : month < 12) :
    0 ≤ Int.fdiv (153 * month + 2) 5 ∧
      Int.fdiv (153 * month + 2) 5 ≤ 337 := by
  simp [Int.fdiv_eq_ediv]
  omega

theorem civil_day_of_era_bounds (year month day : Int)
    (hy0 : 0 ≤ year) (hy1 : year < 400)
    (hm0 : 0 ≤ month) (hm1 : month < 12) (hd0 : 1 ≤ day) (hd1 : day ≤ 31) :
    0 ≤ year * 365 + Int.fdiv year 4 - Int.fdiv year 100 +
      Int.fdiv (153 * month + 2) 5 + day - 1 ∧
    year * 365 + Int.fdiv year 4 - Int.fdiv year 100 +
      Int.fdiv (153 * month + 2) 5 + day - 1 ≤ 146098 := by
  have hy := civil_year_prefix_bounds year hy0 hy1
  have hm := civil_month_prefix_bounds month hm0 hm1
  omega

theorem civil_era_quotient (era dayOfEra : Int)
    (h0 : 0 ≤ dayOfEra) (h1 : dayOfEra < 146097) :
    Int.fdiv (era * 146097 + dayOfEra) 146097 = era := by
  have h := Int.mul_fdiv_add_fmod (era * 146097 + dayOfEra) 146097
  have h0' := Int.fmod_nonneg_of_pos (era * 146097 + dayOfEra)
    (show (0 : Int) < 146097 by decide)
  have h1' := Int.fmod_lt_of_pos (era * 146097 + dayOfEra)
    (show (0 : Int) < 146097 by decide)
  omega

theorem civil_era_residue (era dayOfEra : Int)
    (h0 : 0 ≤ dayOfEra) (h1 : dayOfEra < 146097) :
    era * 146097 + dayOfEra -
      Int.fdiv (era * 146097 + dayOfEra) 146097 * 146097 = dayOfEra := by
  rw [civil_era_quotient era dayOfEra h0 h1]
  omega

theorem civil_month_inverse (month day : Int)
    (_hm0 : 0 ≤ month) (_hm1 : month < 12)
    (hd0 : 0 ≤ day) (hd1 : day < 28) :
    Int.fdiv (5 * (Int.fdiv (153 * month + 2) 5 + day) + 2) 153 = month := by
  simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 5 by decide),
    Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 153 by decide)]
  omega

theorem civil_valid_shifted_doy_bounds (y m d : Int)
    (h : (CivilDate.mk y m d).valid) :
    0 ≤ Int.fdiv (153 * (if m > 2 then m - 3 else m + 9) + 2) 5 + d - 1 ∧
    Int.fdiv (153 * (if m > 2 then m - 3 else m + 9) + 2) 5 + d - 1 ≤ 365 := by
  rcases h with ⟨hm0, hm1, hd0, hd1⟩
  dsimp only at hm0 hm1 hd0 hd1
  by_cases hFeb : m = 2
  · subst m
    simp only [daysInMonth, ite_true] at hd1
    have hd29 : d ≤ 29 := by
      split at hd1 <;> omega
    simp only [show ¬ ((2 : Int) > 2) by omega, ite_false, Int.fdiv_eq_ediv]
    omega
  · have hd31 : d ≤ 31 := by
      simp only [daysInMonth, hFeb, ite_false] at hd1
      split at hd1 <;> omega
    by_cases hAfter : m > 2
    · simp only [hAfter, ite_true, Int.fdiv_eq_ediv]
      omega
    · have hJan : m = 1 := by omega
      subst m
      simp only [show ¬ ((1 : Int) > 2) by omega, ite_false, Int.fdiv_eq_ediv]
      omega

theorem civil_valid_doe_bounds (date : CivilDate) (h : date.valid) :
    let y := if date.month ≤ 2 then date.year - 1 else date.year
    let r := y - Int.fdiv y 400 * 400
    let p := if date.month > 2 then date.month - 3 else date.month + 9
    0 ≤ r * 365 + Int.fdiv r 4 - Int.fdiv r 100 +
      Int.fdiv (153 * p + 2) 5 + date.day - 1 ∧
    r * 365 + Int.fdiv r 4 - Int.fdiv r 100 +
      Int.fdiv (153 * p + 2) 5 + date.day - 1 < 146097 := by
  dsimp only
  have hr := civil_era_remainder
    (if date.month ≤ 2 then date.year - 1 else date.year)
  have hp := civil_year_prefix_bounds
    ((if date.month ≤ 2 then date.year - 1 else date.year) -
      Int.fdiv (if date.month ≤ 2 then date.year - 1 else date.year) 400 * 400)
    hr.1 hr.2
  have hd := civil_valid_shifted_doy_bounds date.year date.month date.day h
  omega
def decodeYearOfEra (dayOfEra : Int) : Int :=
  Int.fdiv (dayOfEra - Int.fdiv dayOfEra 1460 +
    Int.fdiv dayOfEra 36524 - Int.fdiv dayOfEra 146096) 365

set_option maxHeartbeats 2000000 in
theorem civil_decode_year_of_era (year doy : Int)
    (hy0 : 0 ≤ year) (hy1 : year < 400) (hd0 : 0 ≤ doy)
    (hd1 : doy ≤ 364 + (if Int.fmod (year + 1) 4 = 0 ∧
      (Int.fmod (year + 1) 100 ≠ 0 ∨ Int.fmod (year + 1) 400 = 0) then 1 else 0)) :
    decodeYearOfEra (year * 365 + Int.fdiv year 4 - Int.fdiv year 100 + doy) = year := by
  let doe := year * 365 + Int.fdiv year 4 - Int.fdiv year 100 + doy
  have hdoe : 0 ≤ doe ∧ doe < 146097 := by
    have hp := civil_year_prefix_bounds year hy0 hy1
    dsimp only [doe]
    split at hd1 <;> omega
  have corrected :
      year * 365 ≤ doe - Int.fdiv doe 1460 +
        Int.fdiv doe 36524 - Int.fdiv doe 146096 ∧
      doe - Int.fdiv doe 1460 + Int.fdiv doe 36524 -
        Int.fdiv doe 146096 < (year + 1) * 365 := by
    dsimp only [doe] at *
    simp [Int.fdiv_eq_ediv, Int.fmod_eq_emod] at *
    have remainder : year % 4 = 0 ∨ year % 4 = 1 ∨
        year % 4 = 2 ∨ year % 4 = 3 := by omega
    have century : year / 100 = 0 ∨ year / 100 = 1 ∨
        year / 100 = 2 ∨ year / 100 = 3 := by omega
    have hfour : doe / 1460 = year / 4 ∨ doe / 1460 = year / 4 + 1 := by
      dsimp only [doe]
      simp [Int.fdiv_eq_ediv]
      omega
    have hcentury : doe / 36524 = year / 100 ∨
        doe / 36524 = year / 100 + 1 := by
      dsimp only [doe]
      simp [Int.fdiv_eq_ediv]
      omega
    have hlast : doe / 146096 = 0 ∨ doe / 146096 = 1 := by
      dsimp only [doe]
      simp [Int.fdiv_eq_ediv]
      omega
    dsimp only [doe] at hfour hcentury hlast
    simp [Int.fdiv_eq_ediv] at hfour hcentury hlast
    rcases remainder with hr | hr | hr | hr <;>
      rcases century with hc | hc | hc | hc <;>
      rcases hfour with hfour | hfour <;>
      rcases hcentury with hcentury | hcentury <;>
      rcases hlast with hlast | hlast
    all_goals split at hd1 <;> omega
  change Int.fdiv (doe - Int.fdiv doe 1460 +
    Int.fdiv doe 36524 - Int.fdiv doe 146096) 365 = year
  simp [Int.fdiv_eq_ediv] at corrected ⊢
  omega


theorem civil_valid_month_inverse (date : CivilDate) (h : date.valid) :
    let shifted := if date.month > 2 then date.month - 3 else date.month + 9
    Int.fdiv (5 * (Int.fdiv (153 * shifted + 2) 5 + date.day - 1) + 2) 153 =
      shifted := by
  rcases date with ⟨year, month, day⟩
  rcases h with ⟨hm0, hm1, hd0, hd1⟩
  dsimp only at hm0 hm1 hd0 hd1
  have months : month = 1 ∨ month = 2 ∨ month = 3 ∨ month = 4 ∨
      month = 5 ∨ month = 6 ∨ month = 7 ∨ month = 8 ∨ month = 9 ∨
      month = 10 ∨ month = 11 ∨ month = 12 := by omega
  rcases months with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
  all_goals
    subst month
    simp [daysInMonth, Int.fdiv_eq_ediv] at hd1 ⊢
    repeat first | split at hd1
    all_goals omega

theorem gantt_civil_roundtrip (date : CivilDate) (h : date.valid) :
    civilFromDays (daysFromCivil date) = date := by
  let y := if date.month ≤ 2 then date.year - 1 else date.year
  let era := Int.fdiv y 400
  let r := y - era * 400
  let shifted := if date.month > 2 then date.month - 3 else date.month + 9
  let doy := Int.fdiv (153 * shifted + 2) 5 + date.day - 1
  let doe := r * 365 + Int.fdiv r 4 - Int.fdiv r 100 + doy
  have bounds : 0 ≤ doe ∧ doe < 146097 := by
    have hb := civil_valid_doe_bounds date h
    dsimp only at hb
    dsimp only [doe, doy, shifted, r, era, y]
    omega
  have hr : 0 ≤ r ∧ r < 400 := civil_era_remainder y
  have hd0 : 0 ≤ doy := (civil_valid_shifted_doy_bounds
    date.year date.month date.day h).1
  have hd1 : doy ≤ 364 + (if Int.fmod (r + 1) 4 = 0 ∧
      (Int.fmod (r + 1) 100 ≠ 0 ∨ Int.fmod (r + 1) 400 = 0) then 1 else 0) := by
    rcases h with ⟨hm0, hm1, hday0, hday1⟩
    clear bounds hr hd0
    have months : date.month = 1 ∨ date.month = 2 ∨ date.month = 3 ∨
        date.month = 4 ∨ date.month = 5 ∨ date.month = 6 ∨ date.month = 7 ∨
        date.month = 8 ∨ date.month = 9 ∨ date.month = 10 ∨
        date.month = 11 ∨ date.month = 12 := by omega
    rcases months with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
    all_goals
      simp [doy, shifted, r, era, y, hm, daysInMonth, isLeap,
        Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Bool.or_eq_true,
        Int.fdiv_eq_ediv, Int.fmod_eq_emod] at *
      repeat first | split at hday1 | split
      all_goals omega
  have decoded : decodeYearOfEra doe = r :=
    civil_decode_year_of_era r doy hr.1 hr.2 hd0 hd1
  have encoded : daysFromCivil date + 719468 = era * 146097 + doe := by
    change era * 146097 + doe - 719468 + 719468 = era * 146097 + doe
    omega
  have he := civil_era_quotient era doe bounds.1 bounds.2
  unfold civilFromDays
  rw [encoded]
  dsimp only
  rw [he]
  have residue : era * 146097 + doe - era * 146097 = doe := by omega
  rw [residue]
  have decoded' : Int.fdiv (doe - Int.fdiv doe 1460 +
      Int.fdiv doe 36524 - Int.fdiv doe 146096) 365 = r := decoded
  rw [decoded']
  have dayResidue : doe - (365 * r + Int.fdiv r 4 - Int.fdiv r 100) = doy := by
    dsimp only [doe]
    omega
  rw [dayResidue]
  have monthDecoded : Int.fdiv (5 * doy + 2) 153 = shifted :=
    civil_valid_month_inverse date h
  rw [monthDecoded]
  have unshift :
      (if shifted ≥ 10 then shifted - 9 else shifted + 3) = date.month := by
    have hm0 := h.1
    have hm1 := h.2.1
    dsimp only [shifted]
    repeat first | split
    all_goals omega
  have adjusted : r + era * 400 = y := by
    dsimp only [r]
    omega
  apply civilDate_ext
  · change (if (if shifted ≥ 10 then shifted - 9 else shifted + 3) ≤ 2
        then r + era * 400 + 1 else r + era * 400) = date.year
    rw [unshift, adjusted]
    dsimp only [y]
    split <;> omega
  · exact unshift
  · change doy - Int.fdiv (153 * shifted + 2) 5 + 1 = date.day
    dsimp only [doy]
    omega

def civilYearPrefix (year : Int) : Int :=
  year * 365 + Int.fdiv year 4 - Int.fdiv year 100 + Int.fdiv year 400

theorem civil_era_prefix (year : Int) :
    let era := Int.fdiv year 400
    let r := year - era * 400
    era * 146097 + r * 365 + Int.fdiv r 4 - Int.fdiv r 100 =
      civilYearPrefix year := by
  dsimp only [civilYearPrefix]
  simp [Int.fdiv_eq_ediv]
  omega

theorem civil_days_normal_form (date : CivilDate) :
    daysFromCivil date =
      civilYearPrefix (if date.month ≤ 2 then date.year - 1 else date.year) +
        Int.fdiv (153 * (if date.month > 2 then date.month - 3 else date.month + 9) + 2) 5 +
        date.day - 1 - 719468 := by
  have hp := civil_era_prefix (if date.month ≤ 2 then date.year - 1 else date.year)
  dsimp only at hp
  unfold daysFromCivil
  dsimp only
  omega

theorem civil_year_prefix_step (year : Int) :
    civilYearPrefix (year + 1) = civilYearPrefix year + 365 +
      (if isLeap (year + 1) then 1 else 0) := by
  simp [civilYearPrefix, isLeap, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, Int.fdiv_eq_ediv, Int.fmod_eq_emod]
  split <;> omega

theorem civil_year_prefix_add_nonneg (year : Int) (n : Nat) :
    civilYearPrefix year ≤ civilYearPrefix (year + (n : Int)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := civil_year_prefix_step (year + (n : Int))
    have hn : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    rw [hn]
    have he : year + ((n : Int) + 1) = year + (n : Int) + 1 := by omega
    rw [he]
    split at hs <;> omega

theorem civil_year_prefix_monotone (first last : Int) (h : first ≤ last) :
    civilYearPrefix first ≤ civilYearPrefix last := by
  have hn : first + ((last - first).toNat : Int) = last := by omega
  have hm := civil_year_prefix_add_nonneg first (last - first).toNat
  rw [hn] at hm
  exact hm

def civilYearStart (year : Int) : Int := civilYearPrefix (year - 1) + 306 - 719468

theorem civil_date_year_bounds (date : CivilDate) (h : date.valid) :
    civilYearStart date.year ≤ daysFromCivil date ∧
      daysFromCivil date < civilYearStart (date.year + 1) := by
  rcases h with ⟨hm0, hm1, hd0, hd1⟩
  have hd31 : date.day ≤ 31 := by
    unfold daysInMonth at hd1
    repeat first | split at hd1
    all_goals omega
  have hs := civil_year_prefix_step (date.year - 1)
  have hy : date.year - 1 + 1 = date.year := by omega
  rw [hy] at hs
  simp only [civil_days_normal_form]
  unfold civilYearStart
  have hAfter : (date.month > 2) ↔ ¬ (date.month ≤ 2) := by omega
  by_cases hEarly : date.month ≤ 2
  all_goals
    simp [hEarly, hAfter, Int.fdiv_eq_ediv] at hs ⊢
    repeat first | split at hs
    all_goals omega

def CivilDate.before (a b : CivilDate) : Prop :=
  a.year < b.year ∨
    (a.year = b.year ∧ (a.month < b.month ∨ (a.month = b.month ∧ a.day < b.day)))

theorem civil_same_month_day_order (year month first last : Int) (h : first < last) :
    daysFromCivil ⟨year, month, first⟩ < daysFromCivil ⟨year, month, last⟩ := by
  unfold daysFromCivil
  dsimp only
  omega

set_option maxHeartbeats 2000000 in
theorem gantt_day_order (a b : CivilDate) (ha : a.valid) (hb : b.valid)
    (hab : a.before b) : daysFromCivil a < daysFromCivil b := by
  by_cases hYear : a.year = b.year
  · by_cases hMonth : a.month = b.month
    · have hDay : a.day < b.day := by
        unfold CivilDate.before at hab
        omega
      rcases a with ⟨year, month, first⟩
      rcases b with ⟨lastYear, lastMonth, last⟩
      dsimp only at hYear hMonth hDay
      subst lastYear
      subst lastMonth
      exact civil_same_month_day_order year month first last hDay
    · have hMonthOrder : a.month < b.month := by
        unfold CivilDate.before at hab
        omega
      have hs := civil_year_prefix_step (b.year - 1)
      have hy : b.year - 1 + 1 = b.year := by omega
      rw [hy] at hs
      rw [civil_days_normal_form, civil_days_normal_form]
      simp only [hYear]
      have hAfterA : (a.month > 2) ↔ ¬ (a.month ≤ 2) := by omega
      have hAfterB : (b.month > 2) ↔ ¬ (b.month ≤ 2) := by omega
      by_cases hEarlyA : a.month ≤ 2 <;> by_cases hEarlyB : b.month ≤ 2
      all_goals
        simp [hYear, hAfterA, hAfterB, hEarlyA, hEarlyB,
          CivilDate.valid, daysInMonth, isLeap,
          Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Bool.or_eq_true,
          Int.fdiv_eq_ediv, Int.fmod_eq_emod] at ha hb hs ⊢
        repeat first | split at ha | split at hb | split at hs | split
        all_goals
          first
          | omega
          | by_cases hJuly : a.month = 7 <;> by_cases hAugust : b.month = 8
            all_goals
              (try simp [hJuly, hAugust] at ha hb ⊢) <;> omega
  · have ba := civil_date_year_bounds a ha
    have bb := civil_date_year_bounds b hb
    have hYearOrder : a.year < b.year := by
      unfold CivilDate.before at hab
      omega
    have hPrefix := civil_year_prefix_monotone a.year (b.year - 1) (by omega)
    have hBoundary : civilYearStart (a.year + 1) ≤ civilYearStart b.year := by
      unfold civilYearStart
      have hy : a.year + 1 - 1 = a.year := by omega
      rw [hy]
      omega
    omega

theorem gantt_axis_monotone (a : Axis) (hDomain : a.startTime < a.endTime)
    (hRange : a.left ≤ a.right) (d d' : Int) (h : d ≤ d') :
    a.position d ≤ a.position d' := by
  exact linear_monotone hDomain hRange h

theorem gantt_task_rows_disjoint (top height gap i j : Int)
    (hHeight : 0 ≤ height) (hGap : 0 ≤ gap) (hOrder : i < j) :
    rowEnd top height gap i ≤ rowStart top height gap j := by
  have hPitch : 0 ≤ height + gap := by omega
  have hStep := Int.mul_le_mul_of_nonneg_right (show i + 1 ≤ j by omega) hPitch
  simp only [Int.add_mul, Int.one_mul] at hStep
  unfold rowEnd rowStart
  omega

theorem gantt_task_boxes_disjoint (p : Plan) (a b : Task) (i j : Int)
    (ha : a.vert = false) (hb : b.vert = false)
    (hHeight : 0 < p.c.barH) (hGap : 0 ≤ p.c.rowGap) (hRows : i ≠ j) :
    Disjoint (p.taskRect a i) (p.taskRect b j) := by
  have ordered (a b : Task) (i j : Int)
      (ha : a.vert = false) (hb : b.vert = false) (hij : i < j) :
      Disjoint (p.taskRect a i) (p.taskRect b j) := by
    have sep := gantt_task_rows_disjoint p.c.topPad p.c.barH p.c.rowGap i j
      (by omega) hGap hij
    simp only [Plan.taskRect, ha, hb, Bool.false_eq_true, ite_false]
    unfold Disjoint Rect.meetsInterior
    unfold rowEnd at sep
    split <;> split <;> dsimp only at * <;> omega
  by_cases hij : i < j
  · exact ordered a b i j ha hb hij
  · exact (Disjoint.comm _ _).mpr (ordered b a j i hb ha (by omega))

theorem gantt_clamped_task_boxes_disjoint (p : Plan) (a b : Task) (i j : Int)
    (ha : a.vert = false) (hb : b.vert = false)
    (hHeight : 0 < p.c.barH) (hGap : 0 ≤ p.c.rowGap) (hRows : i ≠ j) :
    Disjoint
      { (p.taskRect a i) with
        x := clamp (p.taskRect a i).x 0
          (max (p.c.width - (p.taskRect a i).w) 0) }
      { (p.taskRect b j) with
        x := clamp (p.taskRect b j).x 0
          (max (p.c.width - (p.taskRect b j).w) 0) } := by
  have ordered (a b : Task) (i j : Int)
      (ha : a.vert = false) (hb : b.vert = false) (hij : i < j) :
      Disjoint
        { (p.taskRect a i) with
          x := clamp (p.taskRect a i).x 0
            (max (p.c.width - (p.taskRect a i).w) 0) }
        { (p.taskRect b j) with
          x := clamp (p.taskRect b j).x 0
            (max (p.c.width - (p.taskRect b j).w) 0) } := by
    have sep := gantt_task_rows_disjoint p.c.topPad p.c.barH p.c.rowGap i j
      (by omega) hGap hij
    simp only [Plan.taskRect, ha, hb, Bool.false_eq_true, ite_false]
    unfold Disjoint Rect.meetsInterior
    unfold rowEnd at sep
    split <;> split <;> dsimp only at * <;> omega
  by_cases hij : i < j
  · exact ordered a b i j ha hb hij
  · exact (Disjoint.comm _ _).mpr (ordered b a j i hb ha (by omega))

theorem gantt_axis_position_inside (a : Axis) (seconds : Int)
    (hStart : min a.startTime a.endTime ≤ seconds)
    (hEnd : seconds ≤ max a.startTime a.endTime) :
    min a.left a.right ≤ a.position seconds ∧
      a.position seconds ≤ max a.left a.right := by
  exact linear_into_plot a.scale seconds hStart hEnd

theorem gantt_bar_width_bound (a : Axis) (start finish edge : Int)
    (hd : a.startTime ≤ a.endTime) (hr : a.left ≤ a.right)
    (hs0 : a.startTime ≤ start) (hs1 : start ≤ a.endTime)
    (hf : finish ≤ a.endTime) :
    barWidth a start finish edge ≤ a.right - a.left + edge := by
  by_cases heq : a.endTime = a.startTime
  · have he : a.position finish = a.position start := by
      simp only [Axis.position, Axis.scale, Linear.map, heq, ite_true]
    unfold barWidth
    rw [he]
    omega
  · have hs := gantt_axis_position_inside a start (by omega) (by omega)
    have he := gantt_axis_position_inside a a.endTime (by omega) (by omega)
    have hm := gantt_axis_monotone a (by omega) hr finish a.endTime hf
    unfold barWidth
    omega

private theorem bar_row_bounds (p : Plan) (row : Int)
    (hRow : 0 ≤ row) (hLast : row < (p.rows.length : Int))
    (hHeight : 0 ≤ p.c.barH) (hGap : 0 ≤ p.c.rowGap) :
    p.c.topPad ≤ rowStart p.c.topPad p.c.barH p.c.rowGap row ∧
    rowStart p.c.topPad p.c.barH p.c.rowGap row + p.c.barH ≤
      p.c.topPad + (p.rows.length : Int) * p.pitch := by
  have hPitch : 0 ≤ p.c.barH + p.c.rowGap := by omega
  have hLower := Int.mul_nonneg hRow hPitch
  have hUpper := Int.mul_le_mul_of_nonneg_right
    (show row + 1 ≤ (p.rows.length : Int) by omega) hPitch
  simp only [Int.add_mul, Int.one_mul] at hUpper
  unfold rowStart Plan.pitch
  omega

theorem gantt_bars_inside_axis (p : Plan) (task : Gantt.Task) (row : Int)
    (hVert : task.vert = false) (hMilestone : task.milestone = false)
    (hRow : 0 ≤ row) (hLast : row < (p.rows.length : Int))
    (hHeight : 0 ≤ p.c.barH) (hGap : 0 ≤ p.c.rowGap)
    (hGutter : 0 ≤ p.c.gutter) (hEdge : p.c.edge ≤ p.c.sidePad)
    (hRange : p.c.gutter ≤ p.c.width - p.c.sidePad)
    (hLeft : p.axis.left = p.c.gutter)
    (hRight : p.axis.right = p.c.width - p.c.sidePad)
    (hStart : min p.axis.startTime p.axis.endTime ≤ task.startTime)
    (hStartEnd : task.startTime ≤ max p.axis.startTime p.axis.endTime)
    (hEnd : min p.axis.startTime p.axis.endTime ≤ task.renderEnd)
    (hEndEnd : task.renderEnd ≤ max p.axis.startTime p.axis.endTime) :
    p.plot.Contained (p.taskRect task row) := by
  have hs := gantt_axis_position_inside p.axis task.startTime hStart hStartEnd
  have he := gantt_axis_position_inside p.axis task.renderEnd hEnd hEndEnd
  rw [hLeft, hRight] at hs he
  have hv := bar_row_bounds p row hRow hLast hHeight hGap
  simp only [Plan.plot, Plan.taskRect, hVert, hMilestone, Bool.false_eq_true,
    ite_false, Rect.Contained, barWidth]
  omega
theorem gantt_clamped_bar_inside_plot (p : Plan) (task : Gantt.Task) (row : Int)
    (hVert : task.vert = false) (hMilestone : task.milestone = false)
    (hRow : 0 ≤ row) (hLast : row < (p.rows.length : Int))
    (hHeight : 0 ≤ p.c.barH) (hGap : 0 ≤ p.c.rowGap)
    (hEdge : 0 ≤ p.c.edge) (hBudget : p.c.edge ≤ p.c.gutter + p.c.sidePad)
    (hRange : p.c.gutter ≤ p.c.width - p.c.sidePad)
    (hLeft : p.axis.left = p.c.gutter)
    (hRight : p.axis.right = p.c.width - p.c.sidePad)
    (hDomain : p.axis.startTime ≤ p.axis.endTime)
    (hStart : p.axis.startTime ≤ task.startTime)
    (hStartEnd : task.startTime ≤ p.axis.endTime)
    (hEndEnd : task.renderEnd ≤ p.axis.endTime) :
    p.plot.Contained
      { (p.taskRect task row) with
        x := clamp (p.taskRect task row).x 0
          (max (p.c.width - (p.taskRect task row).w) 0) } := by
  have hw := gantt_bar_width_bound p.axis task.startTime task.renderEnd p.c.edge
    hDomain (by omega) hStart hStartEnd hEndEnd
  rw [hLeft, hRight] at hw
  have hw0 : 0 ≤ barWidth p.axis task.startTime task.renderEnd p.c.edge := by
    unfold barWidth
    omega
  have hv := bar_row_bounds p row hRow hLast hHeight hGap
  have hx := clamp_between (p.axis.position task.startTime) 0
    (max (p.c.width - barWidth p.axis task.startTime task.renderEnd p.c.edge) 0)
  simp only [Plan.plot, Plan.taskRect, hVert, hMilestone, Bool.false_eq_true,
    ite_false, Rect.Contained]
  omega

theorem gantt_clamped_milestone_inside_plot (p : Plan) (task : Gantt.Task) (row : Int)
    (hVert : task.vert = false) (hMilestone : task.milestone = true)
    (hRow : 0 ≤ row) (hLast : row < (p.rows.length : Int))
    (hHeight : 0 ≤ p.c.barH) (hGap : 0 ≤ p.c.rowGap)
    (hWidth : p.c.barH ≤ p.c.width) :
    p.plot.Contained
      { (p.taskRect task row) with
        x := clamp (p.taskRect task row).x 0
          (max (p.c.width - (p.taskRect task row).w) 0) } := by
  have hv := bar_row_bounds p row hRow hLast hHeight hGap
  have hx := clamp_between
    (milestoneLeft p.axis p.c.barH task.startTime task.endTime) 0
    (max (p.c.width - p.c.barH) 0)
  simp only [Plan.plot, Plan.taskRect, hVert, hMilestone,
    Bool.false_eq_true, ite_false, ite_true, Rect.Contained]
  omega

def unpaddedBarWitness : Plan := {
  model := { kind := "gantt" }
  c := {
    width := 10, barH := 1, rowGap := 0, topPad := 0,
    gutter := 0, sidePad := 0, axisH := 0, tickLen := 0,
    tickGap := 0, titlePad := 0, labelGap := 0, sectionPad := 0,
    vertW := 0, tickCap := 0, estimateCap := 0, excludeYears := 0,
    edge := 1
  }
  tasks := []
  rows := ["t0"]
  axis := ⟨0, 1, 0, 10⟩
  tickValues := []
  capped := false
}

def unpaddedBarTask : Gantt.Task := {
  «section» := -1, startTime := 0, endTime := 1, renderEnd := 1,
  milestone := false, vert := false, crit := false, active := false,
  done := false
}

theorem unpadded_bar_satisfies_containment_premises :
    let p := unpaddedBarWitness
    let task := unpaddedBarTask
    task.vert = false ∧ task.milestone = false ∧
    (0 : Int) < (p.rows.length : Int) ∧
    0 ≤ p.c.barH ∧ 0 ≤ p.c.rowGap ∧ 0 ≤ p.c.edge ∧
    0 ≤ p.c.gutter ∧ 0 ≤ p.c.sidePad ∧
    p.c.gutter + p.c.sidePad + p.c.edge ≤ p.c.width ∧
    p.axis.left = p.c.gutter ∧ p.axis.right = p.c.width - p.c.sidePad ∧
    min p.axis.startTime p.axis.endTime ≤ task.startTime ∧
    task.startTime ≤ max p.axis.startTime p.axis.endTime ∧
    min p.axis.startTime p.axis.endTime ≤ task.renderEnd ∧
    task.renderEnd ≤ max p.axis.startTime p.axis.endTime := by
  decide

theorem unpadded_bar_not_contained :
    ¬ unpaddedBarWitness.plot.Contained
      (unpaddedBarWitness.taskRect unpaddedBarTask 0) := by
  decide
/-- Default vector axis, with a one-day domain. -/
def defaultDayAxis : Axis := ⟨0, 86400, 4800, 72000⟩

/-- The planned inside-axis claim is false for an earliest zero-duration milestone.
The native layout centres a 20px-wide milestone on the start tick. -/
theorem gantt_milestone_outside_axis :
    milestoneLeft defaultDayAxis 1280 0 0 = 4160 ∧
    milestoneLeft defaultDayAxis 1280 0 0 < defaultDayAxis.left := by
  decide

/-- A negative row gap is accepted by the native Gantt constant loader. With one task,
the plot height is one pitch, so the task extends below its model-stage parent. -/
theorem gantt_negative_gap_breaks_parent :
    ¬ Rect.Contained (⟨0, 3200, 76800, 1024⟩ : Rect)
      (⟨4800, rowStart 3200 1280 (-256) 0, 67200, 1280⟩ : Rect) := by
  decide

def oversizedMilestoneWitness : Model := {
  kind := "gantt"
  profile := .vector
  options := {
    profile := .vector
    config := [("barHeight", .integer 2000), ("barGap", .integer 0)]
  }
  boxes := [
    { id := "plot", role := .group, exclusive := false },
    { id := "t0", parent := "plot" }
  ]
  regionSets := [{ parent := 1, regions := [1, 0, 0, 172800, 172800] }]
}

theorem oversizedMilestoneWitness_wellFormed : WellFormed oversizedMilestoneWitness := by
  decide

theorem oversizedMilestoneWitness_withinLimits : WithinLimits oversizedMilestoneWitness := by
  decide

theorem oversized_milestone_not_contained :
    ¬ Rect.Contained (⟨0, 3200, 76800, 128000⟩ : Rect)
      (⟨0, 3200, 128000, 128000⟩ : Rect) := by
  decide

theorem oversizedMilestoneWitness_rejected :
    Kinds.Gantt.layout oversizedMilestoneWitness = .error (.geometry .domain) := by
  have ha : Kinds.Gantt.admitted oversizedMilestoneWitness = false := by decide
  unfold Kinds.Gantt.layout
  rw [ha]
  rfl

def negativeGapWitness : Model :=
  { oversizedMilestoneWitness with
    options := {
      profile := .vector
      config := [("barHeight", .integer 20), ("barGap", .integer (-4))] } }

theorem gantt_negative_gap_rejected :
    Kinds.Gantt.layout negativeGapWitness = .error (.geometry .domain) := by
  have ha : Kinds.Gantt.admitted negativeGapWitness = false := by decide
  unfold Kinds.Gantt.layout
  rw [ha]
  rfl

theorem unpadded_bar_width :
    barWidth unpaddedBarWitness.axis unpaddedBarTask.startTime
      unpaddedBarTask.renderEnd unpaddedBarWitness.c.edge =
      unpaddedBarWitness.c.width + 1 := by
  decide
def ganttParentCounterexample : Model :=
  { kind := "gantt"
    profile := .vector
    options := {}
    boxes :=
      [ { id := "plot", role := .node, parent := "", exclusive := false }
      , { id := "s0", role := .node, parent := "plot", exclusive := false }
      , { id := "t0", role := .node, parent := "s0", exclusive := false } ]
    routes := []
    labels := []
    regionSets :=
      [ { parent := 0, regions := [0, 0, 0, 0, 0] } ] }

theorem ganttParentCounterexample_wellFormed :
    Elegant.WellFormed ganttParentCounterexample := by
  decide

theorem ganttParentCounterexample_withinLimits :
    Elegant.WithinLimits ganttParentCounterexample := by
  decide

theorem gantt_c3bool_failure_lifts (d : LayoutDump)
    (hb : Validator.c3 d = false) : ¬ HardConstraints d := by
  have hC3 : ¬ Validator.C3 d := by
    intro hc
    have hciff := Validator.c3_iff d
    have ht := hciff.mpr hc
    rw [hb] at ht
    contradiction
  intro hc
  exact hC3 hc.2.2.1

/-- The parent counterexample is now rejected at admission: `t0` is parented to `s0`
instead of `plot`, which the supported structure forbids. -/
theorem ganttParentCounterexample_rejected :
    Kinds.Gantt.layout ganttParentCounterexample = .error (.geometry .domain) := by
  have ha : Kinds.Gantt.admitted ganttParentCounterexample = false := by decide
  unfold Kinds.Gantt.layout
  rw [ha]
  rfl

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩


/-- The task domain `prepare` computes, factored out so proofs can name it. -/
def taskDomain (tasks : List Task) : Int × Int :=
  match tasks with
  | [] => (0, 86400)
  | first :: rest => rest.foldl (fun (range : Int × Int) (t : Task) =>
      (min range.1 t.startTime, max range.2 t.endTime)) (first.startTime, first.endTime)

/-- The row ids `prepare` computes, factored out so proofs can name it. -/
def taskRows (m : Model) (tasks : List Task) : List String :=
  m.boxes.filterMap fun b =>
    if (boxIndex 's' b.id).isSome then some b.id else
      match boxIndex 't' b.id with
      | some i => match tasks[i]? with
        | some task => if task.vert then none else some b.id
        | none => none
      | none => none

theorem taskRows_section (m : Model) (tasks : List Task) (b : ModelBox)
    (hb : b ∈ m.boxes) (hs : (boxIndex 's' b.id).isSome = true) :
    b.id ∈ taskRows m tasks := by
  apply List.mem_filterMap.mpr
  exact ⟨b, hb, by simp only [hs, ite_true]⟩

theorem taskRows_task (m : Model) (tasks : List Task) (b : ModelBox)
    (hb : b ∈ m.boxes) (i : Nat) (task : Task)
    (hi : boxIndex 't' b.id = some i) (ht : tasks[i]? = some task)
    (hv : task.vert = false) : b.id ∈ taskRows m tasks := by
  apply List.mem_filterMap.mpr
  refine ⟨b, hb, ?_⟩
  by_cases hs : (boxIndex 's' b.id).isSome = true
  · simp only [hs, ite_true]
  · simp [hs, hi, ht, hv]

theorem row_bounds (p : Plan) (id : String) (hm : id ∈ p.rows) :
    0 ≤ p.row id ∧ p.row id < (p.rows.length : Int) := by
  cases hf : p.rows.zipIdx.find? (fun entry => entry.1 == id) with
  | none =>
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    have hz : (id, i) ∈ p.rows.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
    have hn := List.find?_eq_none.mp hf (id, i) hz
    simp at hn
  | some entry =>
    have hb := List.mem_zipIdx (List.mem_of_find?_eq_some hf)
    simp only [Plan.row, hf, Option.map_some, Option.getD_some]
    have hi : entry.2 < p.rows.length := by
      simpa only [Nat.zero_add] using hb.2.1
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast hi⟩

private theorem foldl_domain_bounds (rest : List Task) (a b : Int) :
    (rest.foldl (fun (range : Int × Int) (t : Task) =>
        (min range.1 t.startTime, max range.2 t.endTime)) (a, b)).1 ≤ a ∧
      b ≤ (rest.foldl (fun (range : Int × Int) (t : Task) =>
        (min range.1 t.startTime, max range.2 t.endTime)) (a, b)).2 ∧
      ∀ t ∈ rest, (rest.foldl (fun (range : Int × Int) (t : Task) =>
          (min range.1 t.startTime, max range.2 t.endTime)) (a, b)).1 ≤
            t.startTime ∧
        t.endTime ≤ (rest.foldl (fun (range : Int × Int) (t : Task) =>
          (min range.1 t.startTime, max range.2 t.endTime)) (a, b)).2 := by
  induction rest generalizing a b with
  | nil =>
    simp only [List.foldl]
    exact ⟨Int.le_refl _, Int.le_refl _, by simp⟩
  | cons u us ih =>
    simp only [List.foldl]
    obtain ⟨h1, h2, h3⟩ := ih (min a u.startTime) (max b u.endTime)
    refine ⟨by omega, by omega, ?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨by omega, by omega⟩
    · exact h3 t ht

/-- Every decoded task's times lie inside the domain `prepare` computes, and the domain
is ordered. -/
theorem taskDomain_bounds (tasks : List Task) (t : Task) (ht : t ∈ tasks)
    (htime : t.startTime ≤ t.endTime) :
    (taskDomain tasks).1 ≤ t.startTime ∧ t.endTime ≤ (taskDomain tasks).2 ∧
      (taskDomain tasks).1 ≤ t.endTime ∧ t.startTime ≤ (taskDomain tasks).2 ∧
      (taskDomain tasks).1 ≤ (taskDomain tasks).2 := by
  cases tasks with
  | nil => simp at ht
  | cons first rest =>
    obtain ⟨h1, h2, h3⟩ := foldl_domain_bounds rest first.startTime first.endTime
    dsimp only [taskDomain]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨h1, h2, by omega, by omega, by omega⟩
    · obtain ⟨hs, he⟩ := h3 t ht
      exact ⟨hs, he, by omega, by omega, by omega⟩

/-- `prepare` exposes its constants, task list, row list, and axis through the plan it
returns. -/
theorem prepare_decompose (m : Model) (p : Plan)
    (hp : prepare m = .ok p) :
    ∃ c, loadConsts m = .ok c ∧ p.c = c ∧
      p.tasks = m.regionSets.filterMap decodeTask ∧
      p.rows = taskRows m (m.regionSets.filterMap decodeTask) ∧
      p.axis.startTime = (taskDomain (m.regionSets.filterMap decodeTask)).1 ∧
      p.axis.endTime = (taskDomain (m.regionSets.filterMap decodeTask)).2 ∧
      p.axis.left = c.gutter ∧ p.axis.right = c.width - c.sidePad := by
  unfold prepare at hp
  split at hp
  · cases hp
  · obtain ⟨c, hload, hp⟩ := bind_ok hp
    dsimp only at hp
    split at hp
    · cases hp
    · split at hp
      · cases hp
      · split at hp
        all_goals
          obtain ⟨_, _, hp⟩ := bind_ok hp
          simp only [pure, Except.pure, Except.ok.injEq] at hp
          subst p
          refine ⟨c, hload, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
          all_goals simp_all only [taskDomain]

/-- The x-clamp `boxRect` applies to every non-plot box. -/
def boxClamp (p : Plan) (r : Rect) : Rect :=
  { r with x := clamp r.x 0 (max (p.c.width - r.w) 0) }

theorem boxRect_spec (p : Plan) (b : ModelBox) {r : Rect}
    (h : p.boxRect b = .ok r) :
    ((b.id = "plot" ∧ r = p.plot) ∨
      ((boxIndex 's' b.id).isSome = true ∧
        r = boxClamp p ⟨0, rowStart p.c.topPad p.c.barH p.c.rowGap (p.row b.id),
                       p.c.width, p.pitch⟩) ∨
      (∃ i task, boxIndex 't' b.id = some i ∧ p.tasks[i]? = some task ∧
        r = boxClamp p (p.taskRect task (p.row b.id)))) ∧
    Rect.Valid r := by
  have checked (raw : Rect)
      (hc : (if Rect.Valid raw then (Except.ok raw : Except LayoutError Rect)
        else .error .overflow) = .ok r) : r = raw ∧ Rect.Valid r := by
    split at hc
    · rename_i hv
      cases hc
      exact ⟨rfl, hv⟩
    · cases hc
  unfold Plan.boxRect at h
  simp only [Bind.bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  · rename_i hid
    obtain ⟨hr, hv⟩ := checked p.plot h
    exact ⟨Or.inl ⟨beq_iff_eq.mp hid, hr⟩, hv⟩
  · rename_i hid
    split at h
    · rename_i hs
      obtain ⟨hr, hv⟩ := checked _ h
      exact ⟨Or.inr (Or.inl ⟨hs, hr⟩), hv⟩
    · cases hi : boxIndex 't' b.id with
      | none =>
        simp only [hi] at h
        cases h
      | some i =>
        simp only [hi] at h
        cases ht : p.tasks[i]? with
        | none =>
          simp only [ht] at h
          cases h
        | some task =>
          simp only [ht] at h
          have finish (hc : (if Rect.Valid (boxClamp p (p.taskRect task (p.row b.id)))
              then (Except.ok (boxClamp p (p.taskRect task (p.row b.id))) :
                Except LayoutError Rect) else .error .overflow) = .ok r) :
              ((b.id = "plot" ∧ r = p.plot) ∨
                ((boxIndex 's' b.id).isSome = true ∧
                  r = boxClamp p ⟨0, rowStart p.c.topPad p.c.barH p.c.rowGap (p.row b.id),
                    p.c.width, p.pitch⟩) ∨
                (∃ i task, boxIndex 't' b.id = some i ∧ p.tasks[i]? = some task ∧
                  r = boxClamp p (p.taskRect task (p.row b.id)))) ∧ Rect.Valid r := by
            obtain ⟨hr, hv⟩ := checked _ hc
            exact ⟨Or.inr (Or.inr ⟨i, task, hi, ht, hr⟩), hv⟩
          cases hstart : p.axis.positionChecked task.startTime with
          | error error =>
            simp only [hstart] at h
            cases h
          | ok position =>
            simp only [hstart] at h
            cases hv : task.vert with
            | true =>
              simp [hv] at h
              simpa only [hi] using finish h
            | false =>
              simp only [hv] at h
              cases hend : p.axis.positionChecked
                  (if task.milestone then task.endTime else task.renderEnd) with
              | error error =>
                simp [hend] at h
              | ok position =>
                simp [hend] at h
                simpa only [hi] using finish h

/-- Everything a successful Gantt layout exposes: the plan's constants, decoded tasks,
rows, and axis, plus the scene assembly facts. -/
theorem successful_plan (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) :
    ∃ (p : Plan) (c : Consts) (boxes : List Box)
      (labels : List PlacedLabel) (excluded : List Primitive),
      prepare m = .ok p ∧ loadConsts m = .ok c ∧ p.c = c ∧
      0 ≤ c.topPad ∧ 0 ≤ c.gutter ∧ 0 ≤ c.sidePad ∧ 0 ≤ c.barH ∧
      0 ≤ c.rowGap ∧ 0 ≤ c.axisH ∧ 0 ≤ c.vertW ∧ 0 ≤ c.edge ∧
      0 < c.width ∧ c.barH ≤ c.width ∧ c.vertW ≤ c.width ∧
      c.edge ≤ c.gutter + c.sidePad ∧ c.gutter ≤ c.width - c.sidePad ∧
      p.tasks = m.regionSets.filterMap decodeTask ∧
      p.rows = taskRows m (m.regionSets.filterMap decodeTask) ∧
      p.axis.startTime = (taskDomain (m.regionSets.filterMap decodeTask)).1 ∧
      p.axis.endTime = (taskDomain (m.regionSets.filterMap decodeTask)).2 ∧
      p.axis.left = c.gutter ∧ p.axis.right = c.width - c.sidePad ∧
      (m.boxes.mapM fun (b : ModelBox) => do
        let rect ← p.boxRect b
        pure ({
          id := b.id
          role := b.role.id
          rect := rect
          parent := b.parent
          exclusive := b.exclusive } : Box)) = .ok boxes ∧
      placeLabels p boxes m.labels [] = .ok labels ∧
      excludedItems p = .ok excluded ∧
      result.scene = sceneOf p boxes labels excluded := by
  rcases Kinds.Gantt.successful_scene m result h with
    ⟨p, boxes, labels, excluded, hp, hb, hl, he, hs, _, _⟩
  rcases prepare_decompose m p hp with
    ⟨c, hload, hpc, hpt, hpr, hps, hpe, hpl, hpr2⟩
  have hconst := Kinds.Gantt.successful_constants m result h
  rw [hload] at hconst
  simp at hconst
  rcases hconst with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  exact ⟨p, c, boxes, labels, excluded, hp, hload, hpc,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    hpt, hpr, hps, hpe, hpl, hpr2, hb, hl, he, hs⟩

private theorem mapM_mem {α β : Type} (f : α → Except LayoutError β) :
    ∀ (l : List α) (bs : List β), l.mapM f = .ok bs → ∀ b ∈ bs, ∃ a ∈ l, f a = .ok b := by
  intro l
  induction l with
  | nil =>
    intro bs h b hb
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hb
  | cons a as ih =>
    intro bs h b hb
    rw [List.mapM_cons] at h
    rcases bind_ok h with ⟨b1, hfa, h⟩
    rcases bind_ok h with ⟨bs1, hrest, h⟩
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), hfa⟩
    · obtain ⟨x, hx, hfx⟩ := ih bs1 hrest b hb'
      exact ⟨x, List.mem_cons.mpr (Or.inr hx), hfx⟩

/-- C2 for a successful Gantt layout: every admitted box is non-exclusive, so the
exclusive-disjointness clause is vacuous. -/
theorem gantt_c2 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) : Validator.C2 result.scene.layoutDump := by
  intro b hb c hc _ hex1 _ _
  rcases Kinds.Gantt.successful_scene m result h with
    ⟨p, boxes, labels, excluded, hp, hbmap, hl, he, hs, _, _⟩
  have hboxes : result.scene.layoutDump.boxes = boxes := by
    rw [hs]
    rfl
  rw [hboxes] at hb
  obtain ⟨bm, hbm, hfa⟩ := mapM_mem _ _ _ hbmap b hb
  obtain ⟨_, hex⟩ := Kinds.Gantt.successful_supported_box m result h bm hbm
  rcases bind_ok hfa with ⟨r, hrect, hbox⟩
  simp only [pure, Except.pure, Except.ok.injEq] at hbox
  have hbe : b.exclusive = bm.exclusive := (congrArg Box.exclusive hbox).symm
  have htrue : bm.exclusive = true := hbe.symm.trans hex1
  rw [hex] at htrue
  simp at htrue

theorem successful_box_inside_plot (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Gantt.layout m = .ok result) (p : Plan)
    (hp : prepare m = .ok p) (b : ModelBox) (hb : b ∈ m.boxes)
    (r : Rect) (hr : p.boxRect b = .ok r) : p.plot.Contained r := by
  obtain ⟨c, hload, hpc, hpt, hpr, hps, hpe, hpl, hpright⟩ :=
    prepare_decompose m p hp
  have hc := Kinds.Gantt.successful_constants m result h
  rw [hload] at hc
  rw [← hpc] at hc hpl hpright
  rcases hc with ⟨htop, hgutter, hside, hbar, hgap, haxis, hvert, hedge,
    hwidth, hbarwidth, hvertwidth, hbudget, hrange⟩
  have hpitch : 0 ≤ p.pitch := by unfold Plan.pitch; omega
  obtain ⟨hspec, _⟩ := boxRect_spec p b hr
  rcases hspec with ⟨_, rfl⟩ | ⟨hsection, rfl⟩ | ⟨i, task, hi, ht, rfl⟩
  · unfold Rect.Contained
    exact ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _, Int.le_refl _⟩
  · have hrows : b.id ∈ p.rows := by
      rw [hpr]
      exact taskRows_section m _ b hb hsection
    have hrow := row_bounds p b.id hrows
    have hy0 := Int.mul_nonneg hrow.1 hpitch
    have hy1 := Int.mul_le_mul_of_nonneg_right
      (show p.row b.id + 1 ≤ (p.rows.length : Int) by omega) hpitch
    simp only [Int.add_mul, Int.one_mul] at hy1
    have hx := clamp_between 0 0 (max (p.c.width - p.c.width) 0)
    dsimp only [boxClamp, Plan.plot, Rect.Contained, rowStart] at *
    unfold Plan.pitch at *
    omega
  · have hmem : task ∈ p.tasks := List.mem_iff_getElem?.mpr ⟨i, ht⟩
    have htimes : task.startTime ≤ task.endTime ∧ task.renderEnd ≤ task.endTime := by
      rw [hpt] at hmem
      obtain ⟨region, hregion, hdecode⟩ := List.mem_filterMap.mp hmem
      obtain ⟨_, _, _, _, _, _, hstart, hend, _⟩ :=
        Kinds.Gantt.successful_region_task m result h region hregion task hdecode
      exact ⟨hstart, hend⟩
    have hdomain := taskDomain_bounds p.tasks task hmem htimes.1
    rw [← hpt] at hps hpe
    rw [← hps, ← hpe] at hdomain
    cases hv : task.vert with
    | true =>
      have hx := clamp_between
        (p.axis.position task.startTime - Int.fdiv p.c.vertW 2) 0
        (max (p.c.width - p.c.vertW) 0)
      dsimp only [boxClamp, Plan.taskRect, Plan.plot, Rect.Contained]
      simp only [hv, ite_true]
      omega
    | false =>
      have hrows : b.id ∈ p.rows := by
        rw [hpr, ← hpt]
        exact taskRows_task m p.tasks b hb i task hi ht hv
      have hrow := row_bounds p b.id hrows
      cases hm : task.milestone with
      | true =>
        exact gantt_clamped_milestone_inside_plot p task (p.row b.id)
          hv hm hrow.1 hrow.2 hbar hgap hbarwidth
      | false =>
        exact gantt_clamped_bar_inside_plot p task (p.row b.id)
          hv hm hrow.1 hrow.2 hbar hgap hedge hbudget hrange hpl hpright
          hdomain.2.2.2.2 hdomain.1 hdomain.2.2.2.1
          (by omega)

end Elegant.Chart.Gantt

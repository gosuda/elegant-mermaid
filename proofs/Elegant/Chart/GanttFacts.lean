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
    (hGutter : 0 ≤ p.c.gutter) (hSide : 0 ≤ p.c.sidePad)
    (hEdge : 0 ≤ p.c.edge) (hBudget : p.c.edge ≤ p.c.gutter + p.c.sidePad)
    (hRange : p.c.gutter + p.c.sidePad + p.c.edge ≤ p.c.width)
    (hLeft : p.axis.left = p.c.gutter)
    (hRight : p.axis.right = p.c.width - p.c.sidePad)
    (hStart : min p.axis.startTime p.axis.endTime ≤ task.startTime)
    (hStartEnd : task.startTime ≤ max p.axis.startTime p.axis.endTime)
    (hEnd : min p.axis.startTime p.axis.endTime ≤ task.renderEnd)
    (hEndEnd : task.renderEnd ≤ max p.axis.startTime p.axis.endTime) :
    p.plot.Contained
      { (p.taskRect task row) with
        x := clamp (p.taskRect task row).x 0
          (max (p.c.width - (p.taskRect task row).w) 0) } := by
  have hs := gantt_axis_position_inside p.axis task.startTime hStart hStartEnd
  have he := gantt_axis_position_inside p.axis task.renderEnd hEnd hEndEnd
  rw [hLeft, hRight] at hs he
  have hv := bar_row_bounds p row hRow hLast hHeight hGap
  have hx := clamp_between (p.axis.position task.startTime) 0
    (max (p.c.width - barWidth p.axis task.startTime task.renderEnd p.c.edge) 0)
  simp only [Plan.plot, Plan.taskRect, hVert, hMilestone, Bool.false_eq_true,
    ite_false, Rect.Contained]
  unfold barWidth at hx ⊢
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
  have ha : Kinds.Gantt.admittedConfig oversizedMilestoneWitness = false := by decide
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
  have ha : Kinds.Gantt.admittedConfig negativeGapWitness = false := by decide
  unfold Kinds.Gantt.layout
  rw [ha]
  rfl

theorem unpadded_bar_width :
    barWidth unpaddedBarWitness.axis unpaddedBarTask.startTime
      unpaddedBarTask.renderEnd unpaddedBarWitness.c.edge =
      unpaddedBarWitness.c.width + 1 := by
  decide
end Elegant.Chart.Gantt

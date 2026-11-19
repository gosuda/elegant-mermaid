import Elegant.Chart.Scale

set_option autoImplicit false

namespace Elegant.Chart.Gantt

structure CivilDate where
  year : Int
  month : Int
  day : Int
  deriving DecidableEq, Repr

def daysFromCivil (date : CivilDate) : Int :=
  let y := if date.month ≤ 2 then date.year - 1 else date.year
  let era := Int.fdiv y 400
  let yoe := y - era * 400
  let shifted := if date.month > 2 then date.month - 3 else date.month + 9
  let doy := Int.fdiv (153 * shifted + 2) 5 + date.day - 1
  let doe := yoe * 365 + Int.fdiv yoe 4 - Int.fdiv yoe 100 + doy
  era * 146097 + doe - 719468

def civilFromDays (days : Int) : CivilDate :=
  let z := days + 719468
  let era := Int.fdiv z 146097
  let doe := z - era * 146097
  let yoe := Int.fdiv (doe - Int.fdiv doe 1460 + Int.fdiv doe 36524 -
    Int.fdiv doe 146096) 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + Int.fdiv yoe 4 - Int.fdiv yoe 100)
  let mp := Int.fdiv (5 * doy + 2) 153
  let d := doy - Int.fdiv (153 * mp + 2) 5 + 1
  let m := if mp ≥ 10 then mp - 9 else mp + 3
  ⟨if m ≤ 2 then y + 1 else y, m, d⟩

def isLeap (year : Int) : Bool :=
  Int.fmod year 4 == 0 && (Int.fmod year 100 != 0 || Int.fmod year 400 == 0)

def daysInMonth (year month : Int) : Int :=
  if month = 2 then if isLeap year then 29 else 28
  else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31

abbrev CivilDate.valid (date : CivilDate) : Prop :=
  1 ≤ date.month ∧ date.month ≤ 12 ∧
    1 ≤ date.day ∧ date.day ≤ daysInMonth date.year date.month

structure Axis where
  startTime : Int
  endTime : Int
  left : Int
  right : Int
  deriving DecidableEq, Repr

def Axis.scale (a : Axis) : Linear := ⟨a.startTime, a.endTime, a.left, a.right⟩

def Axis.position (a : Axis) (seconds : Int) : Int := a.scale.map seconds

def Axis.positionChecked (a : Axis) (seconds : Int) : Except LayoutError Int :=
  if a.startTime ≠ a.endTime ∧
      ((seconds - a.startTime) * (a.right - a.left)).natAbs > 9223372036854775807 then
    .error .overflow
  else .ok (a.position seconds)

def rowStart (top height gap row : Int) : Int := top + row * (height + gap)

def rowEnd (top height gap row : Int) : Int := rowStart top height gap row + height

def milestoneLeft (a : Axis) (height startTime endTime : Int) : Int :=
  let start := a.position startTime
  start + Int.fdiv (a.position endTime - start) 2 - Int.fdiv height 2

def barLeft (a : Axis) (startTime : Int) : Int := a.position startTime

def barWidth (a : Axis) (startTime renderEnd edge : Int) : Int :=
  max (a.position renderEnd - a.position startTime) 0 + edge

end Elegant.Chart.Gantt

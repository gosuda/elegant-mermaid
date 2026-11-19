import Elegant.Chart.Gantt

set_option autoImplicit false

namespace Elegant.Chart.Gantt

inductive TickUnit where
  | second | minute | hour | day | week | month | year
  deriving DecidableEq, Repr

structure TickRule where
  unit : TickUnit
  every : Int
  deriving DecidableEq, Repr

def ceilDiv (a b : Int) : Int := -Int.fdiv (-a) b

def weekdayIndex (name : String) : Int :=
  match name with
  | "monday" => 1 | "tuesday" => 2 | "wednesday" => 3 | "thursday" => 4
  | "friday" => 5 | "saturday" => 6 | _ => 7

def autoTickTable : List (Int × TickRule) :=
  [(1, ⟨.second, 1⟩), (5, ⟨.second, 5⟩), (15, ⟨.second, 15⟩), (30, ⟨.second, 30⟩),
   (60, ⟨.minute, 1⟩), (300, ⟨.minute, 5⟩), (900, ⟨.minute, 15⟩), (1800, ⟨.minute, 30⟩),
   (3600, ⟨.hour, 1⟩), (10800, ⟨.hour, 3⟩), (21600, ⟨.hour, 6⟩), (43200, ⟨.hour, 12⟩),
   (86400, ⟨.day, 1⟩), (172800, ⟨.day, 2⟩), (604800, ⟨.week, 1⟩),
   (2592000, ⟨.month, 1⟩), (7776000, ⟨.month, 3⟩), (31536000, ⟨.year, 1⟩)]

def autoTickRule (span : Int) : TickRule := Id.run do
  let mut previous : Int × TickRule := (1, ⟨.second, 1⟩)
  for entry in autoTickTable do
    if entry.1 * 10 > span then
      if span * span < 100 * previous.1 * entry.1 then return previous.2
      else return entry.2
    previous := entry
  return previous.2

def explicitRule (text : String) : Option (TickRule × Int) := do
  let digits := text.toList.takeWhile Char.isDigit
  let n ← (String.ofList digits).toInt?
  if n ≤ 0 then none else
    let unit := String.ofList (text.toList.drop digits.length)
    match unit with
    | "second" => some (⟨.second, n⟩, 1000)
    | "minute" => some (⟨.minute, n⟩, 60000)
    | "hour" => some (⟨.hour, n⟩, 3600000)
    | "day" => some (⟨.day, n⟩, 86400000)
    | "week" => some (⟨.week, n⟩, 604800000)
    | "month" => some (⟨.month, n⟩, 2628000000)
    | _ => none

def tickRuleFor (lo hi estimateCap : Int) (interval weekday : String) : TickRule × Int :=
  match explicitRule interval with
  | some (rule, millis) =>
    if ceilDiv ((hi - lo).natAbs * 1000) (rule.every * millis) ≤ estimateCap then
      (rule, weekdayIndex weekday)
    else (autoTickRule (hi - lo).natAbs, 7)
  | none => (autoTickRule (hi - lo).natAbs, 7)

def tickBlock (rule : TickRule) (weekday lo : Int) (block : Nat) : List Int :=
  let day := Int.fdiv lo 86400
  let date := civilFromDays day
  let k := (block : Int)
  let field (seconds width unitSeconds : Int) :=
    let start := Int.fdiv lo seconds * seconds + k * seconds
    (List.range width.toNat).filterMap fun (j : Nat) =>
      if Int.fmod (j : Int) rule.every = 0 then some (start + (j : Int) * unitSeconds) else none
  match rule.unit with
  | .second => field 60 60 1
  | .minute => field 3600 60 60
  | .hour => field 86400 24 3600
  | .day =>
    let month := date.month - 1 + k
    let year := date.year + Int.fdiv month 12
    let month := Int.fmod month 12 + 1
    (List.range (daysInMonth year month).toNat).filterMap fun (j : Nat) =>
      if Int.fmod (j : Int) rule.every = 0 then
        some (daysFromCivil ⟨year, month, (j : Int) + 1⟩ * 86400) else none
  | .week =>
    let shift := Int.fmod (4 - weekday) 7
    let count := ceilDiv (ceilDiv (ceilDiv lo 86400 + shift) 7) rule.every * rule.every
    [( (count + k * rule.every) * 7 - shift) * 86400]
  | .month =>
    (List.range 12).filterMap fun (j : Nat) =>
      if Int.fmod (j : Int) rule.every = 0 then
        some (daysFromCivil ⟨date.year + k, (j : Int) + 1, 1⟩ * 86400) else none
  | .year => [daysFromCivil ⟨date.year + k, 1, 1⟩ * 86400]

def collectTicks (rule : TickRule) (weekday lo hi : Int) (cap : Nat) :
    Nat → Nat → List Int → List Int
  | 0, _, out => out
  | fuel + 1, block, out =>
    let candidates := tickBlock rule weekday lo block
    let out := (out ++ candidates.filter (fun t => lo ≤ t && t ≤ hi)).take (cap + 1)
    if out.length > cap || candidates.any (fun t => hi < t) then out
    else collectTicks rule weekday lo hi cap fuel (block + 1) out

def ticks (a : Axis) (cap estimateCap : Int) (interval weekday : String) : List Int × Bool :=
  let (rule, weekday) := tickRuleFor a.startTime a.endTime estimateCap interval weekday
  let out := collectTicks rule weekday (min a.startTime a.endTime) (max a.startTime a.endTime)
    cap.toNat (cap.toNat + 2) 0 []
  let values := out.take cap.toNat
  (if a.endTime < a.startTime then values.reverse else values, out.length > cap.toNat)

def padSigned (n : Int) (width : Nat) : String :=
  let digits := toString n.natAbs
  (if n < 0 then "-" else "") ++ String.ofList (List.replicate (width - digits.length) '0') ++ digits

def formatDirective (seconds : Int) (code : Char) : Option String :=
  let days := Int.fdiv seconds 86400
  let date := civilFromDays days
  let within := Int.fmod seconds 86400
  match code with
  | 'Y' => some (padSigned (date.year.tmod 10000) 4)
  | 'm' => some (padSigned date.month 2)
  | 'd' => some (padSigned date.day 2)
  | 'H' => some (padSigned (Int.fdiv within 3600) 2)
  | 'M' => some (padSigned (Int.fdiv (Int.fmod within 3600) 60) 2)
  | 'S' => some (padSigned (Int.fmod within 60) 2)
  | 'a' => ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"][ (Int.fmod (days + 4) 7).toNat ]?
  | 'b' => ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"][ (date.month - 1).toNat ]?
  | '%' => some "%"
  | _ => none

def formatChars (seconds : Int) : List Char → Option (List Char)
  | [] => some []
  | '%' :: code :: rest => do
    let piece ← formatDirective seconds code
    let suffix ← formatChars seconds rest
    pure (piece.toList ++ suffix)
  | '%' :: [] => none
  | c :: rest => do
    let suffix ← formatChars seconds rest
    pure (c :: suffix)

def formatTime (seconds : Int) (format : String) : String :=
  let format := if format == "" then "%Y-%m-%d" else format
  match formatChars seconds format.toList with
  | some chars => String.ofList chars
  | none => String.ofList ((formatChars seconds "%Y-%m-%d".toList).getD [])

end Elegant.Chart.Gantt

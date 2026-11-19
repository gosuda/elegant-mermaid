import Elegant.Chart.GanttLayout

set_option autoImplicit false

namespace Elegant.Chart.Gantt

open Validator

def isoDayToken (token : String) : Option Int := do
  let chars := token.toList
  if chars.length != 10 || chars[4]? != some '-' || chars[7]? != some '-' then none else do
    let y ← (String.ofList (chars.take 4)).toNat?
    let m ← (String.ofList ((chars.drop 5).take 2)).toNat?
    let d ← (String.ofList (chars.drop 8)).toNat?
    let date : CivilDate := ⟨y, m, d⟩
    if date.valid then some (daysFromCivil date) else none

def excludedDay (excludes includes : List String) (weekend : String) (day : Int) : Bool :=
  if includes.any (fun t => isoDayToken t == some day) then false else
    let weekday := Int.fmod (day + 3) 7 + 1
    let weekendStart := if weekend == "friday" then 5 else 6
    let name := ["", "monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"].getD weekday.toNat ""
    (excludes.contains "weekends" && (weekday == weekendStart || weekday == weekendStart + 1)) ||
      excludes.contains name || excludes.any (fun t => isoDayToken t == some day)

def excludedRuns (days : List Int) : List (Int × Int) :=
  match days with
  | [] => []
  | first :: rest =>
    let state := rest.foldl (fun (state : List (Int × Int) × Int × Int) day =>
      if day = state.2.2 + 1 then (state.1, state.2.1, day)
      else (state.1 ++ [(state.2.1, state.2.2)], day, day)) ([], first, first)
    state.1 ++ [(state.2.1, state.2.2)]

def excludedItems (p : Plan) : Except LayoutError (List Primitive) := do
  let span := p.axis.endTime - p.axis.startTime
  if span ≤ 0 || p.c.excludeYears * 366 * 86400 < span || p.rows.isEmpty then return []
  let excludes := (stringConfig p.model "excludes").splitOn ","
  let includes := (stringConfig p.model "includes").splitOn ","
  let weekend := stringConfig p.model "weekend" "saturday"
  let first := Int.fdiv p.axis.startTime 86400
  let last := Int.fdiv (p.axis.endTime - 1) 86400
  let days := (List.range (last - first + 1).toNat).map (fun (k : Nat) => first + Int.ofNat k)
  let runs := excludedRuns (days.filter (excludedDay excludes includes weekend))
  runs.mapM fun (first, last) => do
    let x0 ← p.axis.positionChecked (max (first * 86400) p.axis.startTime)
    let x1 ← p.axis.positionChecked (min ((last + 1) * 86400) p.axis.endTime)
    let r : Rect := ⟨min x0 x1, p.c.topPad, (x1 - x0).natAbs,
      (p.rows.length : Int) * p.pitch⟩
    if Rect.Valid r then pure (.rect r { style := "band" }) else throw .overflow

def checkPoint (point : Point) : Bool := decide (InI32 point.x ∧ InI32 point.y)

def checkPrimitive : Primitive → Bool
  | .rect r _ => decide (Rect.Valid r)
  | .roundRect r _ _ => decide (Rect.Valid r)
  | .ellipse cx cy rx ry _ => decide (InI32 cx ∧ InI32 cy ∧ InI32 rx ∧ InI32 ry)
  | .polygon points _ | .polyline points _ _ => points.all checkPoint
  | .path commands _ => commands.all fun cmd => match cmd with
    | .M point | .L point => checkPoint point
    | .C a b c => checkPoint a && checkPoint b && checkPoint c
    | .A centre radius start sweep => checkPoint centre && decide (InI32 radius ∧ InI32 start ∧ InI32 sweep)
    | .Z => true
  | .text text => decide (Rect.Valid text.rect)
  | .markerRef _ point _ | .symbolRef _ point _ => checkPoint point


def layout (m : Model) : Except LayoutError (Scene × Bool) := do
  let p ← prepare m
  let boxes ← m.boxes.mapM fun (b : ModelBox) => do
    let rect ← p.boxRect b
    pure ({
      id := b.id
      role := b.role.id
      rect := rect
      parent := b.parent
      exclusive := b.exclusive } : Box)
  let labels ← placeLabels p boxes m.labels []
  let excluded ← excludedItems p
  let scene := sceneOf p boxes labels excluded
  if InI32 scene.canvas.w ∧ InI32 scene.canvas.h ∧
      scene.items.all (fun group => group.items.all checkPrimitive) = true then
    pure (scene, p.capped)
  else throw .overflow

end Elegant.Chart.Gantt

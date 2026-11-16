import Elegant.Chart.WardleyLabels
import Elegant.Chart.XY

set_option autoImplicit false

namespace Elegant.Chart.Wardley

inductive LabelKind where
  | title | axisX | axisY | stage | node | link | note | number | annotation
  | accelerator | deaccelerator
  deriving DecidableEq, Repr

structure MeasuredLabel where
  model : ModelLabel
  kind : LabelKind
  index : Nat
  role : Measure.Role
  size : Int
  lines : List Measure.Line
  extent : TextExtent

structure FontConstants where
  labelSize : Int
  axisSize : Int
  noteSize : Int

def indexAfter (stem suffix id : String) : Option Nat :=
  let chars := id.toList
  let pre := stem.toList
  let post := suffix.toList
  if pre.isPrefixOf chars && post.reverse.isPrefixOf chars.reverse &&
      pre.length + post.length ≤ chars.length then
    (String.ofList ((chars.drop pre.length).take (chars.length - pre.length - post.length))).toNat?
  else none
def classify (l : ModelLabel) : Except LayoutError (LabelKind × Nat) := do
  if l.id = "title" then return (.title, 0)
  if l.id = "x.title" then return (.axisX, 0)
  if l.id = "y.title" then return (.axisY, 0)
  if let some i := indexAfter "st" "" l.id then return (.stage, i)
  if let some i := indexAfter "n" ".label" l.id then return (.node, i)
  if let some i := indexAfter "l" ".label" l.id then return (.link, i)
  if let some i := indexAfter "note" "" l.id then return (.note, i)
  if let some i := indexAfter "an" ".label" l.id then return (.number, i)
  if let some i := indexAfter "an" ".text" l.id then return (.annotation, i)
  if let some i := indexAfter "ac" ".label" l.id then return (.accelerator, i)
  if let some i := indexAfter "de" ".label" l.id then return (.deaccelerator, i)
  throw .domain

def textStyle (c : FontConstants) (kind : LabelKind) : Measure.Role × Int :=
  match kind with
  | .title => (.title, Measure.Role.title.sizePx)
  | .axisX | .axisY | .stage => (.label, Int.fdiv c.axisSize 64)
  | .note | .number => (.label, Int.fdiv c.noteSize 64)
  | .annotation => (.body, Int.fdiv c.noteSize 64)
  | _ => (.body, Int.fdiv c.labelSize 64)

def measureLabels (c : FontConstants) (cell : Bool) (labels : List ModelLabel) :
    Except LayoutError (List MeasuredLabel) :=
  labels.mapM fun l => do
    let (kind, index) ← classify l
    let (role, size) := textStyle c kind
    if l.text = "" then return ⟨l, kind, index, role, size, [], {}⟩
    let box ← XY.measureText cell l.text role size
    return ⟨l, kind, index, role, size, box.lines, ⟨box.w, box.h⟩⟩

end Elegant.Chart.Wardley

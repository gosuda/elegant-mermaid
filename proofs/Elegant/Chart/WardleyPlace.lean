import Elegant.Chart.WardleyMeasure

set_option autoImplicit false

namespace Elegant.Chart.Wardley

structure PlacedLabel where
  measured : MeasuredLabel
  rect : Rect
  align : Align
  shown : Bool

private def pointAt (ps : List Point) (index : Nat) : Point :=
  (ps[index]?).getD ⟨0, 0⟩

private def annotationNumber (labels : List MeasuredLabel) (index : Nat) : Int :=
  match labels.find? (fun l => l.kind == .number && l.index == index) with
  | none => 0
  | some l => l.model.text.toInt?.getD 0

def boxedAnnotations (labels : List MeasuredLabel) : List MeasuredLabel :=
  (labels.filter (fun l => l.kind == .annotation && l.model.text != "")).mergeSort
    (fun a b => annotationNumber labels a.index ≤ annotationNumber labels b.index)

def labelPosition (c : LabelConstants) (cell : Bool) (input : Input) (g : Geometry)
    (routes : List ModelRoute) (box : Rect) (boxed : List MeasuredLabel)
    (l : MeasuredLabel) : Except LayoutError (Rect × Align) := do
  let t := l.extent
  match l.kind with
  | .title => return (titleLabel g.plot t, .middle)
  | .axisX => return (xAxisLabel c g.plot t, .middle)
  | .axisY => return (yAxisLabel c g.plot t, .start)
  | .stage => return (stageLabel c g.plot input l.index t, .middle)
  | .node =>
      let some n := input.nodes[l.index]? | throw .domain
      return nodeLabel c cell n (pointAt g.positions l.index) t
  | .link =>
      let some r := routes.find? (fun r => r.id == l.model.owner) | throw .domain
      let some source := indexAfter "n" "" r.fromId | throw .domain
      let some target := indexAfter "n" "" r.toId | throw .domain
      return linkLabel c (pointAt g.positions source) (pointAt g.positions target) t
  | .note =>
      let pos := pointAt g.notes l.index
      return (⟨pos.x, pos.y - t.h, t.w, t.h⟩, .start)
  | .number => return (centredAt (pointAt g.annotations l.index) t, .middle)
  | .annotation =>
      if input.box.isSome && !boxed.isEmpty then
        let earlier := (boxed.takeWhile (fun a => a.index != l.index)).map (·.extent)
        return (annotationBoxLabel c box earlier t, .start)
      return (annotationLabel c (pointAt g.annotations l.index) t, .start)
  | .accelerator =>
      let some r := g.accelerators[l.index]? | throw .domain
      return (forceLabel c r t, .middle)
  | .deaccelerator =>
      let some r := g.deaccelerators[l.index]? | throw .domain
      return (forceLabel c r t, .middle)

def placeLabels (c : LabelConstants) (cell : Bool) (input : Input) (g : Geometry)
    (routes : List ModelRoute) (labels : List MeasuredLabel) :
    Except LayoutError (Rect × List PlacedLabel) := do
  let boxed := boxedAnnotations labels
  let box := match input.box with
    | some pos => annotationBox c g.plot pos (boxed.map (·.extent))
    | none => ⟨0, 0, 0, 0⟩
  let placed ← labels.mapM fun l => do
    if l.model.text = "" then return ⟨l, ⟨0, 0, 0, 0⟩, .start, false⟩
    let (r, align) ← labelPosition c cell input g routes box boxed l
    return ⟨l, fitCanvas g.canvas r, align, true⟩
  return (box, placed)

def PlacedLabel.dump (l : PlacedLabel) : SceneLabel :=
  { id := l.measured.model.id, owner := l.measured.model.owner, text := l.measured.model.text
    rect := l.rect, lines := if l.shown then l.measured.lines.map (fun line => String.ofList line.text) else [] }

end Elegant.Chart.Wardley

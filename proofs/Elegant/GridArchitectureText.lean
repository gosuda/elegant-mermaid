import Elegant.StyledMeasure
import Elegant.Scene

set_option autoImplicit false

namespace Elegant.Grid.Architecture

def sliceRuns (runs : List Label.Run) (offset count : Nat) : List TextRun :=
  match runs with
  | [] => []
  | r :: rs =>
    if r.text.length ≤ offset then sliceRuns rs (offset - r.text.length) count
    else
      let part := (r.text.drop offset).take count
      let tail := sliceRuns rs 0 (count - part.length)
      if part.isEmpty then tail else
        { text := String.ofList part, bold := r.bold, italic := r.italic } :: tail

def sceneLines (source : String) (ls : List Measure.Line) : List (List TextRun) :=
  let runs := (Label.regions source.toList).flatMap fun reg =>
    reg.runs ++ [{text := reg.separator,bold := false,italic := false}]
  (ls.foldl (fun (state : Nat × List (List TextRun)) line =>
    (state.1 + line.text.length + line.sep.length,
      state.2 ++ [sliceRuns runs state.1 line.text.length])) (0,[])).2

def styledText (source : String) (r : Rect) (align : Align) (ls : List Measure.Line) : Primitive :=
  .text {rect := r,role := .label,size := 14,align := align,style := "text",lines := sceneLines source ls}

end Elegant.Grid.Architecture

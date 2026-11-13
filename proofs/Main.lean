import ElegantGeometry
import Elegant
import ElegantGeometry.Eval
import Elegant.Kinds.Flowchart
import Elegant.Kinds.Class


set_option autoImplicit false

def usage : String :=
  "usage: geomcheck validate | eval FILE | layout | text --charset unicode|ascii"

def readStdin : IO String := do
  let stdin ← IO.getStdin
  stdin.readToEnd

def validateMain : IO UInt32 := do
  let text ← readStdin
  match DumpReader.readDump text with
  | .error reason =>
    IO.eprintln s!"malformed dump: {reason}"
    pure 2
  | .ok d =>
    match Validator.validate d with
    | none =>
      IO.println "valid"
      pure 0
    | some (id, msg) =>
      IO.println s!"invalid {id}: {msg}"
      pure 1

def evalLines : List String → Nat → IO UInt32
  | [], _ => pure 0
  | [""], _ => pure 0
  | [_], n => do
    IO.eprintln s!"bad case line {n}"
    pure 2
  | line :: rest, n => do
    match ElegantGeometry.Eval.evalLine line with
    | .error _ =>
      IO.eprintln s!"bad case line {n}"
      pure 2
    | .ok out =>
      IO.println out
      evalLines rest (n + 1)

def evalMain (file : String) : IO UInt32 := do
  let text ← IO.FS.readFile file
  evalLines (text.splitOn "\n") 1

def layoutDiagnostic (budgetExhausted : Bool) : IO Unit :=
  if budgetExhausted then
    IO.eprintln "info[layout/budget-exhausted]: layout stopped at its iteration cap"
  else
    pure ()

def layoutFailure : LayoutError → IO UInt32
  | .overflow => do
    IO.eprintln "layout error: overflow"
    pure 1
  | .domain => do
    IO.eprintln "layout error: domain"
    pure 1

def familyFailure : Elegant.LayoutFailure → IO UInt32
  | .geometry error => layoutFailure error
  | .tooLarge limit actual => do
    IO.eprintln s!"layout error: model size {actual} exceeds limit {limit}"
    pure 1

def kindLayout (m : Elegant.Model) :
    Option (Except Elegant.LayoutFailure Elegant.Layered.FamilyResult) :=
  match m.kind with
  | "flowchart" => some (Elegant.Kinds.Flowchart.layout m)
  | "class" => some (Elegant.Kinds.Class.layout m)
  | _ => none

def withModel (run : Elegant.Model → IO UInt32) : IO UInt32 := do
  let text ← readStdin
  match Elegant.readModel text with
  | .error reason => do
    IO.eprintln s!"malformed dump: {reason}"
    pure 2
  | .ok m =>
    if (kindLayout m).isNone then do
      IO.eprintln s!"unsupported diagram kind: {m.kind}"
      pure 1
    else run m

def layoutMain : IO UInt32 :=
  withModel fun m =>
    match (kindLayout m).getD (.error (.geometry .domain)) with
    | .error e => familyFailure e
    | .ok result => do
      layoutDiagnostic result.budgetExhausted
      IO.print (Elegant.toDump result.scene)
      pure 0

def cellModel (m : Elegant.Model) : Elegant.Model :=
  { m with profile := .cell, options := { m.options with profile := .cell } }

def textMain (charset : Elegant.Text.Charset) : IO UInt32 :=
  withModel fun m =>
    match (kindLayout (cellModel m)).getD (.error (.geometry .domain)) with
    | .error e => familyFailure e
    | .ok result =>
      match Elegant.Text.render result.scene charset with
      | .error e => layoutFailure e
      | .ok (text, _) => do
        layoutDiagnostic result.budgetExhausted
        IO.print text
        pure 0

def dispatch : List String → IO UInt32
  | ["validate"] => validateMain
  | ["layout"] => layoutMain
  | ["text", "--charset", "unicode"] => textMain .unicode
  | ["text", "--charset", "ascii"] => textMain .ascii
  | ["eval", file] => evalMain file
  | _ => do
    IO.eprintln usage
    pure 2

def main (args : List String) : IO UInt32 :=
  dispatch args

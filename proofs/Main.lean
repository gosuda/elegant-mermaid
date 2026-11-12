import ElegantGeometry
import Elegant
import ElegantGeometry.Eval


set_option autoImplicit false

def usage : String :=
  "usage: geomcheck validate | eval FILE"

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

def dispatch : List String → IO UInt32
  | ["validate"] => validateMain
  | ["eval", file] => evalMain file
  | _ => do
    IO.eprintln usage
    pure 2

def main (args : List String) : IO UInt32 :=
  dispatch args

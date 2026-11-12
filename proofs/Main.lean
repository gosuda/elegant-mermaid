import ElegantGeometry
import Elegant

/-! `geomcheck`: the developer entry point. This step provides `validate`; `eval` arrives
with the kernel case runner, `layout` and `text` with the Lean reference layout.

`validate` reads a canonical layout dump on stdin and prints `valid` (exit 0), or
`invalid <clause-id>: <message>` (exit 1), or `malformed dump: REASON` (exit 2). Any
other subcommand prints the usage line on stderr and exits 2. -/

set_option autoImplicit false

/-- The usage line, printed when the subcommand is missing or unknown. -/
def usage : String :=
  "usage: geomcheck validate"

/-- Read all of stdin. -/
def readStdin : IO String := do
  let stdin ← IO.getStdin
  stdin.readToEnd

/-- `geomcheck validate`: read a layout dump on stdin and report the first violated
clause. -/
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

/-- Dispatch on the subcommand. -/
def dispatch : List String → IO UInt32
  | ["validate"] => validateMain
  | _ => do
    IO.eprintln usage
    pure 2

def main (args : List String) : IO UInt32 :=
  dispatch args

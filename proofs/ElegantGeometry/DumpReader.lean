import ElegantGeometry.Validator
import Lean

/-! Reads the canonical layout dump (`emd layout`, `spec/layout-dump.md`) into
`LayoutDump`. The reader is I/O shell code: it is outside the theorems and is checked by
`just validate`, which pipes every corpus dump through `geomcheck validate`.

The JSON keys `from` and `to` are read as `fromId` and `toId`. `canvas` is the `w` and
`h` of the top-level `canvas` object. Every malformed input produces a `String` reason,
which `geomcheck validate` prints as `malformed dump: REASON` before exiting 2. -/

set_option autoImplicit false

namespace DumpReader

open Lean (Json)

/-- An integer at a JSON position, or a reason. -/
def intAt (j : Json) : Except String Int :=
  Json.getInt? j

/-- An integer field of a JSON object, or a reason. -/
def intField (j : Json) (key : String) : Except String Int :=
  j.getObjVal? key >>= intAt

/-- A string field of a JSON object, or a reason. -/
def strField (j : Json) (key : String) : Except String String :=
  j.getObjVal? key >>= Json.getStr?

/-- A boolean field of a JSON object, or a reason. -/
def boolField (j : Json) (key : String) : Except String Bool :=
  j.getObjVal? key >>= Json.getBool?

/-- An array field of a JSON object, or a reason. -/
def arrField (j : Json) (key : String) : Except String (Array Json) :=
  j.getObjVal? key >>= Json.getArr?

/-- A list of strings, or a reason. -/
def strList (j : Json) : Except String (List String) := do
  let a ← Json.getArr? j
  a.toList.mapM Json.getStr?

/-- A point written as `[x,y]`. -/
def readPoint (j : Json) : Except String Point := do
  let a ← Json.getArr? j
  match a.toList with
  | [x, y] => pure ⟨← intAt x, ← intAt y⟩
  | _ => throw "point is not a two-element array"

/-- A box object. -/
def readBox (j : Json) : Except String Box := do
  let id ← strField j "id"
  let role ← strField j "role"
  let x ← intField j "x"
  let y ← intField j "y"
  let w ← intField j "w"
  let h ← intField j "h"
  let parent ← strField j "parent"
  let exclusive ← boolField j "exclusive"
  pure ⟨id, role, ⟨x, y, w, h⟩, parent, exclusive⟩

/-- A route object. -/
def readRoute (j : Json) : Except String Route := do
  let id ← strField j "id"
  let fromId ← strField j "from"
  let toId ← strField j "to"
  let orthogonal ← boolField j "orthogonal"
  let pts ← arrField j "points"
  let points ← pts.toList.mapM readPoint
  pure ⟨id, fromId, toId, orthogonal, points⟩

/-- A label object. -/
def readLabel (j : Json) : Except String Label := do
  let id ← strField j "id"
  let owner ← strField j "owner"
  let x ← intField j "x"
  let y ← intField j "y"
  let w ← intField j "w"
  let h ← intField j "h"
  let linesJson ← j.getObjVal? "lines"
  let lines ← strList linesJson
  pure ⟨id, owner, ⟨x, y, w, h⟩, lines⟩

/-- The dump, or a reason. `stage` is checked so that a model-stage dump, which has no
coordinates, is rejected rather than read as a layout with empty geometry. A dump that
is not `WellFormed` is rejected with the first violated condition as its reason. -/
def readDump (text : String) : Except String LayoutDump := do
  let j ← Json.parse text
  let stage ← strField j "stage"
  if stage ≠ "layout" then
    throw s!"stage is {stage}, not layout"
  let canvasJson ← j.getObjVal? "canvas"
  let w ← intField canvasJson "w"
  let h ← intField canvasJson "h"
  let boxesJson ← arrField j "boxes"
  let boxes ← boxesJson.toList.mapM readBox
  let routesJson ← arrField j "routes"
  let routes ← routesJson.toList.mapM readRoute
  let labelsJson ← arrField j "labels"
  let labels ← labelsJson.toList.mapM readLabel
  let dump : LayoutDump := ⟨⟨w, h⟩, boxes, routes, labels⟩
  match wellFormedReason dump with
  | some reason => throw reason
  | none => pure dump

end DumpReader

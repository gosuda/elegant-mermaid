import Elegant.Model
import Elegant.Layered.Pipeline

set_option autoImplicit false

/-! Class model adapter. A class box carries its three compartments (heading, attributes,
methods) in its box label, joined by blank lines. The adapter recovers them from the label
text at the last two blank lines, because members are single nonempty lines and only the
heading can hold a blank line. It sizes the box as a compartment table (class-051, class-052),
runs the layered family with those sizes, and replaces each class group's drawing by the
table drawing. Every other node box is a note. -/

namespace Elegant
namespace Kinds
namespace Class

/-- The three compartments of a class: heading lines, attribute rows, method rows. -/
structure Table where
  head : List String
  attributes : List String
  methods : List String
deriving DecidableEq, Repr

def Table.compartments (t : Table) : List (List String) := [t.head, t.attributes, t.methods]

/-! ### Label text -/

/-- Split at line breaks; the empty text is one empty line. -/
def splitLines : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    match splitLines rest with
    | [] => [[c]]
    | l :: ls => if c = '\n' then [] :: l :: ls else (c :: l) :: ls

/-- Join lines by line breaks. -/
def joinLines : List (List Char) → List Char
  | [] => []
  | [l] => l
  | l :: ls => l ++ '\n' :: joinLines ls

/-- Split at the last blank line, that is the last `"\n\n"`. -/
def splitLastBlank : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    match splitLastBlank rest with
    | some q => some (c :: q.1, q.2)
    | none =>
      match c :: rest with
      | '\n' :: '\n' :: r => some ([], r)
      | _ => none

def compartmentChars (rows : List String) : List Char := joinLines (rows.map String.toList)

/-- The rows of one compartment; the empty text is an empty compartment. -/
def compartmentLines (part : List Char) : List String :=
  if part.isEmpty then [] else (splitLines part).map String.ofList

/-- The label text of a class: three compartments joined by blank lines. -/
def Table.chars (t : Table) : List Char :=
  compartmentChars t.head ++ '\n' :: '\n' :: (compartmentChars t.attributes ++
    '\n' :: '\n' :: compartmentChars t.methods)

/-- Recover the compartments of a class label; a label with fewer than two blank lines is not a
class label. -/
def tableOfChars (cs : List Char) : Option Table := do
  let (methods, rest) ← (splitLastBlank cs).map fun q => (q.2, q.1)
  let (attributes, head) ← (splitLastBlank rest).map fun q => (q.2, q.1)
  pure ⟨(splitLines head).map String.ofList, compartmentLines attributes,
    compartmentLines methods⟩

def tableOfText (text : String) : Option Table := tableOfChars text.toList

/-! ### Size -/

def constant (profile : Profile) (name : String) : Int :=
  (Layered.PipelineImpl.constantOf profile name).getD 0

def metricOf : Profile → Except LayoutError Measure.Metric
  | .vector => Measure.Role.label.metric
  | .cell => pure Measure.Metric.cell

/-- The widest value of `f` over a list, `start` included; the first error stops it. -/
def maxWidthM {α : Type} (f : α → Except LayoutError Int) (xs : List α) (start : Int) :
    Except LayoutError Int :=
  xs.foldlM (fun acc a => do pure (max acc (← f a))) start

def compartmentWidth (m : Measure.Metric) (rows : List String) : Except LayoutError Int :=
  maxWidthM (fun row => Measure.textWidth m row.toList) rows 0

/-- Widest row of any compartment, no padding. -/
def tableWidth (m : Measure.Metric) (compartments : List (List String)) :
    Except LayoutError Int :=
  maxWidthM (compartmentWidth m) compartments 0

/-- An empty compartment keeps one row. -/
def compartmentHeight (lineH : Int) (compartment : List String) : Int :=
  (max 1 compartment.length : Int) * lineH

/-- Sum of compartment heights. -/
def tableHeight (lineH : Int) : List (List String) → Int
  | [] => 0
  | c :: cs => compartmentHeight lineH c + tableHeight lineH cs

/-- A size in the int32 range, else an overflow. -/
def checkSize (width height : Int) : Except LayoutError Size :=
  if I32_MAX < width ∨ I32_MAX < height then .error .overflow else .ok ⟨width, height⟩

/-- class-051 and class-052: widest row plus twice the padding, the compartment heights, one
separator between compartments, and two border rows in the cell profile. -/
def classSize (profile : Profile) (t : Table) : Except LayoutError Size :=
  match metricOf profile with
  | .error e => .error e
  | .ok metric =>
    match tableWidth metric t.compartments with
    | .error e => .error e
    | .ok widest =>
      checkSize (widest + 2 * constant profile "class.padding")
        (tableHeight (constant profile "line_h") t.compartments +
          ((t.compartments.length : Int) - 1) * constant profile "class.separator" +
          (if profile = .cell then 2 else 0))

/-- The compartments of a node box, none for a note. -/
def boxTable (m : Model) (b : ModelBox) : Option Table :=
  if b.role = .node then tableOfText (modelBoxText m b) else none

/-- The size handed to the family for each class box; the family minimum applies. -/
def classSizes (m : Model) : Except LayoutError (List (String × Size)) :=
  m.boxes.filterMapM fun b => do
    match boxTable m b with
    | none => pure none
    | some t =>
      let size ← classSize m.options.profile t
      let minW := (Layered.PipelineImpl.constantOf m.options.profile "node_min_w").getD 0
      let minH := (Layered.PipelineImpl.constantOf m.options.profile "node_min_h").getD 0
      pure (some (b.id, ⟨max size.w minW, max size.h minH⟩))

def sceneMarker (name : String) : String :=
  if name == "none" then "" else name

def edgeOptions (r : ModelRoute) : Layered.EdgeOptions :=
  ⟨sceneMarker r.markerStart, sceneMarker r.markerEnd, r.stroke, 1⟩

def input (m : Model) (sizes : List (String × Size)) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (modelBoxText m)
    edges := m.routes.map edgeOptions
    labels := m.labels
    fixedSizes := sizes }

/-! ### Drawing -/

/-- Top of each compartment's text: the first at `y`, then one separator below each bottom. -/
def tops (lineH separator : Int) : Int → List (List String) → List Int
  | _, [] => []
  | y, c :: cs => y :: tops lineH separator (y + compartmentHeight lineH c + separator) cs

/-- The drawing of a class: the frame, one rule between neighbouring compartments, and one
left-aligned text per compartment. The cell profile insets the table by its border rows. -/
def classPrimitives (profile : Profile) (rect : Rect) (t : Table) : List Primitive :=
  let padding := constant profile "class.padding"
  let separator := constant profile "class.separator"
  let lineH := constant profile "line_h"
  let top := if profile = .cell then rect.y + 1 else rect.y
  let right := if profile = .cell then rect.x + rect.w - 1 else rect.x + rect.w
  let ys := tops lineH separator top t.compartments
  [.rect rect { style := "node" }] ++
  ys.tail.map (fun y =>
    .polyline [⟨rect.x, y - separator⟩, ⟨right, y - separator⟩] 0 { style := "rule" }) ++
  (ys.zip t.compartments).map fun q =>
    .text { rect := ⟨rect.x + padding, q.1, rect.w - 2 * padding, compartmentHeight lineH q.2⟩
            role := .label
            size := 14
            align := .start
            style := "text"
            lines := q.2.map fun s => [⟨s, false, false⟩] }

def noteStyle : Primitive → Primitive
  | .rect r paint => .rect r { paint with style := "note" }
  | item => item

/-- Replace the drawing of class boxes and restyle note frames. -/
def decorate (m : Model) (s : Scene) : Scene :=
  { s with items := s.items.map fun group =>
      match m.boxes.find? (fun b => b.id == group.owner),
          s.boxes.find? (fun b => b.id == group.owner) with
      | some b, some placed =>
        match boxTable m b with
        | some t =>
          if group.role = .node then
            { group with items := classPrimitives m.options.profile placed.rect t }
          else group
        | none =>
          if b.role = .node ∧ group.role = .node then
            { group with items := group.items.map noteStyle }
          else group
      | _, _ => group }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match classSizes m with
  | .error e => .error (.geometry e)
  | .ok sizes =>
    match Layered.layoutFamily (input m sizes) m.options with
    | .error e => .error e
    | .ok result =>
      let markers : List RouteMarkers := m.routes.map fun r =>
        ⟨r.id, sceneMarker r.markerStart, sceneMarker r.markerEnd⟩
      .ok { result with scene := decorate m (result.scene.projectCellAttachments markers) }

end Class
end Kinds
end Elegant

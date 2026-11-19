import Elegant.Kinds.Common

set_option autoImplicit false

/-! Class model adapter. A class box carries its three compartments (heading, attributes,
methods) in its box label, joined by blank lines. The adapter recovers them from the label
text at the last two blank lines, because members are single nonempty lines and only the
heading can hold a blank line. It measures each compartment as styled text (the heading as a
label, the members as body text), sizes the box as a compartment table (class-051, class-052),
runs the layered family with those sizes, and replaces each class group's drawing by the table
drawing. Every other node box is a note. -/

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


/-- The metric of compartment `index`: the cell metric in the cell profile; in the vector profile
the heading (compartment 0) is label text and the member compartments are body text. -/
def compartmentMetric : Profile → Nat → Except LayoutError Measure.Metric
  | .cell, _ => pure Measure.Metric.cell
  | .vector, 0 => Measure.Role.label.metric
  | .vector, _ => Measure.Role.body.metric

/-- The lines of one row, wrapped without a width limit; a row with no line keeps one empty line. -/
def rowLines (metric : Measure.Metric) (row : String) : Except LayoutError (List Measure.Line) :=
  match Common.unwrapped metric row with
  | .error e => .error e
  | .ok lines => .ok (if lines.isEmpty then [⟨[], [], 0⟩] else lines)

/-- The lines of the rows of one compartment, in row order; the first failing row stops it. -/
def measureCompartment (metric : Measure.Metric) :
    List String → Except LayoutError (List Measure.Line)
  | [] => .ok []
  | row :: rows =>
    match rowLines metric row with
    | .error e => .error e
    | .ok lines =>
      match measureCompartment metric rows with
      | .error e => .error e
      | .ok rest => .ok (lines ++ rest)

/-- The measured lines of the heading, attribute, and method compartments, measured in order. -/
def measureTable (profile : Profile) (t : Table) :
    Except LayoutError (List (List Measure.Line)) :=
  match compartmentMetric profile 0 with
  | .error e => .error e
  | .ok m0 =>
    match measureCompartment m0 t.head with
    | .error e => .error e
    | .ok head =>
      match compartmentMetric profile 1 with
      | .error e => .error e
      | .ok m1 =>
        match measureCompartment m1 t.attributes with
        | .error e => .error e
        | .ok attributes =>
          match compartmentMetric profile 2 with
          | .error e => .error e
          | .ok m2 =>
            match measureCompartment m2 t.methods with
            | .error e => .error e
            | .ok methods => .ok [head, attributes, methods]

/-- The widest line of one compartment, 0 for none. -/
def compartmentWidth (lines : List Measure.Line) : Int :=
  lines.foldl (fun w l => max w l.width) 0

/-- Widest line of any compartment, no padding. -/
def tableWidth (compartments : List (List Measure.Line)) : Int :=
  compartments.foldl (fun w c => max w (compartmentWidth c)) 0

/-- An empty compartment keeps one row. -/
def compartmentHeight {α : Type} (lineH : Int) (compartment : List α) : Int :=
  (max 1 compartment.length : Int) * lineH

/-- Sum of compartment heights. -/
def tableHeight {α : Type} (lineH : Int) : List (List α) → Int
  | [] => 0
  | c :: cs => compartmentHeight lineH c + tableHeight lineH cs

/-- A size in the int32 range, else an overflow. -/
def checkSize (width height : Int) : Except LayoutError Size :=
  if I32_MAX < width ∨ I32_MAX < height then .error .overflow else .ok ⟨width, height⟩

/-- class-051 and class-052: widest line plus twice the padding, the compartment heights, one
separator between compartments, and two border rows in the cell profile. -/
def tableSize (profile : Profile) (compartments : List (List Measure.Line)) :
    Except LayoutError Size :=
  checkSize (tableWidth compartments + 2 * LayoutConst.class_padding.get profile)
    (tableHeight (LayoutConst.line_h.get profile) compartments +
      ((compartments.length : Int) - 1) * LayoutConst.class_separator.get profile +
      (if profile = .cell then 2 else 0))

def classSize (profile : Profile) (t : Table) : Except LayoutError Size :=
  match measureTable profile t with
  | .error e => .error e
  | .ok compartments => tableSize profile compartments

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
      let minW := LayoutConst.node_min_w.get m.options.profile
      let minH := LayoutConst.node_min_h.get m.options.profile
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
def tops {α : Type} (lineH separator : Int) : Int → List (List α) → List Int
  | _, [] => []
  | y, c :: cs => y :: tops lineH separator (y + compartmentHeight lineH c + separator) cs

/-- The text role of compartment `index`: the heading is a label, the members are body text. -/
def compartmentRole (index : Nat) : TextRole := if index = 0 then .label else .body

/-- The left-aligned text of one compartment, whose top is `q.1`. -/
def compartmentText (padding lineH : Int) (rect : Rect) (q : Int × List Measure.Line)
    (index : Nat) : Primitive :=
  .text { rect := ⟨rect.x + padding, q.1, rect.w - 2 * padding, compartmentHeight lineH q.2⟩
          role := compartmentRole index
          size := 14
          align := .start
          style := "text"
          lines := q.2.map fun l => [⟨String.ofList l.text, false, false⟩] }

/-- The drawing of a class: the frame, one rule between neighbouring compartments, and one
text per compartment. The cell profile insets the table by its border rows. -/
def classPrimitives (profile : Profile) (rect : Rect) (compartments : List (List Measure.Line)) :
    List Primitive :=
  let padding := LayoutConst.class_padding.get profile
  let separator := LayoutConst.class_separator.get profile
  let lineH := LayoutConst.line_h.get profile
  let top := if profile = .cell then rect.y + 1 else rect.y
  let right := if profile = .cell then rect.x + rect.w - 1 else rect.x + rect.w
  let ys := tops lineH separator top compartments
  [.rect rect { style := "node" }] ++
  ys.tail.map (fun y =>
    .polyline [⟨rect.x, y - separator⟩, ⟨right, y - separator⟩] 0 { style := "rule" }) ++
  (ys.zip compartments).zipIdx.map fun x => compartmentText padding lineH rect x.1 x.2

def noteStyle : Primitive → Primitive
  | .rect r paint => .rect r { paint with style := "note" }
  | item => item

/-- Replace the drawing of one class box and restyle note frames. -/
def decorateGroup (m : Model) (s : Scene) (group : Group) : Except LayoutError Group :=
  match m.boxes.find? (fun b => b.id == group.owner),
      s.boxes.find? (fun b => b.id == group.owner) with
  | some b, some placed =>
    match boxTable m b with
    | some t =>
      if group.role = .node then
        match measureTable m.options.profile t with
        | .error e => .error e
        | .ok compartments =>
          .ok { group with items := classPrimitives m.options.profile placed.rect compartments }
      else .ok group
    | none =>
      if b.role = .node ∧ group.role = .node then
        .ok { group with items := group.items.map noteStyle }
      else .ok group
  | _, _ => .ok group

/-- Replace the drawing of class boxes and restyle note frames. -/
def decorate (m : Model) (s : Scene) : Except LayoutError Scene :=
  match s.items.mapM (decorateGroup m s) with
  | .error e => .error e
  | .ok items => .ok { s with items := items }

def routeMarkers (m : Model) : List RouteMarkers :=
  m.routes.map fun r => ⟨r.id, sceneMarker r.markerStart, sceneMarker r.markerEnd⟩

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match classSizes m with
  | .error e => .error (.geometry e)
  | .ok sizes =>
    match Layered.layoutFamily (input m sizes) m.options with
    | .error e => .error e
    | .ok result =>
      match decorate m (result.scene.projectCellAttachments (routeMarkers m)) with
      | .error e => .error (.geometry e)
      | .ok scene => .ok { result with scene := scene }

end Class
end Kinds
end Elegant

import Elegant.Kinds.Common
import Elegant.Layered.StatePipeline
import Elegant.Kinds.StateRegions

set_option autoImplicit false

/-! State model adapter. Start, end, choice and fork pseudo-states carry an exact size from the
state constants (a fork turns with the direction of its scope) and an empty text; every other
state is an ordinary node box and a composite is a group. After layout the drawing of every
pseudo-state is replaced by its symbol, a note keeps only its frame and text, and the
concurrent regions of a composite lose their frames and gain their dividers, as the Go adapter
paints them. -/

namespace Elegant
namespace Kinds
namespace State

open Common

/-- Pseudo-state shapes that the family keeps at an exact size and the adapter redraws. -/
def isSized (shape : String) : Bool :=
  shape == "sm-circ" || shape == "fr-circ" || shape == "fork" || shape == "choice"

/-- Shapes whose group drawing the adapter replaces. -/
def isSymbol (shape : String) : Bool := isSized shape || shape == "note"

/-- The region group boxes of the model's region sets. -/
def regionIds (m : Model) : List String :=
  let groups := m.boxes.filter fun b => b.role == .group
  m.regionSets.flatMap fun s =>
    s.regions.filterMap fun (i : Int) =>
      if 0 ≤ i ∧ i < groups.length then
        match groups[i.toNat]? with
        | some g => some g.id
        | none => none
      else none

/-- A pseudo-state and a region carry no text; every other box shows its label text or its
id. -/
def boxText (m : Model) (b : ModelBox) : String :=
  if isSized b.shape then ""
  else if (regionIds m).contains b.id then ""
  else Common.boxText m b

/-- The direction of the scope that declares a box: the explicit direction of its composite,
`TB` when the composite has none, the header direction at the root. -/
def scopeDirection (m : Model) (b : ModelBox) : Direction :=
  if b.parent == "" then m.options.direction
  else
    match m.boxes.find? (fun p => p.id == b.parent) with
    | none => .TB
    | some p => Layered.PipelineImpl.directionOf p.direction


def forkSize (profile : Profile) (direction : Direction) : Size :=
  let length := LayoutConst.state_fork_length.get profile
  let thickness := LayoutConst.state_fork_thickness.get profile
  match direction with
  | .LR | .RL => ⟨thickness, length⟩
  | .TB | .BT => ⟨length, thickness⟩

def exactSize (m : Model) (b : ModelBox) : Option Size :=
  let profile := m.options.profile
  match b.shape with
  | "sm-circ" => some ⟨LayoutConst.state_start_size.get profile, LayoutConst.state_start_size.get profile⟩
  | "fr-circ" => some ⟨LayoutConst.state_end_size.get profile, LayoutConst.state_end_size.get profile⟩
  | "choice" => some ⟨LayoutConst.state_choice_size.get profile, LayoutConst.state_choice_size.get profile⟩
  | "fork" => some (forkSize profile (scopeDirection m b))
  | _ => none

def sizes (m : Model) : List (String × Size) :=
  m.boxes.filterMap fun b => (exactSize m b).map fun size => (b.id, size)

def input (m : Model) (fixed : List (String × Size)) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (boxText m)
    edges := m.routes.map fun r => edgeOptions (max r.minLength 1) r
    labels := m.labels
    fixedSizes := fixed }

/-! ### Drawing -/

def inkPaint : Paint := { style := "ink" }

def diamond (r : Rect) : Primitive :=
  let cx := r.x + Int.fdiv r.w 2
  let cy := r.y + Int.fdiv r.h 2
  .polygon [⟨cx, r.y⟩, ⟨r.x + r.w, cy⟩, ⟨cx, r.y + r.h⟩, ⟨r.x, cy⟩] { style := "node" }

def cellSymbol (shape : String) (r : Rect) : Option Primitive :=
  match shape with
  | "sm-circ" => some (.symbolRef "disc" ⟨r.x, r.y⟩ "ink")
  | "fr-circ" => some (.symbolRef "bullseye" ⟨r.x, r.y⟩ "ink")
  | "choice" => some (.symbolRef "diamond-hollow" ⟨r.x, r.y⟩ "node")
  | _ => none

def circles (shape : String) (r : Rect) : Except LayoutError (List Primitive) :=
  let cx := r.x + Int.fdiv r.w 2
  let cy := r.y + Int.fdiv r.h 2
  if shape == "fr-circ" then
    let inner := LayoutConst.state_end_inner_size.vector
    if inner ≤ 0 ∨ r.w < inner ∨ r.h < inner then .error .domain
    else .ok [.ellipse cx cy (Int.fdiv r.w 2) (Int.fdiv r.h 2) { style := "ink-line" },
      .ellipse cx cy (Int.fdiv inner 2) (Int.fdiv inner 2) inkPaint]
  else .ok [.ellipse cx cy (Int.fdiv r.w 2) (Int.fdiv r.h 2) inkPaint]

def symbolItems (profile : Profile) (shape : String) (r : Rect) :
    Except LayoutError (List Primitive) :=
  if r.w ≤ 0 ∨ r.h ≤ 0 then .error .domain
  else if profile = .cell ∧ shape != "fork" then
    match cellSymbol shape r with
    | some item => .ok [item]
    | none => .error .domain
  else if shape == "fork" then .ok [.rect r inkPaint]
  else if shape == "choice" then .ok [diamond r]
  else circles shape r

/-- A note keeps its frame, restyled, and its text. -/
def noteItems (items : List Primitive) (r : Rect) : List Primitive :=
  .rect r { style := "note" } :: items.filter fun item =>
    match item with
    | .text _ => true
    | _ => false

def decorateGroup (m : Model) (s : Scene) (group : Group) : Except LayoutError Group :=
  if group.role != .node then .ok group
  else
    match m.boxes.find? (fun b => b.id == group.owner) with
    | none => .ok group
    | some b =>
      if !isSymbol b.shape then .ok group
      else
        match s.boxes.find? (fun placed => placed.id == group.owner) with
        | none => .error .domain
        | some placed =>
          if b.shape == "note" then .ok { group with items := noteItems group.items placed.rect }
          else do
            let items ← symbolItems m.options.profile b.shape placed.rect
            pure { group with items := items }

def decorate (m : Model) (s : Scene) : Except LayoutError Scene :=
  match s.items.mapM (decorateGroup m s) with
  | .error e => .error e
  | .ok items => .ok { s with items := items }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match Layered.layoutFamilyRN ((sizes m).map (·.1)) m.regionSets (input m (sizes m)) m.options with
  | .error e => .error e
  | .ok result =>
    match decorate m (result.scene.projectCellAttachments (routeMarkers m)) with
    | .error e => .error (.geometry e)
    | .ok scene =>
      match StateRegions.paintRegions m scene with
      | .error e => .error (.geometry e)
      | .ok scene => .ok { result with scene := scene }

end State
end Kinds
end Elegant

import Elegant.Model
import Elegant.Layered.Pipeline

set_option autoImplicit false

/-! Adapter from the model-stage dump of a flowchart to the input of the layered family
(spec/model-dump.md, model-dump-17 and model-dump-18). A box with no label record named
`<boxId>.label` and owned by the box has its id as its label text; a route that owns a label
record `<routeId>.label` has minimum length 2 (spec/layout/layered.md, layered-15), every other
route has minimum length 1. The model-stage dump carries neither the dash count of an edge nor its
markers or stroke, so the adapter cannot reproduce an edge of more than one dash of extra length,
and it draws every route as a solid line with an arrowhead at its target. Markers and strokes do
not reach the layout-stage dump; they reach the text rendering only. Label records owned by a box
are consumed here and the layout stage writes no label record. -/

namespace Elegant
namespace Kinds
namespace Flowchart

def ownsLabel (id : String) (l : ModelLabel) : Bool :=
  l.owner == id && l.id == id ++ ".label"

def boxText (m : Model) (b : ModelBox) : String :=
  match m.labels.find? (ownsLabel b.id) with
  | some l => l.text
  | none => b.id

def routeMinLength (m : Model) (r : ModelRoute) : Int :=
  if m.labels.any (ownsLabel r.id) then 2 else 1

def edgeOptions (m : Model) (r : ModelRoute) : Layered.EdgeOptions :=
  ⟨"", "point", "normal", routeMinLength m r⟩

def input (m : Model) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (boxText m)
    edges := m.routes.map (edgeOptions m) }

def layout (m : Model) : Except LayoutError Layered.FamilyResult :=
  Layered.layoutFamily (input m) m.options

end Flowchart
end Kinds
end Elegant

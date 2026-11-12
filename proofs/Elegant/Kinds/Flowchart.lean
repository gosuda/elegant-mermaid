import Elegant.Model
import Elegant.Layered.Pipeline

set_option autoImplicit false

/-! Adapter from the model-stage dump of a flowchart to the input of the layered family
(spec/model-dump.md, model-dump-17 to model-dump-20). A box with no label record named
`<boxId>.label` and owned by the box has its id as its label text. In the walking-skeleton steps
every edge has minimum length 1: the dash count of a link never changes a rank, and a label
record owned by a route changes nothing until label nodes arrive (model-dump-20). The route
record carries the marker at each end and the stroke (model-dump-19); `none` is the absence of a
marker. Markers and strokes reach the scene items only, never the layout-stage dump. Label
records owned by a box are consumed here and the layout stage writes no label record. -/

namespace Elegant
namespace Kinds
namespace Flowchart

def ownsLabel (id : String) (l : ModelLabel) : Bool :=
  l.owner == id && l.id == id ++ ".label"

def boxText (m : Model) (b : ModelBox) : String :=
  match m.labels.find? (ownsLabel b.id) with
  | some l => l.text
  | none => b.id

def routeMinLength : Int := 1

def sceneMarker (name : String) : String :=
  if name == "none" then "" else name

def edgeOptions (r : ModelRoute) : Layered.EdgeOptions :=
  ⟨sceneMarker r.markerStart, sceneMarker r.markerEnd, r.stroke, routeMinLength⟩

def input (m : Model) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (boxText m)
    edges := m.routes.map edgeOptions }

def layout (m : Model) : Except LayoutError Layered.FamilyResult :=
  Layered.layoutFamily (input m) m.options

end Flowchart
end Kinds
end Elegant

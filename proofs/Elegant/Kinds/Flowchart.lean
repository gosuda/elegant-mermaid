import Elegant.Model
import Elegant.Layered.Pipeline
import Elegant.Kinds.FlowchartIcons

set_option autoImplicit false

/-! Flowchart model adapter. Box-owned labels provide node text; route-owned label records
reach the family in model order. The family measures them and raises labelled-edge minimum
lengths to two before ranking. Markers and strokes remain scene metadata. Icon nodes (shapes
`icon`, `iconCircle`, `iconRounded`, `iconSquare`) get the built-in `unknown` icon after the
family scene is assembled (`FlowchartIcons`). -/

namespace Elegant
namespace Kinds
namespace Flowchart

def boxText (m : Model) (b : ModelBox) : String :=
  modelBoxText m b

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
    edges := m.routes.map edgeOptions
    labels := m.labels }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  let result ← Layered.layoutFamily (input m) m.options
  let markers : List RouteMarkers := m.routes.map fun r =>
    ⟨r.id, sceneMarker r.markerStart, sceneMarker r.markerEnd⟩
  pure { result with scene := placeIcons m (result.scene.projectCellAttachments markers) }

end Flowchart
end Kinds
end Elegant

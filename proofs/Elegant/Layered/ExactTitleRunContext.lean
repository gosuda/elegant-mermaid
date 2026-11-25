import Elegant.Layered.ExactFlatFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The shared measured and exact graphs before the component fold. A selected
component can execute `componentRunX` without the other components doing so. -/
structure ExactTitleRunContext (exactIds : List String) (inp : Input) (o : Options) where
  params : Params
  lines : List (List Measure.Line)
  measured : List MeasuredLabel
  graph0 : Graph
  graph : Graph
  checked : checkedParams o.profile inp.kind = .ok params
  lines_len : lines.length = inp.boxes.length
  graph0_eq : measuredGraph params inp o lines = .ok graph0
  graph_eq : exactGraph params exactIds inp o measured graph0 = .ok graph

def SceneExecutionX.exactTitleContext {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (e : SceneExecutionX exactIds inp o res) :
    ExactTitleRunContext exactIds inp o :=
  ⟨e.params, e.lines, e.measured, e.graph0, e.graph, e.checked,
    by simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ e.lines_eq).1,
    e.graph0_eq, e.graph_eq⟩

end Elegant.Layered.PipelineImpl

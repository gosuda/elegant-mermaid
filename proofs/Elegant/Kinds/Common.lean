import Elegant.Model
import Elegant.Layered.Pipeline

set_option autoImplicit false

/-! Helpers shared by the per-kind adapters that follow the Go layered adapters: the label
metric, checked sizes, and the family minimum that Go applies to a non-exact `Input.Sizes`
entry. Constants are read directly from the generated `LayoutConst` definitions. -/

namespace Elegant
namespace Kinds
namespace Common


def labelMetric : Profile → Except LayoutError Measure.Metric
  | .vector => Measure.Role.label.metric
  | .cell => pure Measure.Metric.cell

def checkSize (width height : Int) : Except LayoutError Size :=
  if I32_MAX < width ∨ I32_MAX < height then .error .overflow else .ok ⟨width, height⟩

/-- Go raises a non-exact size to the family minimum before ranking. -/
def withFamilyMinimum (profile : Profile) (size : Size) : Size :=
  ⟨max size.w (LayoutConst.node_min_w.get profile), max size.h (LayoutConst.node_min_h.get profile)⟩

def sceneMarker (name : String) : String :=
  if name == "none" then "" else name

def edgeOptions (minLength : Int) (r : ModelRoute) : Layered.EdgeOptions :=
  ⟨sceneMarker r.markerStart, sceneMarker r.markerEnd, r.stroke, minLength⟩

def routeMarkers (m : Model) : List RouteMarkers :=
  m.routes.map fun r => ⟨r.id, sceneMarker r.markerStart, sceneMarker r.markerEnd⟩

/-- The text of a box: its `<id>.label` label, else the model-stage `text` of the dump, else its id. -/
def boxText (m : Model) (b : ModelBox) : String :=
  match m.labels.find? (fun l => l.owner == b.id && l.id == b.id ++ ".label") with
  | some l => l.text
  | none => b.text.getD b.id

/-- The widest line of a wrapped text. -/
def widest (lines : List Measure.Line) : Int :=
  lines.foldl (fun w l => max w l.width) 0

/-- Wrap `text` without a width limit, as Go's `StyledLines(text, math.MaxInt32, metric)`. -/
def unwrapped (metric : Measure.Metric) (text : String) :
    Except LayoutError (List Measure.Line) :=
  StyledMeasure.wrap metric I32_MAX text.toList

theorem guarded_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {x : Except ε α} {y : α}
    (h : (if c then (throw e : Except ε PUnit) >>= (fun _ => x) else x) = .ok y) :
    x = .ok y := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    cases h
  · rwa [ite_eq_right hc] at h

theorem guarded_error {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {x : Except ε α} {y : α} (hc : c)
    (h : (if c then (throw e : Except ε PUnit) >>= (fun _ => x) else x) = .ok y) :
    False := by
  rw [ite_eq_left hc] at h
  cases h

end Common
end Kinds
end Elegant

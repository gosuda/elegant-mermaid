import Elegant.Chart.Pie
import Elegant.Chart.PieFacts

set_option autoImplicit false

namespace Elegant.Kinds.Pie

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match Chart.Pie.layout m with
  | .error e => .error (.geometry e)
  | .ok scene => .ok { scene, budgetExhausted := false }

theorem pie_valid {m : Model} {result : Layered.FamilyResult}
    (hw : Elegant.WellFormed m) (hl : WithinLimits m)
    (h : layout m = .ok result) : HardConstraints result.scene.layoutDump := by
  unfold layout at h
  split at h
  · cases h
  · rename_i scene hs
    cases h
    exact Chart.Pie.pie_valid hw hl hs

end Elegant.Kinds.Pie

import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The per-expansion step fact of clause `Step`, quantified over the
`expandChild` calls `layoutRecursive` performs, with the measurements the
recursion ran the call with. -/
abbrev RecursiveStepFacts
    (Step : Params → Input → Options → ModelBox → Int → FamilyResult → FamilyResult →
      FamilyResult → Prop) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    Step P inp o group titleHeight parent child res

end Elegant.Layered.PipelineImpl

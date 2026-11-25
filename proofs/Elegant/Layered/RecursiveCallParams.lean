import Elegant.Layered.ExpandChildContainment

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The measurements an `expandChild` call inside `layoutRecursive` runs with:
`P` is the checked parameter record of the input, `titleLines` is the wrapped
group title, and `titleHeight` is the height the recursion computes from those
lines.  `layoutRecursive_succ_sources` exposes all three for every executed
call. -/
def ExpandChildCallParams (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) : Prop :=
  checkedParams o.profile inp.kind = .ok P ∧
    titleHeight = (max 1 titleLines.length : Int) * P.lineH ∧
    ExpandChildTitleWrapped P inp o group titleLines

end Elegant.Layered.PipelineImpl

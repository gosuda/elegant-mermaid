import Elegant.Layered.ExactFlatC5
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatC5Bottom
import Elegant.Layered.ExactFlatC5Ports
import Elegant.Layered.ExactFlatC5ChosenPart
import Elegant.Layered.ExactFlatC5RunAttach
import Elegant.Layered.ExactFlatC5SelfRoutes

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Flat C5 for the exact pipeline with no open hypotheses: the five
`flatC5B_layoutX` premises are discharged by `x_topRank_holds`,
`x_bottomBoundary_holds`, `x_tailPort_holds`, `x_chosenPart_holds` (over
`x_runAttach_holds`), and `x_selfRoutes_holds`. -/
theorem flatC5B_layoutX_closed (exactIds : List String) :
    FlatC5B (layoutX exactIds) :=
  flatC5B_layoutX exactIds
    (x_topRank_holds exactIds)
    (x_bottomBoundary_holds exactIds)
    (x_tailPort_holds exactIds)
    (x_chosenPart_holds exactIds (x_runAttach_holds exactIds))
    (x_selfRoutes_holds exactIds)

end PipelineImpl
end Layered
end Elegant

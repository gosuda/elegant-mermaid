import Elegant.Chart.TreemapFacts
import Elegant.Chart.TreemapContainmentFacts
import Elegant.Chart.TreemapRoutes
import Elegant.Chart.TreemapC8a
import Elegant.Chart.TreemapC8b
import Elegant.Kinds.Treemap
import Elegant.Kinds.TreemapC7
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Kinds.Treemap

/-- Treemap validity assembly: a well-formed, within-limits model whose layout
succeeds produces a dump satisfying every hard constraint, given the one part
that is still OPEN for the treemap adapter: the geometric kernels of clause
C8b (`Elegant.Treemap.C8b.Kernels`).  The public `treemap_valid` drops the
premise when the kernels are proved. -/
theorem treemap_valid_of_kernels (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : layout m = .ok result)
    (K : Elegant.Treemap.C8b.Kernels m) :
    HardConstraints result.scene.layoutDump :=
  ⟨Elegant.Treemap.CanvasC1.treemap_c1 m result h,
    Elegant.Treemap.CanvasC1.treemap_c2 m result h,
    Elegant.Treemap.Containment.treemap_c3 m result hwf h,
    treemap_c4 m result h, treemap_c5 m result h, treemap_c6 m result h,
    treemap_c7_of_kernels m result K hwf hlimits h,
    ⟨Elegant.Treemap.C8a.treemap_c8a m result hwf hlimits h,
     Elegant.Treemap.C8b.treemap_c8b m result K hwf hlimits h⟩⟩

end Elegant.Kinds.Treemap

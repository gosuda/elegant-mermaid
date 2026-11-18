import Elegant.Chart.TreemapFacts
import Elegant.Chart.TreemapContainmentFacts
import Elegant.Chart.TreemapRoutes
import Elegant.Chart.TreemapC8a
import Elegant.Chart.TreemapC8b
import Elegant.Kinds.Treemap
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Kinds.Treemap

/-- Treemap validity assembly: a well-formed, within-limits model whose layout
succeeds produces a dump satisfying every hard constraint, given the two parts
that are still OPEN for the treemap adapter: the label clearance clause C7
(`hC7`) and the geometric kernels of clause C8b (`Elegant.Treemap.C8b.Kernels`).
The public `treemap_valid` drops both premises when they are proved. -/
theorem treemap_valid_of_kernels (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : layout m = .ok result)
    (hC7 : Validator.C7 result.scene.layoutDump)
    (K : Elegant.Treemap.C8b.Kernels m) :
    HardConstraints result.scene.layoutDump :=
  ⟨Elegant.Treemap.CanvasC1.treemap_c1 m result h,
    Elegant.Treemap.CanvasC1.treemap_c2 m result h,
    Elegant.Treemap.Containment.treemap_c3 m result hwf h,
    treemap_c4 m result h, treemap_c5 m result h, treemap_c6 m result h,
    hC7,
    ⟨Elegant.Treemap.C8a.treemap_c8a m result hwf hlimits h,
     Elegant.Treemap.C8b.treemap_c8b m result K hwf hlimits h⟩⟩

end Elegant.Kinds.Treemap

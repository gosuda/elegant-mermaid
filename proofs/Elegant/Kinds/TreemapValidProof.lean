import Elegant.Kinds.TreemapValid
import Elegant.Chart.TreemapLabelOwnerCases
import Elegant.Chart.TreemapHeaderBandKernel

set_option autoImplicit false

namespace Elegant.Kinds.Treemap

/-- The C8b kernel bundle of the treemap adapter, from the two label kernels
and the four tile kernels. -/
theorem treemap_kernels (m : Model) : Elegant.Treemap.C8b.Kernels m :=
  Elegant.Treemap.C8b.kernels_of_label_kernels m
    (Elegant.Treemap.C8b.label_owner_cases' m)
    (Elegant.Treemap.C8b.internal_label_header_band' m)

/-- Treemap validity: a well-formed, within-limits model whose layout succeeds
produces a dump that satisfies every hard constraint. -/
theorem treemap_valid (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : layout m = .ok result) :
    HardConstraints result.scene.layoutDump :=
  treemap_valid_of_kernels m result hwf hlimits h (treemap_kernels m)

end Elegant.Kinds.Treemap

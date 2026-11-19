import Elegant.Layered.LaneBandsPhaseFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-- Every box of the scene is a lane band or a member of one. Band pinning
moves a box only through its band, so a box outside every band keeps its
place while a lane frame moves over it. -/
def PinBoxCoverage (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing) : Prop :=
  ∀ b ∈ s.boxes, ∃ band ∈ layBands boxes s axis sp (lanesOf boxes),
    band.id = b.id ∨ b.id ∈ band.members

end LaneBands
end Layered
end Elegant

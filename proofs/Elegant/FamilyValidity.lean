import Elegant.FamilyDispatch
import Elegant.Kinds.EventmodelingSceneSeparationFacts
import Elegant.Kinds.TimelineSceneValidity
import Elegant.Kinds.JourneyFinal

set_option autoImplicit false

namespace Elegant.Lanes

/-- Lanes family validity over the executable dispatcher: every lanes-family model whose
`kindLayout` succeeds produces a dump satisfying every hard constraint. -/
theorem lanes_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hmem : m.kind ∈ ["gitgraph", "eventmodeling", "timeline", "journey"])
    (h : kindLayout m = some (.ok result)) :
    HardConstraints result.scene.layoutDump :=
  lanes_valid_of_members
    (fun hwf hlim h => Kinds.Eventmodeling.eventmodeling_valid hwf hlim h)
    (fun hwf hlim h => Kinds.Timeline.timeline_valid hwf hlim h)
    (fun hwf hlim h => Kinds.Journey.journey_valid hwf hlim h)
    hwf hlim hmem h

end Elegant.Lanes

import Elegant.Kinds.JourneySceneClauses

set_option autoImplicit false

namespace Elegant.Kinds.Journey

/-- The public journey validity theorem: a well-formed, within-limits model whose layout
succeeds produces a dump satisfying every hard constraint. -/
theorem journey_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (h : layout m = .ok result) :
    HardConstraints result.scene.layoutDump :=
  ⟨JourneySceneFacts.journey_c1 hwf h, JourneySceneFacts.journey_c2 hwf h,
    JourneySceneFacts.journey_c3 hwf h, journey_c4 h, journey_c5 h, journey_c6 h,
    journey_c7 h, ⟨JourneySceneFacts.journey_c8a hwf hlimits h, journey_c8b h⟩⟩

end Elegant.Kinds.Journey

import Elegant.FamilyDispatch
import Elegant.Kinds.EventmodelingSceneSeparationFacts
import Elegant.Kinds.TimelineSceneValidity
import Elegant.Kinds.JourneyFinal
import Elegant.Kinds.ArchitectureC8
import Elegant.Kinds.IshikawaValidClosed
import Elegant.Kinds.FlowchartValid
import Elegant.Kinds.LayeredSeamAdapters
import Elegant.Kinds.SwimlaneValidSeams
import Elegant.Kinds.UsecaseCaptionInduction

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

namespace Elegant.Grid

/-- Grid family validity over the executable dispatcher: every grid-family model whose
`kindLayout` succeeds produces a dump satisfying every hard constraint. -/
theorem grid_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hmem : m.kind ∈ ["block", "architecture", "kanban", "packet"])
    (h : kindLayout m = some (.ok result)) :
    HardConstraints result.scene.layoutDump :=
  grid_valid_of_members
    (fun hwf hlim h => Kinds.Architecture.architecture_valid_closed _ _ hwf hlim h)
    hwf hlim hmem h

end Elegant.Grid

namespace Elegant.Tree

/-- Tree family validity over the executable dispatcher: every tree-family model whose
`kindLayout` succeeds produces a dump satisfying every hard constraint. -/
theorem tree_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hmem : m.kind ∈ ["mindmap", "treeview", "ishikawa"])
    (h : kindLayout m = some (.ok result)) :
    HardConstraints result.scene.layoutDump :=
  tree_valid_of_members
    (fun hwf hlim h => Kinds.IshikawaFinal.ishikawa_valid_closed _ _ hwf hlim h)
    hwf hlim hmem h

end Elegant.Tree

namespace Elegant

theorem layered_valid_nonstate {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hmem : m.kind ∈ ["flowchart", "class", "requirement", "er", "c4", "usecase", "agentflow", "swimlane"])
    (h : kindLayout m = some (.ok result)) :
    HardConstraints result.scene.layoutDump :=
  layered_valid_of_nonstate_members
    (fun _ _ h => Kinds.flowchart_valid_of_seams h)
    (fun _ _ h => Kinds.class_valid_of_seams h)
    (fun _ _ h => Kinds.requirement_valid_of_seams h)
    (fun _ _ h => Kinds.er_valid_of_seams h)
    (fun _ _ h => Kinds.c4_valid_of_seams h)
    (fun hwf hlim h => Kinds.usecase_valid hwf hlim h)
    (fun _ _ h => Kinds.agentflow_valid_of_seams h)
    (fun hwf hlim h => Kinds.swimlane_valid hwf hlim h)
    hwf hlim hmem h

end Elegant

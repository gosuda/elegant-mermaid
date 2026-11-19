import Elegant.Kinds.Flowchart
import Elegant.Kinds.Class
import Elegant.Kinds.Requirement
import Elegant.Kinds.Er
import Elegant.Kinds.C4
import Elegant.Kinds.Usecase
import Elegant.Kinds.Agentflow
import Elegant.Kinds.Swimlane
import Elegant.Kinds.Sequence
import Elegant.Kinds.Gitgraph
import Elegant.Kinds.State
import Elegant.Kinds.Xychart
import Elegant.Kinds.Mindmap
import Elegant.Kinds.Block
import Elegant.Kinds.Railroad
import Elegant.Kinds.Timeline
import Elegant.Kinds.Eventmodeling
import Elegant.Kinds.Radar
import Elegant.Kinds.Cynefin
import Elegant.Kinds.Info
import Elegant.Kinds.Architecture
import Elegant.Kinds.Kanban
import Elegant.Kinds.Packet
import Elegant.Kinds.Treeview
import Elegant.Kinds.Ishikawa
import Elegant.Kinds.Journey
import Elegant.Kinds.Gantt
import Elegant.Kinds.Quadrant
import Elegant.Kinds.Treemap
import Elegant.Kinds.Wardley
import Elegant.Kinds.Pie
import Elegant.Kinds.Sankey
import Elegant.Kinds.Venn

set_option autoImplicit false

namespace Elegant

def kindLayout (m : Model) :
    Option (Except LayoutFailure Layered.FamilyResult) :=
  match m.kind with
  | "flowchart" => some (Kinds.Flowchart.layout m)
  | "class" => some (Kinds.Class.layout m)
  | "requirement" => some (Kinds.Requirement.layout m)
  | "er" => some (Kinds.Er.layout m)
  | "c4" => some (Kinds.C4.layout m)
  | "usecase" => some (Kinds.Usecase.layout m)
  | "agentflow" => some (Kinds.Agentflow.layout m)
  | "swimlane" => some (Kinds.Swimlane.layout m)
  | "sequence" => some (Kinds.Sequence.layout m)
  | "gitgraph" => some (Kinds.Gitgraph.layout m)
  | "state" => some (Kinds.State.layout m)
  | "xychart" => some (Kinds.Xychart.layout m)
  | "mindmap" => some (Kinds.Mindmap.layout m)
  | "block" => some (Kinds.Block.layout m)
  | "railroad" => some (Kinds.Railroad.layout m)
  | "timeline" => some (Kinds.Timeline.layout m)
  | "eventmodeling" => some (Kinds.Eventmodeling.layout m)
  | "radar" => some (Kinds.Radar.layout m)
  | "cynefin" => some (Kinds.Cynefin.layout m)
  | "info" => some (Kinds.Info.layout m)
  | "architecture" => some (Kinds.Architecture.layout m)
  | "kanban" => some (Kinds.Kanban.layout m)
  | "packet" => some (Kinds.Packet.layout m)
  | "treeview" => some (Kinds.Treeview.layout m)
  | "ishikawa" => some (Kinds.Ishikawa.layout m)
  | "journey" => some (Kinds.Journey.layout m)
  | "gantt" => some (Kinds.Gantt.layout m)
  | "quadrant" => some (Kinds.Quadrant.layout m)
  | "treemap" => some (Kinds.Treemap.layout m)
  | "wardley" => some (Kinds.Wardley.layout m)
  | "pie" => some (Kinds.Pie.layout m)
  | "sankey" => some (Kinds.Sankey.layout m)
  | "venn" => some (Kinds.Venn.layout m)
  | _ => none

end Elegant

import Elegant.FamilyDispatch
import Elegant.Kinds.XychartFacts
import Elegant.Kinds.Quadrant
import Elegant.Chart.GanttLabelFacts
import Elegant.Kinds.Cynefin
import Elegant.Kinds.Info
import Elegant.Kinds.Pie
import Elegant.Kinds.Radar
import Elegant.Chart.VennFacts
import Elegant.Kinds.Sankey
import Elegant.Kinds.TimelineSceneValidity
import Elegant.Chart.WardleyFacts
import Elegant.RailroadContainmentFacts

set_option autoImplicit false

namespace Elegant

theorem kindLayout_block_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "block")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Block.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Block.block_valid hwf hlimits hl

theorem kindLayout_packet_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "packet")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Packet.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Packet.packet_valid m result hwf hlimits hl

theorem kindLayout_kanban_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "kanban")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Kanban.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact GridKanban.kanban_valid hwf hlimits hl

theorem kindLayout_treeview_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "treeview")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Treeview.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Treeview.treeview_valid hwf hlimits hl

theorem kindLayout_quadrant_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "quadrant")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Quadrant.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Quadrant.quadrant_valid hwf hlimits hl

theorem kindLayout_gantt_valid {m : Model} {result : Layered.FamilyResult}
    (_hwf : WellFormed m) (_hlimits : WithinLimits m) (hk : m.kind = "gantt")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Gantt.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Chart.Gantt.gantt_valid m result hl

theorem kindLayout_cynefin_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "cynefin")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Cynefin.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Cynefin.cynefin_valid m result hwf hlimits hl

theorem kindLayout_info_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "info")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Info.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Info.info_valid hwf hlimits hl

theorem kindLayout_pie_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "pie")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Pie.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Pie.pie_valid hwf hlimits hl

theorem kindLayout_radar_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "radar")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Radar.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Radar.radar_valid hwf hlimits hl

theorem kindLayout_venn_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "venn")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Venn.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Chart.Venn.venn_valid m hwf hlimits result hl

theorem kindLayout_xychart_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "xychart")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Xychart.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Xychart.xychart_valid m result hwf hlimits hl

theorem kindLayout_mindmap_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (_hlimits : WithinLimits m) (hk : m.kind = "mindmap")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Mindmap.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Mindmap.layout_valid hwf hl

theorem kindLayout_gitgraph_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (_hlimits : WithinLimits m) (hk : m.kind = "gitgraph")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Gitgraph.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Gitgraph.layout_valid hwf hl

theorem kindLayout_sequence_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "sequence")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Sequence.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Sequence.layout_valid hwf hlimits hl

theorem kindLayout_sankey_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "sankey")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Sankey.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Sankey.sankey_valid hwf hlimits hl

theorem kindLayout_timeline_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "timeline")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Timeline.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Kinds.Timeline.timeline_valid hwf hlimits hl

theorem kindLayout_wardley_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "wardley")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Wardley.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Chart.Wardley.wardley_valid m result hwf hlimits hl

theorem kindLayout_railroad_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlimits : WithinLimits m) (hk : m.kind = "railroad")
    (h : kindLayout m = some (.ok result)) : HardConstraints result.scene.layoutDump := by
  have hl : Kinds.Railroad.layout m = .ok result := by
    simpa [kindLayout, hk] using h
  exact Railroad.railroad_valid m hwf hlimits result hl

end Elegant

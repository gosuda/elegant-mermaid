import Elegant.KindLayout
import Elegant.Kinds.Block
import Elegant.Kinds.Packet
import Elegant.GridKanbanValid
import Elegant.Kinds.Treeview
import Elegant.Kinds.MindmapValid
import Elegant.Kinds.GitgraphFacts

set_option autoImplicit false

namespace Elegant

theorem kindLayout_block {m : Model} (hk : m.kind = "block") :
    kindLayout m = some (Kinds.Block.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_architecture {m : Model} (hk : m.kind = "architecture") :
    kindLayout m = some (Kinds.Architecture.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_kanban {m : Model} (hk : m.kind = "kanban") :
    kindLayout m = some (Kinds.Kanban.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_packet {m : Model} (hk : m.kind = "packet") :
    kindLayout m = some (Kinds.Packet.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_mindmap {m : Model} (hk : m.kind = "mindmap") :
    kindLayout m = some (Kinds.Mindmap.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_treeview {m : Model} (hk : m.kind = "treeview") :
    kindLayout m = some (Kinds.Treeview.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_ishikawa {m : Model} (hk : m.kind = "ishikawa") :
    kindLayout m = some (Kinds.Ishikawa.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_gitgraph {m : Model} (hk : m.kind = "gitgraph") :
    kindLayout m = some (Kinds.Gitgraph.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_eventmodeling {m : Model} (hk : m.kind = "eventmodeling") :
    kindLayout m = some (Kinds.Eventmodeling.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_timeline {m : Model} (hk : m.kind = "timeline") :
    kindLayout m = some (Kinds.Timeline.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem kindLayout_journey {m : Model} (hk : m.kind = "journey") :
    kindLayout m = some (Kinds.Journey.layout m) := by
  unfold kindLayout
  rw [hk] <;> first | rfl | simp

theorem grid_valid_of_members
    (architecture_valid : ∀ {m : Model} {r : Layered.FamilyResult}, WellFormed m → WithinLimits m →
      Kinds.Architecture.layout m = .ok r → HardConstraints r.scene.layoutDump)
    {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hmem : m.kind ∈ ["block", "architecture", "kanban", "packet"])
    (h : kindLayout m = some (.ok result)) :
    HardConstraints result.scene.layoutDump := by
  simp at hmem
  rcases hmem with hk | hk | hk | hk
  · have hl : Kinds.Block.layout m = .ok result :=
      Option.some.inj ((kindLayout_block hk).symm.trans h)
    exact Kinds.Block.block_valid hwf hlim hl
  · have hl : Kinds.Architecture.layout m = .ok result :=
      Option.some.inj ((kindLayout_architecture hk).symm.trans h)
    exact architecture_valid hwf hlim hl
  · have hl : Kinds.Kanban.layout m = .ok result :=
      Option.some.inj ((kindLayout_kanban hk).symm.trans h)
    exact GridKanban.kanban_valid hwf hlim hl
  · have hl : Kinds.Packet.layout m = .ok result :=
      Option.some.inj ((kindLayout_packet hk).symm.trans h)
    exact Kinds.Packet.packet_valid m result hwf hlim hl

theorem tree_valid_of_members
    (ishikawa_valid : ∀ {m : Model} {r : Layered.FamilyResult}, WellFormed m → WithinLimits m →
      Kinds.Ishikawa.layout m = .ok r → HardConstraints r.scene.layoutDump)
    {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hmem : m.kind ∈ ["mindmap", "treeview", "ishikawa"])
    (h : kindLayout m = some (.ok result)) :
    HardConstraints result.scene.layoutDump := by
  simp at hmem
  rcases hmem with hk | hk | hk
  · have hl : Kinds.Mindmap.layout m = .ok result :=
      Option.some.inj ((kindLayout_mindmap hk).symm.trans h)
    exact Kinds.Mindmap.layout_valid hwf hl
  · have hl : Kinds.Treeview.layout m = .ok result :=
      Option.some.inj ((kindLayout_treeview hk).symm.trans h)
    exact Kinds.Treeview.treeview_valid hwf hlim hl
  · have hl : Kinds.Ishikawa.layout m = .ok result :=
      Option.some.inj ((kindLayout_ishikawa hk).symm.trans h)
    exact ishikawa_valid hwf hlim hl

theorem lanes_valid_of_members
    (eventmodeling_valid : ∀ {m : Model} {r : Layered.FamilyResult}, WellFormed m → WithinLimits m →
      Kinds.Eventmodeling.layout m = .ok r → HardConstraints r.scene.layoutDump)
    (timeline_valid : ∀ {m : Model} {r : Layered.FamilyResult}, WellFormed m → WithinLimits m →
      Kinds.Timeline.layout m = .ok r → HardConstraints r.scene.layoutDump)
    (journey_valid : ∀ {m : Model} {r : Layered.FamilyResult}, WellFormed m → WithinLimits m →
      Kinds.Journey.layout m = .ok r → HardConstraints r.scene.layoutDump)
    {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hmem : m.kind ∈ ["gitgraph", "eventmodeling", "timeline", "journey"])
    (h : kindLayout m = some (.ok result)) :
    HardConstraints result.scene.layoutDump := by
  simp at hmem
  rcases hmem with hk | hk | hk | hk
  · have hl : Kinds.Gitgraph.layout m = .ok result :=
      Option.some.inj ((kindLayout_gitgraph hk).symm.trans h)
    exact Kinds.Gitgraph.layout_valid hwf hl
  · have hl : Kinds.Eventmodeling.layout m = .ok result :=
      Option.some.inj ((kindLayout_eventmodeling hk).symm.trans h)
    exact eventmodeling_valid hwf hlim hl
  · have hl : Kinds.Timeline.layout m = .ok result :=
      Option.some.inj ((kindLayout_timeline hk).symm.trans h)
    exact timeline_valid hwf hlim hl
  · have hl : Kinds.Journey.layout m = .ok result :=
      Option.some.inj ((kindLayout_journey hk).symm.trans h)
    exact journey_valid hwf hlim hl

end Elegant

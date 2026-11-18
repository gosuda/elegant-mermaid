import Elegant.Kinds.TimelineHorizontalSceneFacts
import Elegant.Kinds.TimelineVerticalFacts

set_option autoImplicit false

namespace Elegant.Kinds.Timeline

theorem timeline_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : layout m = .ok result) : HardConstraints result.scene.layoutDump := by
  obtain ⟨s, hs, _hdump⟩ := layout_scene h
  obtain ⟨g, _r, hg, _hr, _hc, _hl, _hb, _hroutes⟩ := scene_execution hs
  have branches : Validator.C2 result.scene.layoutDump ∧
      Validator.C5 result.scene.layoutDump ∧
      Validator.C6 result.scene.layoutDump ∧
      Validator.C8a result.scene.layoutDump := by
    by_cases hdirection : g.direction = .LR
    · obtain ⟨h2, h8a⟩ := horizontal_layout_box_clearance h hg hdirection
      exact ⟨h2, horizontal_layout_ports hwf h hg hdirection,
        horizontal_layout_route_clearance hwf h hg hdirection, h8a⟩
    · have hv : Lanes.Timeline.horizontal g = false := by
        simp [Lanes.Timeline.horizontal, hdirection]
      obtain ⟨h2, h8a⟩ := layout_vertical_box_clearance hwf h hg hv
      exact ⟨h2, layout_vertical_ports hwf h hg hv,
        layout_vertical_clearance hwf h hg hv, h8a⟩
  exact ⟨layout_canvas h, branches.1, layout_parent h, layout_orthogonal h,
    branches.2.1, branches.2.2.1, layout_label_clearance h,
    branches.2.2.2, layout_frame_labels h⟩

end Elegant.Kinds.Timeline

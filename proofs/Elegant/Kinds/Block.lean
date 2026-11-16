theorem layout_ports {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C5 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_ports hwf hs

theorem layout_route_clearance {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C6 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_route_clearance hwf hs

theorem layout_label_clearance {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C7 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_label_clearance hwf hs

theorem layout_frame_clearance {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C8 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_frame_clearance hwf hs

theorem block_valid {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (_hlimits : WithinLimits m) (h : layout m = .ok r) :
    HardConstraints r.scene.layoutDump :=
  ⟨layout_canvas h, layout_siblings hwf h, layout_parent hwf h,
    layout_orthogonal h, layout_ports hwf h, layout_route_clearance hwf h,
    layout_label_clearance hwf h, layout_frame_clearance hwf h⟩

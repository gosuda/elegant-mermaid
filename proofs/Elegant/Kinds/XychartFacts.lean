theorem xychart_valid (m : Model) (result : Layered.FamilyResult)
    (_hwf : WellFormed m) (_hlim : WithinLimits m) (h : layout m = .ok result) :
    HardConstraints result.scene.layoutDump :=
  layout_valid h

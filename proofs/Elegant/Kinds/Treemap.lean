  if (Elegant.Treemap.constants m).width < 0 then
    throw (.geometry .domain)
  if (Elegant.Treemap.constants m).height < 0 then
    throw (.geometry .domain)
theorem layout_adapter_success (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    Elegant.Treemap.layout m = .ok result.scene := by
  unfold layout at h
  have h := Common.guarded_ok
    (Common.guarded_ok (Common.guarded_ok (Common.guarded_ok h)))
  cases hs : Elegant.Treemap.layout m with
  | error e => simp [hs] at h
  | ok scene =>
    simp only [hs, pure, Except.pure, Except.ok.injEq] at h
    cases h
    rfl

theorem layout_width_nonnegative (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : 0 ≤ (Elegant.Treemap.constants m).width := by
  unfold layout at h
  have h := Common.guarded_ok (Common.guarded_ok h)
  by_cases hw : (Elegant.Treemap.constants m).width < 0
  · exact (Common.guarded_error hw h).elim
  · omega

theorem layout_height_nonnegative (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : 0 ≤ (Elegant.Treemap.constants m).height := by
  unfold layout at h
  have h := Common.guarded_ok (Common.guarded_ok (Common.guarded_ok h))
  by_cases hh : (Elegant.Treemap.constants m).height < 0
  · exact (Common.guarded_error hh h).elim
  · omega

theorem layout_routes_eq_nil (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : result.scene.layoutDump.routes = [] := by
  exact Elegant.Treemap.layout_routes_eq_nil m result.scene
    (layout_adapter_success m result h)

theorem treemap_c4 (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C4 result.scene.layoutDump := by
  intro route hr
  rw [layout_routes_eq_nil m result h] at hr
  simp at hr

theorem treemap_c5 (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C5 result.scene.layoutDump := by
  intro route hr
  rw [layout_routes_eq_nil m result h] at hr
  simp at hr

theorem treemap_c6 (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C6 result.scene.layoutDump := by
  intro route hr
  rw [layout_routes_eq_nil m result h] at hr
  simp at hr

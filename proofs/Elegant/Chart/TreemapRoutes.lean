import Elegant.Chart.TreemapFacts

set_option autoImplicit false

namespace Elegant.Treemap

theorem treemap_routes_nil (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) : result.scene.layoutDump.routes = [] := by
  have hr := layout_routes_eq_nil m result.scene (Kinds.Treemap.layout_adapter_success m result h)
  simp [Scene.layoutDump, hr]

theorem treemap_c4 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) : Validator.C4 result.scene.layoutDump := by
  intro r hr
  rw [treemap_routes_nil m result h] at hr
  simp at hr

theorem treemap_c5 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) : Validator.C5 result.scene.layoutDump := by
  intro r hr
  rw [treemap_routes_nil m result h] at hr
  simp at hr

theorem treemap_c6 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) : Validator.C6 result.scene.layoutDump := by
  intro r hr
  rw [treemap_routes_nil m result h] at hr
  simp at hr

end Elegant.Treemap

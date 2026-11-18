import Elegant.Scene
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered

/-- A cell rectangle that `Size.containsCellRect` accepts is contained in the
canvas rectangle of a dump whose canvas is that size. -/
theorem containsCellRect_contained {canvas : Size} {r : Rect}
    (h : Size.containsCellRect canvas r = true) :
    (Validator.canvasRect ⟨canvas, [], [], []⟩).Contained r := by
  unfold Size.containsCellRect at h
  simp only [decide_eq_true_iff] at h
  obtain ⟨hx, hy, hw, hh, hxr, hyr⟩ := h
  unfold Validator.canvasRect Rect.Contained
  simp only
  omega

end Elegant.Layered

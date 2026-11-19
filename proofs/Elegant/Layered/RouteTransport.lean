import ElegantGeometry.Route
import ElegantGeometry.Validator
import Elegant.Model
import Elegant.Layered.Pipeline
import Elegant.Layered.Route

set_option autoImplicit false

namespace Elegant
namespace Layered

open PipelineImpl RouteImpl

theorem point_ext_iff (p q : Point) : p = q ↔ p.x = q.x ∧ p.y = q.y := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro ⟨hx, hy⟩
    cases p; cases q
    dsimp only at hx hy
    subst hx hy
    rfl

theorem shiftPoint_inj (dx dy : Int) (p q : Point) :
    shiftPoint dx dy p = shiftPoint dx dy q ↔ p = q := by
  rw [point_ext_iff, point_ext_iff]
  dsimp only [shiftPoint]
  omega

theorem shiftPoint_ne_iff (dx dy : Int) (p q : Point) :
    (shiftPoint dx dy p ≠ shiftPoint dx dy q) ↔ (p ≠ q) :=
  not_congr (shiftPoint_inj dx dy p q)

theorem orientPoint_inj (d : Direction) (h : Int) (p q : Point) :
    orientPoint d h p = orientPoint d h q ↔ p = q := by
  cases d <;> (
    rw [point_ext_iff, point_ext_iff]
    dsimp only [orientPoint]
    omega
  )

theorem orientPoint_ne_iff (d : Direction) (h : Int) (p q : Point) :
    (orientPoint d h p ≠ orientPoint d h q) ↔ (p ≠ q) :=
  not_congr (orientPoint_inj d h p q)

theorem dot_shift_coords (nx ny dx dy x y : Int) :
    Polyline.dot nx ny ⟨x + dx, y + dy⟩ = Polyline.dot nx ny ⟨x, y⟩ + (nx * dx + ny * dy) := by
  unfold Polyline.dot
  dsimp only
  rw [Int.mul_add, Int.mul_add]
  omega

theorem dot_shiftPoint (nx ny dx dy : Int) (p : Point) :
    Polyline.dot nx ny (shiftPoint dx dy p) = Polyline.dot nx ny p + (nx * dx + ny * dy) :=
  dot_shift_coords nx ny dx dy p.x p.y

theorem minCorner_shiftRect (nx ny dx dy : Int) (r : Rect) :
    Polyline.minCorner nx ny (shiftRect dx dy r) = Polyline.minCorner nx ny r + (nx * dx + ny * dy) := by
  have hc1 : Polyline.dot nx ny ⟨(shiftRect dx dy r).x, (shiftRect dx dy r).y⟩ =
      Polyline.dot nx ny ⟨r.x, r.y⟩ + (nx * dx + ny * dy) := by
    dsimp only [shiftRect]
    exact dot_shift_coords nx ny dx dy r.x r.y
  have hc2 : Polyline.dot nx ny ⟨(shiftRect dx dy r).x + (shiftRect dx dy r).w, (shiftRect dx dy r).y⟩ =
      Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ + (nx * dx + ny * dy) := by
    dsimp only [shiftRect]
    have : r.x + dx + r.w = (r.x + r.w) + dx := by omega
    rw [this]
    exact dot_shift_coords nx ny dx dy (r.x + r.w) r.y
  have hc3 : Polyline.dot nx ny ⟨(shiftRect dx dy r).x, (shiftRect dx dy r).y + (shiftRect dx dy r).h⟩ =
      Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ + (nx * dx + ny * dy) := by
    dsimp only [shiftRect]
    have : r.y + dy + r.h = (r.y + r.h) + dy := by omega
    rw [this]
    exact dot_shift_coords nx ny dx dy r.x (r.y + r.h)
  have hc4 : Polyline.dot nx ny ⟨(shiftRect dx dy r).x + (shiftRect dx dy r).w, (shiftRect dx dy r).y + (shiftRect dx dy r).h⟩ =
      Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ + (nx * dx + ny * dy) := by
    dsimp only [shiftRect]
    have hx : r.x + dx + r.w = (r.x + r.w) + dx := by omega
    have hy : r.y + dy + r.h = (r.y + r.h) + dy := by omega
    rw [hx, hy]
    exact dot_shift_coords nx ny dx dy (r.x + r.w) (r.y + r.h)
  unfold Polyline.minCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem maxCorner_shiftRect (nx ny dx dy : Int) (r : Rect) :
    Polyline.maxCorner nx ny (shiftRect dx dy r) = Polyline.maxCorner nx ny r + (nx * dx + ny * dy) := by
  have hc1 : Polyline.dot nx ny ⟨(shiftRect dx dy r).x, (shiftRect dx dy r).y⟩ =
      Polyline.dot nx ny ⟨r.x, r.y⟩ + (nx * dx + ny * dy) := by
    dsimp only [shiftRect]
    exact dot_shift_coords nx ny dx dy r.x r.y
  have hc2 : Polyline.dot nx ny ⟨(shiftRect dx dy r).x + (shiftRect dx dy r).w, (shiftRect dx dy r).y⟩ =
      Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ + (nx * dx + ny * dy) := by
    dsimp only [shiftRect]
    have : r.x + dx + r.w = (r.x + r.w) + dx := by omega
    rw [this]
    exact dot_shift_coords nx ny dx dy (r.x + r.w) r.y
  have hc3 : Polyline.dot nx ny ⟨(shiftRect dx dy r).x, (shiftRect dx dy r).y + (shiftRect dx dy r).h⟩ =
      Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ + (nx * dx + ny * dy) := by
    dsimp only [shiftRect]
    have : r.y + dy + r.h = (r.y + r.h) + dy := by omega
    rw [this]
    exact dot_shift_coords nx ny dx dy r.x (r.y + r.h)
  have hc4 : Polyline.dot nx ny ⟨(shiftRect dx dy r).x + (shiftRect dx dy r).w, (shiftRect dx dy r).y + (shiftRect dx dy r).h⟩ =
      Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ + (nx * dx + ny * dy) := by
    dsimp only [shiftRect]
    have hx : r.x + dx + r.w = (r.x + r.w) + dx := by omega
    have hy : r.y + dy + r.h = (r.y + r.h) + dy := by omega
    rw [hx, hy]
    exact dot_shift_coords nx ny dx dy (r.x + r.w) (r.y + r.h)
  unfold Polyline.maxCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem segMisses_shift (dx dy : Int) (p q : Point) (r : Rect) :
    Polyline.segMisses (shiftPoint dx dy p) (shiftPoint dx dy q) (shiftRect dx dy r) ↔
      Polyline.segMisses p q r := by
  have hnx : (shiftPoint dx dy p).y - (shiftPoint dx dy q).y = p.y - q.y := by
    dsimp only [shiftPoint]; omega
  have hny : (shiftPoint dx dy q).x - (shiftPoint dx dy p).x = q.x - p.x := by
    dsimp only [shiftPoint]; omega
  have hdot : Polyline.dot ((shiftPoint dx dy p).y - (shiftPoint dx dy q).y)
      ((shiftPoint dx dy q).x - (shiftPoint dx dy p).x) (shiftPoint dx dy p) =
      Polyline.dot (p.y - q.y) (q.x - p.x) p + ((p.y - q.y) * dx + (q.x - p.x) * dy) := by
    rw [hnx, hny]
    exact dot_shiftPoint (p.y - q.y) (q.x - p.x) dx dy p
  have hmin : Polyline.minCorner ((shiftPoint dx dy p).y - (shiftPoint dx dy q).y)
      ((shiftPoint dx dy q).x - (shiftPoint dx dy p).x) (shiftRect dx dy r) =
      Polyline.minCorner (p.y - q.y) (q.x - p.x) r + ((p.y - q.y) * dx + (q.x - p.x) * dy) := by
    rw [hnx, hny]
    exact minCorner_shiftRect (p.y - q.y) (q.x - p.x) dx dy r
  have hmax : Polyline.maxCorner ((shiftPoint dx dy p).y - (shiftPoint dx dy q).y)
      ((shiftPoint dx dy q).x - (shiftPoint dx dy p).x) (shiftRect dx dy r) =
      Polyline.maxCorner (p.y - q.y) (q.x - p.x) r + ((p.y - q.y) * dx + (q.x - p.x) * dy) := by
    rw [hnx, hny]
    exact maxCorner_shiftRect (p.y - q.y) (q.x - p.x) dx dy r
  have hne : (shiftPoint dx dy p ≠ shiftPoint dx dy q) ↔ (p ≠ q) :=
    shiftPoint_ne_iff dx dy p q
  unfold Polyline.segMisses
  rw [hdot, hmin, hmax, hne]
  dsimp only [shiftPoint, shiftRect]
  constructor
  · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; left; omega
    · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
      · left; omega
      · right; omega
  · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; left; omega
    · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
      · left; omega
      · right; omega

theorem shiftRect_dims (dx dy : Int) (r : Rect) :
    (0 < (shiftRect dx dy r).w ∧ 0 < (shiftRect dx dy r).h) ↔ (0 < r.w ∧ 0 < r.h) := by
  dsimp only [shiftRect]; omega

theorem dot_orient_BT_coords (nx ny h x y : Int) :
    Polyline.dot (-nx) ny ⟨x, h - y⟩ = - Polyline.dot nx ny ⟨x, y⟩ + ny * h := by
  unfold Polyline.dot
  dsimp only
  rw [Int.neg_mul, Int.mul_sub]
  omega

theorem dot_orient_LR_coords (nx ny x y : Int) :
    Polyline.dot (-ny) (-nx) ⟨y, x⟩ = - Polyline.dot nx ny ⟨x, y⟩ := by
  unfold Polyline.dot
  dsimp only
  rw [Int.neg_mul, Int.neg_mul]
  omega

theorem dot_orient_RL_coords (nx ny h x y : Int) :
    Polyline.dot (-ny) nx ⟨h - y, x⟩ = Polyline.dot nx ny ⟨x, y⟩ - ny * h := by
  unfold Polyline.dot
  dsimp only
  rw [Int.neg_mul, Int.mul_sub]
  omega

theorem minCorner_orient_BT (nx ny h : Int) (r : Rect) :
    Polyline.minCorner (-nx) ny (orientRect .BT h r) =
      - Polyline.maxCorner nx ny r + ny * h := by
  have hc1 : Polyline.dot (-nx) ny ⟨(orientRect .BT h r).x, (orientRect .BT h r).y⟩ =
      - Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ + ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h = h - (r.y + r.h) := by omega
    rw [this]
    exact dot_orient_BT_coords nx ny h r.x (r.y + r.h)
  have hc2 : Polyline.dot (-nx) ny ⟨(orientRect .BT h r).x + (orientRect .BT h r).w, (orientRect .BT h r).y⟩ =
      - Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ + ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h = h - (r.y + r.h) := by omega
    rw [this]
    exact dot_orient_BT_coords nx ny h (r.x + r.w) (r.y + r.h)
  have hc3 : Polyline.dot (-nx) ny ⟨(orientRect .BT h r).x, (orientRect .BT h r).y + (orientRect .BT h r).h⟩ =
      - Polyline.dot nx ny ⟨r.x, r.y⟩ + ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h + r.h = h - r.y := by omega
    rw [this]
    exact dot_orient_BT_coords nx ny h r.x r.y
  have hc4 : Polyline.dot (-nx) ny ⟨(orientRect .BT h r).x + (orientRect .BT h r).w, (orientRect .BT h r).y + (orientRect .BT h r).h⟩ =
      - Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ + ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h + r.h = h - r.y := by omega
    rw [this]
    exact dot_orient_BT_coords nx ny h (r.x + r.w) r.y
  unfold Polyline.minCorner Polyline.maxCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem maxCorner_orient_BT (nx ny h : Int) (r : Rect) :
    Polyline.maxCorner (-nx) ny (orientRect .BT h r) =
      - Polyline.minCorner nx ny r + ny * h := by
  have hc1 : Polyline.dot (-nx) ny ⟨(orientRect .BT h r).x, (orientRect .BT h r).y⟩ =
      - Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ + ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h = h - (r.y + r.h) := by omega
    rw [this]
    exact dot_orient_BT_coords nx ny h r.x (r.y + r.h)
  have hc2 : Polyline.dot (-nx) ny ⟨(orientRect .BT h r).x + (orientRect .BT h r).w, (orientRect .BT h r).y⟩ =
      - Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ + ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h = h - (r.y + r.h) := by omega
    rw [this]
    exact dot_orient_BT_coords nx ny h (r.x + r.w) (r.y + r.h)
  have hc3 : Polyline.dot (-nx) ny ⟨(orientRect .BT h r).x, (orientRect .BT h r).y + (orientRect .BT h r).h⟩ =
      - Polyline.dot nx ny ⟨r.x, r.y⟩ + ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h + r.h = h - r.y := by omega
    rw [this]
    exact dot_orient_BT_coords nx ny h r.x r.y
  have hc4 : Polyline.dot (-nx) ny ⟨(orientRect .BT h r).x + (orientRect .BT h r).w, (orientRect .BT h r).y + (orientRect .BT h r).h⟩ =
      - Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ + ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h + r.h = h - r.y := by omega
    rw [this]
    exact dot_orient_BT_coords nx ny h (r.x + r.w) r.y
  unfold Polyline.minCorner Polyline.maxCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem minCorner_orient_LR (nx ny h : Int) (r : Rect) :
    Polyline.minCorner (-ny) (-nx) (orientRect .LR h r) =
      - Polyline.maxCorner nx ny r := by
  have hc1 : Polyline.dot (-ny) (-nx) ⟨(orientRect .LR h r).x, (orientRect .LR h r).y⟩ =
      - Polyline.dot nx ny ⟨r.x, r.y⟩ := by
    dsimp only [orientRect]
    exact dot_orient_LR_coords nx ny r.x r.y
  have hc2 : Polyline.dot (-ny) (-nx) ⟨(orientRect .LR h r).x + (orientRect .LR h r).w, (orientRect .LR h r).y⟩ =
      - Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ := by
    dsimp only [orientRect]
    exact dot_orient_LR_coords nx ny r.x (r.y + r.h)
  have hc3 : Polyline.dot (-ny) (-nx) ⟨(orientRect .LR h r).x, (orientRect .LR h r).y + (orientRect .LR h r).h⟩ =
      - Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ := by
    dsimp only [orientRect]
    exact dot_orient_LR_coords nx ny (r.x + r.w) r.y
  have hc4 : Polyline.dot (-ny) (-nx) ⟨(orientRect .LR h r).x + (orientRect .LR h r).w, (orientRect .LR h r).y + (orientRect .LR h r).h⟩ =
      - Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ := by
    dsimp only [orientRect]
    exact dot_orient_LR_coords nx ny (r.x + r.w) (r.y + r.h)
  unfold Polyline.minCorner Polyline.maxCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem maxCorner_orient_LR (nx ny h : Int) (r : Rect) :
    Polyline.maxCorner (-ny) (-nx) (orientRect .LR h r) =
      - Polyline.minCorner nx ny r := by
  have hc1 : Polyline.dot (-ny) (-nx) ⟨(orientRect .LR h r).x, (orientRect .LR h r).y⟩ =
      - Polyline.dot nx ny ⟨r.x, r.y⟩ := by
    dsimp only [orientRect]
    exact dot_orient_LR_coords nx ny r.x r.y
  have hc2 : Polyline.dot (-ny) (-nx) ⟨(orientRect .LR h r).x + (orientRect .LR h r).w, (orientRect .LR h r).y⟩ =
      - Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ := by
    dsimp only [orientRect]
    exact dot_orient_LR_coords nx ny r.x (r.y + r.h)
  have hc3 : Polyline.dot (-ny) (-nx) ⟨(orientRect .LR h r).x, (orientRect .LR h r).y + (orientRect .LR h r).h⟩ =
      - Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ := by
    dsimp only [orientRect]
    exact dot_orient_LR_coords nx ny (r.x + r.w) r.y
  have hc4 : Polyline.dot (-ny) (-nx) ⟨(orientRect .LR h r).x + (orientRect .LR h r).w, (orientRect .LR h r).y + (orientRect .LR h r).h⟩ =
      - Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ := by
    dsimp only [orientRect]
    exact dot_orient_LR_coords nx ny (r.x + r.w) (r.y + r.h)
  unfold Polyline.minCorner Polyline.maxCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem minCorner_orient_RL (nx ny h : Int) (r : Rect) :
    Polyline.minCorner (-ny) nx (orientRect .RL h r) =
      Polyline.minCorner nx ny r - ny * h := by
  have hc1 : Polyline.dot (-ny) nx ⟨(orientRect .RL h r).x, (orientRect .RL h r).y⟩ =
      Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ - ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h = h - (r.y + r.h) := by omega
    rw [this]
    exact dot_orient_RL_coords nx ny h r.x (r.y + r.h)
  have hc2 : Polyline.dot (-ny) nx ⟨(orientRect .RL h r).x + (orientRect .RL h r).w, (orientRect .RL h r).y⟩ =
      Polyline.dot nx ny ⟨r.x, r.y⟩ - ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h + r.h = h - r.y := by omega
    rw [this]
    exact dot_orient_RL_coords nx ny h r.x r.y
  have hc3 : Polyline.dot (-ny) nx ⟨(orientRect .RL h r).x, (orientRect .RL h r).y + (orientRect .RL h r).h⟩ =
      Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ - ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h = h - (r.y + r.h) := by omega
    rw [this]
    exact dot_orient_RL_coords nx ny h (r.x + r.w) (r.y + r.h)
  have hc4 : Polyline.dot (-ny) nx ⟨(orientRect .RL h r).x + (orientRect .RL h r).w, (orientRect .RL h r).y + (orientRect .RL h r).h⟩ =
      Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ - ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h + r.h = h - r.y := by omega
    rw [this]
    exact dot_orient_RL_coords nx ny h (r.x + r.w) r.y
  unfold Polyline.minCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem maxCorner_orient_RL (nx ny h : Int) (r : Rect) :
    Polyline.maxCorner (-ny) nx (orientRect .RL h r) =
      Polyline.maxCorner nx ny r - ny * h := by
  have hc1 : Polyline.dot (-ny) nx ⟨(orientRect .RL h r).x, (orientRect .RL h r).y⟩ =
      Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ - ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h = h - (r.y + r.h) := by omega
    rw [this]
    exact dot_orient_RL_coords nx ny h r.x (r.y + r.h)
  have hc2 : Polyline.dot (-ny) nx ⟨(orientRect .RL h r).x + (orientRect .RL h r).w, (orientRect .RL h r).y⟩ =
      Polyline.dot nx ny ⟨r.x, r.y⟩ - ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h + r.h = h - r.y := by omega
    rw [this]
    exact dot_orient_RL_coords nx ny h r.x r.y
  have hc3 : Polyline.dot (-ny) nx ⟨(orientRect .RL h r).x, (orientRect .RL h r).y + (orientRect .RL h r).h⟩ =
      Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ - ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h = h - (r.y + r.h) := by omega
    rw [this]
    exact dot_orient_RL_coords nx ny h (r.x + r.w) (r.y + r.h)
  have hc4 : Polyline.dot (-ny) nx ⟨(orientRect .RL h r).x + (orientRect .RL h r).w, (orientRect .RL h r).y + (orientRect .RL h r).h⟩ =
      Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ - ny * h := by
    dsimp only [orientRect]
    have : h - r.y - r.h + r.h = h - r.y := by omega
    rw [this]
    exact dot_orient_RL_coords nx ny h (r.x + r.w) r.y
  unfold Polyline.maxCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem segMisses_orient (d : Direction) (h : Int) (p q : Point) (r : Rect) :
    Polyline.segMisses (orientPoint d h p) (orientPoint d h q) (orientRect d h r) ↔
      Polyline.segMisses p q r := by
  cases d with
  | TB => rfl
  | BT =>
    have hnx : (orientPoint .BT h p).y - (orientPoint .BT h q).y = -(p.y - q.y) := by
      dsimp only [orientPoint]; omega
    have hny : (orientPoint .BT h q).x - (orientPoint .BT h p).x = q.x - p.x := rfl
    have hdot : Polyline.dot ((orientPoint .BT h p).y - (orientPoint .BT h q).y)
        ((orientPoint .BT h q).x - (orientPoint .BT h p).x) (orientPoint .BT h p) =
        - Polyline.dot (p.y - q.y) (q.x - p.x) p + (q.x - p.x) * h := by
      rw [hnx, hny]
      exact dot_orient_BT_coords (p.y - q.y) (q.x - p.x) h p.x p.y
    have hmin : Polyline.minCorner ((orientPoint .BT h p).y - (orientPoint .BT h q).y)
        ((orientPoint .BT h q).x - (orientPoint .BT h p).x) (orientRect .BT h r) =
        - Polyline.maxCorner (p.y - q.y) (q.x - p.x) r + (q.x - p.x) * h := by
      rw [hnx, hny]
      exact minCorner_orient_BT (p.y - q.y) (q.x - p.x) h r
    have hmax : Polyline.maxCorner ((orientPoint .BT h p).y - (orientPoint .BT h q).y)
        ((orientPoint .BT h q).x - (orientPoint .BT h p).x) (orientRect .BT h r) =
        - Polyline.minCorner (p.y - q.y) (q.x - p.x) r + (q.x - p.x) * h := by
      rw [hnx, hny]
      exact maxCorner_orient_BT (p.y - q.y) (q.x - p.x) h r
    have hne : (orientPoint .BT h p ≠ orientPoint .BT h q) ↔ (p ≠ q) :=
      orientPoint_ne_iff .BT h p q
    unfold Polyline.segMisses
    rw [hdot, hmin, hmax, hne]
    dsimp only [orientPoint, orientRect]
    constructor
    · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
      · left; omega
      · right; left; omega
      · right; right; right; left; omega
      · right; right; left; omega
      · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
        · right; omega
        · left; omega
    · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
      · left; omega
      · right; left; omega
      · right; right; right; left; omega
      · right; right; left; omega
      · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
        · right; omega
        · left; omega
  | LR =>
    have hdot : Polyline.dot ((orientPoint .LR h p).y - (orientPoint .LR h q).y)
        ((orientPoint .LR h q).x - (orientPoint .LR h p).x) (orientPoint .LR h p) =
        - Polyline.dot (p.y - q.y) (q.x - p.x) p := by
      have hnx : (orientPoint .LR h p).y - (orientPoint .LR h q).y = -(q.x - p.x) := by
        dsimp only [orientPoint]; omega
      have hny : (orientPoint .LR h q).x - (orientPoint .LR h p).x = -(p.y - q.y) := by
        dsimp only [orientPoint]; omega
      rw [hnx, hny]
      exact dot_orient_LR_coords (p.y - q.y) (q.x - p.x) p.x p.y
    have hmin : Polyline.minCorner ((orientPoint .LR h p).y - (orientPoint .LR h q).y)
        ((orientPoint .LR h q).x - (orientPoint .LR h p).x) (orientRect .LR h r) =
        - Polyline.maxCorner (p.y - q.y) (q.x - p.x) r := by
      have hnx : (orientPoint .LR h p).y - (orientPoint .LR h q).y = -(q.x - p.x) := by
        dsimp only [orientPoint]; omega
      have hny : (orientPoint .LR h q).x - (orientPoint .LR h p).x = -(p.y - q.y) := by
        dsimp only [orientPoint]; omega
      rw [hnx, hny]
      exact minCorner_orient_LR (p.y - q.y) (q.x - p.x) h r
    have hmax : Polyline.maxCorner ((orientPoint .LR h p).y - (orientPoint .LR h q).y)
        ((orientPoint .LR h q).x - (orientPoint .LR h p).x) (orientRect .LR h r) =
        - Polyline.minCorner (p.y - q.y) (q.x - p.x) r := by
      have hnx : (orientPoint .LR h p).y - (orientPoint .LR h q).y = -(q.x - p.x) := by
        dsimp only [orientPoint]; omega
      have hny : (orientPoint .LR h q).x - (orientPoint .LR h p).x = -(p.y - q.y) := by
        dsimp only [orientPoint]; omega
      rw [hnx, hny]
      exact maxCorner_orient_LR (p.y - q.y) (q.x - p.x) h r
    have hne : (orientPoint .LR h p ≠ orientPoint .LR h q) ↔ (p ≠ q) :=
      orientPoint_ne_iff .LR h p q
    unfold Polyline.segMisses
    rw [hdot, hmin, hmax, hne]
    dsimp only [orientPoint, orientRect]
    constructor
    · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
      · right; right; left; omega
      · right; right; right; left; omega
      · left; omega
      · right; left; omega
      · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
        · right; omega
        · left; omega
    · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
      · right; right; left; omega
      · right; right; right; left; omega
      · left; omega
      · right; left; omega
      · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
        · right; omega
        · left; omega
  | RL =>
    have hdot : Polyline.dot ((orientPoint .RL h p).y - (orientPoint .RL h q).y)
        ((orientPoint .RL h q).x - (orientPoint .RL h p).x) (orientPoint .RL h p) =
        Polyline.dot (p.y - q.y) (q.x - p.x) p - (q.x - p.x) * h := by
      have hnx : (orientPoint .RL h p).y - (orientPoint .RL h q).y = -(q.x - p.x) := by
        dsimp only [orientPoint]; omega
      have hny : (orientPoint .RL h q).x - (orientPoint .RL h p).x = p.y - q.y := by
        dsimp only [orientPoint]; omega
      rw [hnx, hny]
      exact dot_orient_RL_coords (p.y - q.y) (q.x - p.x) h p.x p.y
    have hmin : Polyline.minCorner ((orientPoint .RL h p).y - (orientPoint .RL h q).y)
        ((orientPoint .RL h q).x - (orientPoint .RL h p).x) (orientRect .RL h r) =
        Polyline.minCorner (p.y - q.y) (q.x - p.x) r - (q.x - p.x) * h := by
      have hnx : (orientPoint .RL h p).y - (orientPoint .RL h q).y = -(q.x - p.x) := by
        dsimp only [orientPoint]; omega
      have hny : (orientPoint .RL h q).x - (orientPoint .RL h p).x = p.y - q.y := by
        dsimp only [orientPoint]; omega
      rw [hnx, hny]
      exact minCorner_orient_RL (p.y - q.y) (q.x - p.x) h r
    have hmax : Polyline.maxCorner ((orientPoint .RL h p).y - (orientPoint .RL h q).y)
        ((orientPoint .RL h q).x - (orientPoint .RL h p).x) (orientRect .RL h r) =
        Polyline.maxCorner (p.y - q.y) (q.x - p.x) r - (q.x - p.x) * h := by
      have hnx : (orientPoint .RL h p).y - (orientPoint .RL h q).y = -(q.x - p.x) := by
        dsimp only [orientPoint]; omega
      have hny : (orientPoint .RL h q).x - (orientPoint .RL h p).x = p.y - q.y := by
        dsimp only [orientPoint]; omega
      rw [hnx, hny]
      exact maxCorner_orient_RL (p.y - q.y) (q.x - p.x) h r
    have hne : (orientPoint .RL h p ≠ orientPoint .RL h q) ↔ (p ≠ q) :=
      orientPoint_ne_iff .RL h p q
    unfold Polyline.segMisses
    rw [hdot, hmin, hmax, hne]
    dsimp only [orientPoint, orientRect]
    constructor
    · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
      · right; right; right; left; omega
      · right; right; left; omega
      · left; omega
      · right; left; omega
      · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
        · left; omega
        · right; omega
    · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
      · right; right; left; omega
      · right; right; right; left; omega
      · right; left; omega
      · left; omega
      · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
        · left; omega
        · right; omega

theorem orientRect_dims (d : Direction) (h : Int) (r : Rect) :
    (0 < (orientRect d h r).w ∧ 0 < (orientRect d h r).h) ↔ (0 < r.w ∧ 0 < r.h) := by
  cases d <;> (dsimp only [orientRect]; omega)

theorem dot_swap (p q : Point) :
    Polyline.dot (p.y - q.y) (q.x - p.x) q = Polyline.dot (p.y - q.y) (q.x - p.x) p := by
  unfold Polyline.dot
  have h1 : (p.y - q.y) * q.x = p.y * q.x - q.y * q.x := Int.sub_mul p.y q.y q.x
  have h2 : (q.x - p.x) * q.y = q.x * q.y - p.x * q.y := Int.sub_mul q.x p.x q.y
  have h3 : (p.y - q.y) * p.x = p.y * p.x - q.y * p.x := Int.sub_mul p.y q.y p.x
  have h4 : (q.x - p.x) * p.y = q.x * p.y - p.x * p.y := Int.sub_mul q.x p.x p.y
  have hcomm1 : p.y * p.x = p.x * p.y := Int.mul_comm p.y p.x
  have hcomm2 : q.y * q.x = q.x * q.y := Int.mul_comm q.y q.x
  have hcomm3 : p.y * q.x = q.x * p.y := Int.mul_comm p.y q.x
  have hcomm4 : p.x * q.y = q.y * p.x := Int.mul_comm p.x q.y
  omega

theorem dot_neg_neg (nx ny x y : Int) :
    Polyline.dot (-nx) (-ny) ⟨x, y⟩ = - Polyline.dot nx ny ⟨x, y⟩ := by
  unfold Polyline.dot
  dsimp only
  rw [Int.neg_mul, Int.neg_mul]
  omega

theorem minCorner_neg_neg (nx ny : Int) (r : Rect) :
    Polyline.minCorner (-nx) (-ny) r = - Polyline.maxCorner nx ny r := by
  have hc1 : Polyline.dot (-nx) (-ny) ⟨r.x, r.y⟩ = - Polyline.dot nx ny ⟨r.x, r.y⟩ :=
    dot_neg_neg nx ny r.x r.y
  have hc2 : Polyline.dot (-nx) (-ny) ⟨r.x + r.w, r.y⟩ = - Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ :=
    dot_neg_neg nx ny (r.x + r.w) r.y
  have hc3 : Polyline.dot (-nx) (-ny) ⟨r.x, r.y + r.h⟩ = - Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ :=
    dot_neg_neg nx ny r.x (r.y + r.h)
  have hc4 : Polyline.dot (-nx) (-ny) ⟨r.x + r.w, r.y + r.h⟩ = - Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ :=
    dot_neg_neg nx ny (r.x + r.w) (r.y + r.h)
  unfold Polyline.minCorner Polyline.maxCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem maxCorner_neg_neg (nx ny : Int) (r : Rect) :
    Polyline.maxCorner (-nx) (-ny) r = - Polyline.minCorner nx ny r := by
  have hc1 : Polyline.dot (-nx) (-ny) ⟨r.x, r.y⟩ = - Polyline.dot nx ny ⟨r.x, r.y⟩ :=
    dot_neg_neg nx ny r.x r.y
  have hc2 : Polyline.dot (-nx) (-ny) ⟨r.x + r.w, r.y⟩ = - Polyline.dot nx ny ⟨r.x + r.w, r.y⟩ :=
    dot_neg_neg nx ny (r.x + r.w) r.y
  have hc3 : Polyline.dot (-nx) (-ny) ⟨r.x, r.y + r.h⟩ = - Polyline.dot nx ny ⟨r.x, r.y + r.h⟩ :=
    dot_neg_neg nx ny r.x (r.y + r.h)
  have hc4 : Polyline.dot (-nx) (-ny) ⟨r.x + r.w, r.y + r.h⟩ = - Polyline.dot nx ny ⟨r.x + r.w, r.y + r.h⟩ :=
    dot_neg_neg nx ny (r.x + r.w) (r.y + r.h)
  unfold Polyline.minCorner Polyline.maxCorner
  rw [hc1, hc2, hc3, hc4]
  omega

theorem segMisses_comm (p q : Point) (r : Rect) :
    Polyline.segMisses q p r ↔ Polyline.segMisses p q r := by
  have hnx : q.y - p.y = -(p.y - q.y) := by omega
  have hny : p.x - q.x = -(q.x - p.x) := by omega
  have hdot : Polyline.dot (q.y - p.y) (p.x - q.x) q =
      - Polyline.dot (p.y - q.y) (q.x - p.x) p := by
    rw [hnx, hny]
    have h1 := dot_neg_neg (p.y - q.y) (q.x - p.x) q.x q.y
    rw [dot_swap p q] at h1
    exact h1
  have hmin : Polyline.minCorner (q.y - p.y) (p.x - q.x) r =
      - Polyline.maxCorner (p.y - q.y) (q.x - p.x) r := by
    rw [hnx, hny]
    exact minCorner_neg_neg (p.y - q.y) (q.x - p.x) r
  have hmax : Polyline.maxCorner (q.y - p.y) (p.x - q.x) r =
      - Polyline.minCorner (p.y - q.y) (q.x - p.x) r := by
    rw [hnx, hny]
    exact maxCorner_neg_neg (p.y - q.y) (q.x - p.x) r
  have hne : (q ≠ p) ↔ (p ≠ q) := ⟨Ne.symm, Ne.symm⟩
  unfold Polyline.segMisses
  rw [hdot, hmin, hmax, hne]
  constructor
  · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; left; omega
    · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
      · right; omega
      · left; omega
  · rintro (h1 | h2 | h3 | h4 | ⟨hne, h5⟩)
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; left; omega
    · right; right; right; right; refine ⟨hne, ?_⟩; rcases h5 with h5a | h5b
      · right; omega
      · left; omega

theorem getLast?_snoc : ∀ (xs : List Point) (x : Point), (xs ++ [x]).getLast? = some x
  | [], x => rfl
  | [a], x => rfl
  | a :: b :: rest, x => by
    simp only [List.cons_append]
    rw [List.getLast?_cons_cons]
    exact getLast?_snoc (b :: rest) x

theorem getLast?_eq_some : ∀ (b : Point) (rest : List Point), ∃ z, (b :: rest).getLast? = some z
  | b, [] => ⟨b, rfl⟩
  | b, c :: cs => by
    rw [List.getLast?_cons_cons]
    exact getLast?_eq_some c cs

theorem pairsAll_snoc (P : Point → Point → Prop) :
    ∀ (l : List Point) (x : Point),
      pairsAll P (l ++ [x]) ↔
        match l.getLast? with
        | none => True
        | some a => pairsAll P l ∧ P a x
  | [], x => by simp [pairsAll]
  | [a], x => by simp [pairsAll]
  | a :: b :: rest, x => by
    have ih := pairsAll_snoc P (b :: rest) x
    obtain ⟨z, hz⟩ := getLast?_eq_some b rest
    rw [List.getLast?_cons_cons, hz]
    rw [hz] at ih
    change (P a b ∧ pairsAll P ((b :: rest) ++ [x])) ↔
      ((P a b ∧ pairsAll P (b :: rest)) ∧ P z x)
    rw [ih]
    constructor
    · rintro ⟨hab, hrest, hzx⟩
      exact ⟨⟨hab, hrest⟩, hzx⟩
    · rintro ⟨⟨hab, hrest⟩, hzx⟩
      exact ⟨hab, hrest, hzx⟩

theorem pairsAll_reverse (P : Point → Point → Prop) (hP : ∀ a b, P a b ↔ P b a) :
    ∀ l : List Point, pairsAll P l.reverse ↔ pairsAll P l
  | [] => by simp [pairsAll]
  | [a] => by simp [pairsAll]
  | a :: b :: rest => by
    have ih := pairsAll_reverse P hP (b :: rest)
    rw [List.reverse_cons, pairsAll_snoc]
    have hlast : (b :: rest).reverse.getLast? = some b := by
      rw [List.reverse_cons]
      exact getLast?_snoc rest.reverse b
    rw [hlast]
    dsimp only
    rw [ih]
    simp only [pairsAll]
    rw [hP b a]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

theorem allSegsMiss_map (f : Point → Point) (g : Rect → Rect)
    (h_seg : ∀ p q r, Polyline.segMisses (f p) (f q) (g r) ↔ Polyline.segMisses p q r) :
    ∀ (points : List Point) (r : Rect),
      Polyline.allSegsMiss (points.map f) (g r) ↔ Polyline.allSegsMiss points r
  | [], _ => by simp [Polyline.allSegsMiss]
  | [_], _ => by simp [Polyline.allSegsMiss]
  | p :: q :: rest, r => by
    have ih := allSegsMiss_map f g h_seg (q :: rest) r
    change (Polyline.segMisses (f p) (f q) (g r) ∧ Polyline.allSegsMiss ((q :: rest).map f) (g r)) ↔
      (Polyline.segMisses p q r ∧ Polyline.allSegsMiss (q :: rest) r)
    rw [h_seg, ih]

theorem hitsRect_map (f : Point → Point) (g : Rect → Rect)
    (h_seg : ∀ p q r, Polyline.segMisses (f p) (f q) (g r) ↔ Polyline.segMisses p q r)
    (h_pos : ∀ r, (0 < (g r).w ∧ 0 < (g r).h) ↔ (0 < r.w ∧ 0 < r.h))
    (points : List Point) (r : Rect) :
    Polyline.hitsRect (points.map f) (g r) ↔ Polyline.hitsRect points r := by
  have hm := allSegsMiss_map f g h_seg points r
  have hp := h_pos r
  unfold Polyline.hitsRect
  constructor
  · rintro ⟨hw, hh, hmiss⟩
    have ⟨hw', hh'⟩ := hp.mp ⟨hw, hh⟩
    exact ⟨hw', hh', fun h => hmiss (hm.mpr h)⟩
  · rintro ⟨hw, hh, hmiss⟩
    have ⟨hw', hh'⟩ := hp.mpr ⟨hw, hh⟩
    exact ⟨hw', hh', fun h => hmiss (hm.mp h)⟩

theorem not_hitsRect_map (f : Point → Point) (g : Rect → Rect)
    (h_seg : ∀ p q r, Polyline.segMisses (f p) (f q) (g r) ↔ Polyline.segMisses p q r)
    (h_pos : ∀ r, (0 < (g r).w ∧ 0 < (g r).h) ↔ (0 < r.w ∧ 0 < r.h))
    (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect (points.map f) (g r) ↔ ¬ Polyline.hitsRect points r := by
  rw [hitsRect_map f g h_seg h_pos points r]

theorem not_hitsRect_map_of_not_hitsRect (f : Point → Point) (g : Rect → Rect)
    (h_seg : ∀ p q r, Polyline.segMisses (f p) (f q) (g r) ↔ Polyline.segMisses p q r)
    (h_pos : ∀ r, (0 < (g r).w ∧ 0 < (g r).h) ↔ (0 < r.w ∧ 0 < r.h))
    (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect points r → ¬ Polyline.hitsRect (points.map f) (g r) := by
  intro hmiss
  rw [not_hitsRect_map f g h_seg h_pos points r]
  exact hmiss

theorem allSegsMiss_shift (dx dy : Int) (points : List Point) (r : Rect) :
    Polyline.allSegsMiss (points.map (shiftPoint dx dy)) (shiftRect dx dy r) ↔
      Polyline.allSegsMiss points r :=
  allSegsMiss_map (shiftPoint dx dy) (shiftRect dx dy) (segMisses_shift dx dy) points r

theorem hitsRect_shift (dx dy : Int) (points : List Point) (r : Rect) :
    Polyline.hitsRect (points.map (shiftPoint dx dy)) (shiftRect dx dy r) ↔
      Polyline.hitsRect points r :=
  hitsRect_map (shiftPoint dx dy) (shiftRect dx dy) (segMisses_shift dx dy) (shiftRect_dims dx dy) points r

theorem not_hitsRect_shift_iff (dx dy : Int) (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect (points.map (shiftPoint dx dy)) (shiftRect dx dy r) ↔
      ¬ Polyline.hitsRect points r :=
  not_hitsRect_map (shiftPoint dx dy) (shiftRect dx dy) (segMisses_shift dx dy) (shiftRect_dims dx dy) points r

theorem not_hitsRect_shift (dx dy : Int) (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect points r →
      ¬ Polyline.hitsRect (points.map (shiftPoint dx dy)) (shiftRect dx dy r) :=
  not_hitsRect_map_of_not_hitsRect (shiftPoint dx dy) (shiftRect dx dy) (segMisses_shift dx dy) (shiftRect_dims dx dy) points r

theorem allSegsMiss_orient (d : Direction) (h : Int) (points : List Point) (r : Rect) :
    Polyline.allSegsMiss (points.map (orientPoint d h)) (orientRect d h r) ↔
      Polyline.allSegsMiss points r :=
  allSegsMiss_map (orientPoint d h) (orientRect d h) (segMisses_orient d h) points r

theorem hitsRect_orient (d : Direction) (h : Int) (points : List Point) (r : Rect) :
    Polyline.hitsRect (points.map (orientPoint d h)) (orientRect d h r) ↔
      Polyline.hitsRect points r :=
  hitsRect_map (orientPoint d h) (orientRect d h) (segMisses_orient d h) (orientRect_dims d h) points r

theorem not_hitsRect_orient_iff (d : Direction) (h : Int) (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect (points.map (orientPoint d h)) (orientRect d h r) ↔
      ¬ Polyline.hitsRect points r :=
  not_hitsRect_map (orientPoint d h) (orientRect d h) (segMisses_orient d h) (orientRect_dims d h) points r

theorem not_hitsRect_orient (d : Direction) (h : Int) (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect points r →
      ¬ Polyline.hitsRect (points.map (orientPoint d h)) (orientRect d h r) :=
  not_hitsRect_map_of_not_hitsRect (orientPoint d h) (orientRect d h) (segMisses_orient d h) (orientRect_dims d h) points r

theorem allSegsMiss_reverse (points : List Point) (r : Rect) :
    Polyline.allSegsMiss points.reverse r ↔ Polyline.allSegsMiss points r := by
  rw [allSegsMiss_iff r points.reverse, allSegsMiss_iff r points]
  exact pairsAll_reverse (fun p q => Polyline.segMisses p q r) (fun p q => (segMisses_comm p q r).symm) points

theorem hitsRect_reverse (points : List Point) (r : Rect) :
    Polyline.hitsRect points.reverse r ↔ Polyline.hitsRect points r := by
  unfold Polyline.hitsRect
  rw [allSegsMiss_reverse]

theorem not_hitsRect_reverse_iff (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect points.reverse r ↔ ¬ Polyline.hitsRect points r := by
  rw [hitsRect_reverse]

theorem not_hitsRect_reverse (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect points r → ¬ Polyline.hitsRect points.reverse r := by
  intro hmiss
  rw [not_hitsRect_reverse_iff]
  exact hmiss

theorem hitsRect_shift_orient_map (d : Direction) (h dx dy : Int) (points : List Point) (r : Rect) :
    Polyline.hitsRect ((points.map (orientPoint d h)).map (shiftPoint dx dy))
      (shiftRect dx dy (orientRect d h r)) ↔ Polyline.hitsRect points r := by
  rw [hitsRect_shift]
  exact hitsRect_orient d h points r

theorem not_hitsRect_shift_orient_map (d : Direction) (h dx dy : Int) (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect points r →
      ¬ Polyline.hitsRect ((points.map (orientPoint d h)).map (shiftPoint dx dy))
        (shiftRect dx dy (orientRect d h r)) := by
  intro hmiss
  rw [hitsRect_shift_orient_map]
  exact hmiss

theorem hitsRect_shift_orient (d : Direction) (h dx dy : Int) (points : List Point) (r : Rect) :
    Polyline.hitsRect (points.map (fun p => shiftPoint dx dy (orientPoint d h p)))
      (shiftRect dx dy (orientRect d h r)) ↔ Polyline.hitsRect points r := by
  have heq : points.map (fun p => shiftPoint dx dy (orientPoint d h p)) =
      (points.map (orientPoint d h)).map (shiftPoint dx dy) := by
    induction points with
    | nil => rfl
    | cons p rest ih => simp [ih]
  rw [heq]
  exact hitsRect_shift_orient_map d h dx dy points r

theorem not_hitsRect_shift_orient_iff (d : Direction) (h dx dy : Int) (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect (points.map (fun p => shiftPoint dx dy (orientPoint d h p)))
      (shiftRect dx dy (orientRect d h r)) ↔ ¬ Polyline.hitsRect points r := by
  rw [hitsRect_shift_orient]

theorem not_hitsRect_shift_orient (d : Direction) (h dx dy : Int) (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect points r →
      ¬ Polyline.hitsRect (points.map (fun p => shiftPoint dx dy (orientPoint d h p)))
        (shiftRect dx dy (orientRect d h r)) := by
  intro hmiss
  rw [not_hitsRect_shift_orient_iff]
  exact hmiss

theorem hitsRect_shift_orient_reverse (d : Direction) (h dx dy : Int) (points : List Point) (r : Rect) :
    Polyline.hitsRect (points.reverse.map (fun p => shiftPoint dx dy (orientPoint d h p)))
      (shiftRect dx dy (orientRect d h r)) ↔ Polyline.hitsRect points r := by
  rw [hitsRect_shift_orient]
  exact hitsRect_reverse points r

theorem not_hitsRect_shift_orient_reverse (d : Direction) (h dx dy : Int) (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect points r →
      ¬ Polyline.hitsRect (points.reverse.map (fun p => shiftPoint dx dy (orientPoint d h p)))
        (shiftRect dx dy (orientRect d h r)) := by
  intro hmiss
  rw [hitsRect_shift_orient_reverse]
  exact hmiss

theorem hitsRect_reverse_shift_orient (d : Direction) (h dx dy : Int) (points : List Point) (r : Rect) :
    Polyline.hitsRect ((points.map (orientPoint d h)).reverse.map (shiftPoint dx dy))
      (shiftRect dx dy (orientRect d h r)) ↔ Polyline.hitsRect points r := by
  rw [hitsRect_shift]
  rw [hitsRect_reverse]
  exact hitsRect_orient d h points r

theorem not_hitsRect_reverse_shift_orient (d : Direction) (h dx dy : Int) (points : List Point) (r : Rect) :
    ¬ Polyline.hitsRect points r →
      ¬ Polyline.hitsRect ((points.map (orientPoint d h)).reverse.map (shiftPoint dx dy))
        (shiftRect dx dy (orientRect d h r)) := by
  intro hmiss
  rw [hitsRect_reverse_shift_orient]
  exact hmiss

theorem isOrthogonal_shift (dx dy : Int) :
    ∀ (points : List Point),
      Polyline.isOrthogonal (points.map (shiftPoint dx dy)) = true ↔
        Polyline.isOrthogonal points = true
  | [] => by simp [Polyline.isOrthogonal]
  | [_] => by simp [Polyline.isOrthogonal]
  | p :: q :: rest => by
    rw [Polyline.isOrthogonal_cons]
    change ((shiftPoint dx dy p).x = (shiftPoint dx dy q).x ||
        (shiftPoint dx dy p).y = (shiftPoint dx dy q).y) &&
        Polyline.isOrthogonal ((q :: rest).map (shiftPoint dx dy)) = true ↔
      Polyline.isOrthogonal (p :: q :: rest) = true
    rw [Polyline.isOrthogonal_cons]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    have h_pair : ((shiftPoint dx dy p).x = (shiftPoint dx dy q).x ∨
        (shiftPoint dx dy p).y = (shiftPoint dx dy q).y) ↔ (p.x = q.x ∨ p.y = q.y) := by
      dsimp only [shiftPoint]; omega
    rw [h_pair, isOrthogonal_shift dx dy (q :: rest)]

theorem isOrthogonal_orient (d : Direction) (h : Int) :
    ∀ (points : List Point),
      Polyline.isOrthogonal (points.map (orientPoint d h)) = true ↔
        Polyline.isOrthogonal points = true
  | [] => by simp [Polyline.isOrthogonal]
  | [_] => by simp [Polyline.isOrthogonal]
  | p :: q :: rest => by
    rw [Polyline.isOrthogonal_cons]
    change ((orientPoint d h p).x = (orientPoint d h q).x ||
        (orientPoint d h p).y = (orientPoint d h q).y) &&
        Polyline.isOrthogonal ((q :: rest).map (orientPoint d h)) = true ↔
      Polyline.isOrthogonal (p :: q :: rest) = true
    rw [Polyline.isOrthogonal_cons]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    have h_pair : ((orientPoint d h p).x = (orientPoint d h q).x ∨
        (orientPoint d h p).y = (orientPoint d h q).y) ↔ (p.x = q.x ∨ p.y = q.y) := by
      cases d <;> (dsimp only [orientPoint]; omega)
    rw [h_pair, isOrthogonal_orient d h (q :: rest)]

theorem isOrthogonal_reverse (points : List Point) :
    Polyline.isOrthogonal points.reverse = true ↔ Polyline.isOrthogonal points = true := by
  rw [isOrthogonal_iff points.reverse, isOrthogonal_iff points]
  have hsymm : ∀ a b : Point, (a.x = b.x ∨ a.y = b.y) ↔ (b.x = a.x ∨ b.y = a.y) := by
    intro a b; omega
  exact pairsAll_reverse (fun p q => p.x = q.x ∨ p.y = q.y) hsymm points

theorem isOrthogonal_shift_orient (d : Direction) (h dx dy : Int) (points : List Point) :
    Polyline.isOrthogonal (points.map (fun p => shiftPoint dx dy (orientPoint d h p))) = true ↔
      Polyline.isOrthogonal points = true := by
  have heq : points.map (fun p => shiftPoint dx dy (orientPoint d h p)) =
      (points.map (orientPoint d h)).map (shiftPoint dx dy) := by
    induction points with
    | nil => rfl
    | cons p rest ih => simp [ih]
  rw [heq]
  rw [isOrthogonal_shift]
  exact isOrthogonal_orient d h points

theorem isOrthogonal_shift_orient_reverse (d : Direction) (h dx dy : Int) (points : List Point) :
    Polyline.isOrthogonal (points.reverse.map (fun p => shiftPoint dx dy (orientPoint d h p))) = true ↔
      Polyline.isOrthogonal points = true := by
  rw [isOrthogonal_shift_orient]
  exact isOrthogonal_reverse points

theorem onBoundary_shift (dx dy : Int) (p : Point) (r : Rect) :
    Validator.onBoundary (shiftPoint dx dy p) (shiftRect dx dy r) ↔
      Validator.onBoundary p r := by
  unfold Validator.onBoundary
  dsimp only [shiftPoint, shiftRect]
  omega

theorem onBoundary_orient (d : Direction) (h : Int) (p : Point) (r : Rect) :
    Validator.onBoundary (orientPoint d h p) (orientRect d h r) ↔
      Validator.onBoundary p r := by
  cases d with
  | TB => rfl
  | BT =>
    unfold Validator.onBoundary
    dsimp only [orientPoint, orientRect]
    omega
  | LR =>
    unfold Validator.onBoundary
    dsimp only [orientPoint, orientRect]
    omega
  | RL =>
    unfold Validator.onBoundary
    dsimp only [orientPoint, orientRect]
    omega

theorem onBoundary_shift_orient (d : Direction) (h dx dy : Int) (p : Point) (r : Rect) :
    Validator.onBoundary (shiftPoint dx dy (orientPoint d h p)) (shiftRect dx dy (orientRect d h r)) ↔
      Validator.onBoundary p r := by
  rw [onBoundary_shift]
  exact onBoundary_orient d h p r

theorem onSegment_shift (dx dy : Int) (a b p : Point) :
    onSegment (shiftPoint dx dy a) (shiftPoint dx dy b) (shiftPoint dx dy p) ↔ onSegment a b p := by
  unfold onSegment
  rw [shiftPoint_inj, shiftPoint_inj]
  dsimp only [shiftPoint]
  have hminy : min (a.y + dy) (b.y + dy) = min a.y b.y + dy := by omega
  have hmaxy : max (a.y + dy) (b.y + dy) = max a.y b.y + dy := by omega
  have hminx : min (a.x + dx) (b.x + dx) = min a.x b.x + dx := by omega
  have hmaxx : max (a.x + dx) (b.x + dx) = max a.x b.x + dx := by omega
  constructor
  · rintro (rfl | rfl | ⟨hx, hpx, hy1, hy2⟩ | ⟨hy, hpy, hx1, hx2⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · rw [hminy] at hy1
      rw [hmaxy] at hy2
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    · rw [hminx] at hx1
      rw [hmaxx] at hx2
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega⟩))
  · rintro (rfl | rfl | ⟨hx, hpx, hy1, hy2⟩ | ⟨hy, hpy, hx1, hx2⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · rw [hminy, hmaxy]
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    · rw [hminx, hmaxx]
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega⟩))

theorem onSegment_orient (d : Direction) (h : Int) (a b p : Point) :
    onSegment (orientPoint d h a) (orientPoint d h b) (orientPoint d h p) ↔ onSegment a b p := by
  cases d with
  | TB => rfl
  | BT =>
    unfold onSegment
    rw [orientPoint_inj, orientPoint_inj]
    dsimp only [orientPoint]
    have hminy : min (h - a.y) (h - b.y) = h - max a.y b.y := by omega
    have hmaxy : max (h - a.y) (h - b.y) = h - min a.y b.y := by omega
    constructor
    · rintro (rfl | rfl | ⟨hx, hpx, hy1, hy2⟩ | ⟨hy, hpy, hx1, hx2⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rw [hminy] at hy1
        rw [hmaxy] at hy2
        exact Or.inr (Or.inr (Or.inl ⟨hx, hpx, by omega, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hx1, hx2⟩))
    · rintro (rfl | rfl | ⟨hx, hpx, hy1, hy2⟩ | ⟨hy, hpy, hx1, hx2⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rw [hminy, hmaxy]
        exact Or.inr (Or.inr (Or.inl ⟨hx, hpx, by omega, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hx1, hx2⟩))
  | LR =>
    unfold onSegment
    rw [orientPoint_inj, orientPoint_inj]
    dsimp only [orientPoint]
    constructor
    · rintro (rfl | rfl | ⟨hx, hpx, hy1, hy2⟩ | ⟨hy, hpy, hx1, hx2⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨hx, hpx, hy1, hy2⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hy, hpy, hx1, hx2⟩))
    · rintro (rfl | rfl | ⟨hx, hpx, hy1, hy2⟩ | ⟨hy, hpy, hx1, hx2⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨hx, hpx, hy1, hy2⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hy, hpy, hx1, hx2⟩))
  | RL =>
    unfold onSegment
    rw [orientPoint_inj, orientPoint_inj]
    dsimp only [orientPoint]
    have hmin : min (h - a.y) (h - b.y) = h - max a.y b.y := by omega
    have hmax : max (h - a.y) (h - b.y) = h - min a.y b.y := by omega
    constructor
    · rintro (rfl | rfl | ⟨hx, hpx, hy1, hy2⟩ | ⟨hy, hpy, hx1, hx2⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hy1, hy2⟩))
      · rw [hmin] at hx1
        rw [hmax] at hx2
        exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    · rintro (rfl | rfl | ⟨hx, hpx, hy1, hy2⟩ | ⟨hy, hpy, hx1, hx2⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rw [hmin, hmax]
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega⟩))
      · rw [hmin, hmax]
        exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))

theorem onSegment_shift_orient (d : Direction) (h dx dy : Int) (a b p : Point) :
    onSegment (shiftPoint dx dy (orientPoint d h a))
              (shiftPoint dx dy (orientPoint d h b))
              (shiftPoint dx dy (orientPoint d h p)) ↔ onSegment a b p := by
  rw [onSegment_shift]
  exact onSegment_orient d h a b p

theorem onPolyline_map (f : Point → Point)
    (h_seg : ∀ a b p, onSegment (f a) (f b) (f p) ↔ onSegment a b p)
    (h_inj : ∀ p q, f p = f q ↔ p = q) :
    ∀ (pts : List Point) (p : Point),
      onPolyline (pts.map f) (f p) ↔ onPolyline pts p
  | [], _ => by simp [onPolyline]
  | [a], p => by
    simp only [List.map_cons, List.map_nil, onPolyline, h_inj]
  | a :: b :: rest, p => by
    simp only [List.map_cons, onPolyline]
    have ih := onPolyline_map f h_seg h_inj (b :: rest) p
    rw [h_seg]
    exact or_congr Iff.rfl (by simpa only [List.map_cons] using ih)

theorem onPolyline_shift (dx dy : Int) (pts : List Point) (p : Point) :
    onPolyline (pts.map (shiftPoint dx dy)) (shiftPoint dx dy p) ↔ onPolyline pts p :=
  onPolyline_map (shiftPoint dx dy) (onSegment_shift dx dy) (shiftPoint_inj dx dy) pts p

theorem onPolyline_orient (d : Direction) (h : Int) (pts : List Point) (p : Point) :
    onPolyline (pts.map (orientPoint d h)) (orientPoint d h p) ↔ onPolyline pts p :=
  onPolyline_map (orientPoint d h) (onSegment_orient d h) (orientPoint_inj d h) pts p

theorem onPolyline_shift_orient (d : Direction) (h dx dy : Int) (pts : List Point) (p : Point) :
    onPolyline (pts.map (fun q => shiftPoint dx dy (orientPoint d h q)))
               (shiftPoint dx dy (orientPoint d h p)) ↔ onPolyline pts p := by
  have heq : pts.map (fun q => shiftPoint dx dy (orientPoint d h q)) =
      (pts.map (orientPoint d h)).map (shiftPoint dx dy) := by
    induction pts with
    | nil => rfl
    | cons x rest ih => simp [ih]
  rw [heq, onPolyline_shift, onPolyline_orient]

theorem onPolyline_snoc : ∀ (l : List Point) (x p : Point),
    onPolyline (l ++ [x]) p ↔
      match l.getLast? with
      | none => p = x
      | some a => onPolyline l p ∨ onSegment a x p
  | [], x, p => by simp [onPolyline]
  | [a], x, p => by
    simp only [List.cons_append, onPolyline, List.getLast?_singleton]
    constructor
    · rintro (h | rfl)
      · exact Or.inr h
      · exact Or.inr (onSegment_right _ _)
    · rintro (rfl | h)
      · exact Or.inl (onSegment_left _ _)
      · exact Or.inl h
  | a :: b :: rest, x, p => by
    have ih := onPolyline_snoc (b :: rest) x p
    obtain ⟨z, hz⟩ := getLast?_eq_some b rest
    rw [List.getLast?_cons_cons, hz]
    rw [hz] at ih
    change (onSegment a b p ∨ onPolyline ((b :: rest) ++ [x]) p) ↔
      ((onSegment a b p ∨ onPolyline (b :: rest) p) ∨ onSegment z x p)
    rw [ih]
    exact or_assoc.symm

theorem onPolyline_reverse : ∀ (l : List Point) (p : Point),
    onPolyline l.reverse p ↔ onPolyline l p
  | [], p => by simp [onPolyline]
  | [a], p => by simp [onPolyline]
  | a :: b :: rest, p => by
    have ih := onPolyline_reverse (b :: rest) p
    rw [List.reverse_cons, onPolyline_snoc]
    have hlast : (b :: rest).reverse.getLast? = some b := by
      rw [List.reverse_cons]
      exact getLast?_snoc rest.reverse b
    rw [hlast]
    dsimp only
    rw [ih]
    simp only [onPolyline]
    rw [onSegment_comm b a]
    exact or_comm

theorem onPolyline_shift_orient_reverse (d : Direction) (h dx dy : Int) (pts : List Point) (p : Point) :
    onPolyline (pts.reverse.map (fun q => shiftPoint dx dy (orientPoint d h q)))
               (shiftPoint dx dy (orientPoint d h p)) ↔ onPolyline pts p := by
  rw [onPolyline_shift_orient, onPolyline_reverse]

theorem onPolyline_reverse_shift_orient (d : Direction) (h dx dy : Int) (pts : List Point) (p : Point) :
    onPolyline ((pts.map (orientPoint d h)).reverse.map (shiftPoint dx dy))
               (shiftPoint dx dy (orientPoint d h p)) ↔ onPolyline pts p := by
  rw [onPolyline_shift, onPolyline_reverse, onPolyline_orient]

/-- The coordinate along the layout rank axis after orientation. -/
def rankCoord (d : Direction) (p : Point) : Int :=
  match d with
  | .TB | .BT => p.y
  | .LR | .RL => p.x

theorem rankCoord_shiftPoint (dx dy : Int) (d : Direction) (p : Point) :
    rankCoord d (shiftPoint dx dy p) =
      rankCoord d p + (match d with | .TB | .BT => dy | .LR | .RL => dx) := by
  cases d <;> rfl

theorem rankCoord_orientPoint (d : Direction) (h : Int) (p : Point) :
    rankCoord d (orientPoint d h p) =
      match d with
      | .TB => p.y
      | .BT => h - p.y
      | .LR => p.y
      | .RL => h - p.y := by
  cases d <;> rfl

theorem rankCoord_shift_orient (d : Direction) (h dx dy : Int) (p : Point) :
    rankCoord d (shiftPoint dx dy (orientPoint d h p)) =
      match d with
      | .TB => p.y + dy
      | .BT => h - p.y + dy
      | .LR => p.y + dx
      | .RL => h - p.y + dx := by
  cases d <;> rfl

theorem rankCoord_shift_orient_ne_of_y_ne (d : Direction) (h dx dy : Int) {p q : Point}
    (hne : p.y ≠ q.y) :
    rankCoord d (shiftPoint dx dy (orientPoint d h p)) ≠
    rankCoord d (shiftPoint dx dy (orientPoint d h q)) := by
  cases d with
  | TB => dsimp only [orientPoint, shiftPoint, rankCoord]; omega
  | BT => dsimp only [orientPoint, shiftPoint, rankCoord]; omega
  | LR => dsimp only [orientPoint, shiftPoint, rankCoord]; omega
  | RL => dsimp only [orientPoint, shiftPoint, rankCoord]; omega

theorem shift_orient_point_ne_of_y_ne (d : Direction) (h dx dy : Int) {p q : Point}
    (hne : p.y ≠ q.y) :
    shiftPoint dx dy (orientPoint d h p) ≠ shiftPoint dx dy (orientPoint d h q) := by
  intro heq
  have hrk := congrArg (rankCoord d) heq
  have hne_rk := rankCoord_shift_orient_ne_of_y_ne d h dx dy hne
  exact hne_rk hrk

/-- Transport a route point along with its polyline: if `p` is on `pts`, then the transported point
is on the transported polyline. -/
theorem route_transport_onPolyline (d : Direction) (h dx dy : Int) {pts : List Point} {p : Point}
    (hp : onPolyline pts p) :
    onPolyline (pts.map (fun q => shiftPoint dx dy (orientPoint d h q)))
               (shiftPoint dx dy (orientPoint d h p)) :=
  (onPolyline_shift_orient d h dx dy pts p).mpr hp

/-- When two route polylines have trunk points with distinct y-coordinates, their transported
points lie on their respective transported polylines and have distinct rank coordinates. -/
theorem route_trunk_rankCoord_separate (d : Direction) (h dx dy : Int)
    {pts1 pts2 : List Point} {t1 t2 : Point}
    (hp1 : onPolyline pts1 t1) (hp2 : onPolyline pts2 t2)
    (hne : t1.y ≠ t2.y) :
    let t1' := shiftPoint dx dy (orientPoint d h t1)
    let t2' := shiftPoint dx dy (orientPoint d h t2)
    onPolyline (pts1.map (fun q => shiftPoint dx dy (orientPoint d h q))) t1' ∧
    onPolyline (pts2.map (fun q => shiftPoint dx dy (orientPoint d h q))) t2' ∧
    rankCoord d t1' ≠ rankCoord d t2' ∧
    t1' ≠ t2' := by
  intro t1' t2'
  refine ⟨route_transport_onPolyline d h dx dy hp1,
          route_transport_onPolyline d h dx dy hp2,
          rankCoord_shift_orient_ne_of_y_ne d h dx dy hne,
          shift_orient_point_ne_of_y_ne d h dx dy hne⟩

/-- Given two forward routes in `routePointsWithLanes` corresponding to conflicting segments with
distinct slots, their transported polylines have distinct points with separated rank coordinates. -/
theorem routePointsWithLanes_forward_trunks_rankCoord_separate
    (d : Direction) (h dx dy : Int)
    {slot : Int} {p : Proper} {layers : List (List Nat)} {_x _y top : List Int}
    {lr : RouteImpl.LaneRouting}
    {rt1 rt2 : EdgeRoute}
    {e1 e2 : Nat}
    (hp1 : onPolyline rt1.points ⟨runOf lr.routing e1, midOf p slot top (layers.map (RouteImpl.layerHeight p)) lr.routing e1⟩)
    (hp2 : onPolyline rt2.points ⟨runOf lr.routing e2, midOf p slot top (layers.map (RouteImpl.layerHeight p)) lr.routing e2⟩)
    (hne : midOf p slot top (layers.map (RouteImpl.layerHeight p)) lr.routing e1 ≠
           midOf p slot top (layers.map (RouteImpl.layerHeight p)) lr.routing e2) :
    let t1' := shiftPoint dx dy (orientPoint d h ⟨runOf lr.routing e1, midOf p slot top (layers.map (RouteImpl.layerHeight p)) lr.routing e1⟩)
    let t2' := shiftPoint dx dy (orientPoint d h ⟨runOf lr.routing e2, midOf p slot top (layers.map (RouteImpl.layerHeight p)) lr.routing e2⟩)
    onPolyline (rt1.points.map (fun q => shiftPoint dx dy (orientPoint d h q))) t1' ∧
    onPolyline (rt2.points.map (fun q => shiftPoint dx dy (orientPoint d h q))) t2' ∧
    rankCoord d t1' ≠ rankCoord d t2' ∧
    t1' ≠ t2' :=
  route_trunk_rankCoord_separate d h dx dy hp1 hp2 hne

/-- Given two reversed lanes with distinct slot-derived trunk coordinates, their transported
polylines have distinct points with separated rank coordinates. -/
theorem routePointsWithLanes_reversed_trunks_rankCoord_separate
    (d : Direction) (h dx dy : Int)
    {rt1 rt2 : EdgeRoute}
    {t1 t2 : Point}
    (hp1 : onPolyline rt1.points t1)
    (hp2 : onPolyline rt2.points t2)
    (hne : t1.y ≠ t2.y) :
    let t1' := shiftPoint dx dy (orientPoint d h t1)
    let t2' := shiftPoint dx dy (orientPoint d h t2)
    onPolyline (rt1.points.map (fun q => shiftPoint dx dy (orientPoint d h q))) t1' ∧
    onPolyline (rt2.points.map (fun q => shiftPoint dx dy (orientPoint d h q))) t2' ∧
    rankCoord d t1' ≠ rankCoord d t2' ∧
    t1' ≠ t2' :=
  route_trunk_rankCoord_separate d h dx dy hp1 hp2 hne

end Layered
end Elegant

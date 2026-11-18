import ElegantGeometry.Route
import Elegant.Layered.Pipeline

set_option autoImplicit false

/-! A route polyline confined to a nondegenerate rectangle misses the open interior of
every rectangle disjoint from that rectangle.

The confinement hypothesis is stated with `PointIn`, because the geometry library has no
closed point-containment predicate. The nondegeneracy hypothesis `0 < box.w ∧ 0 < box.h`
is not removable: a polyline may be confined to a degenerate box (a segment or a point)
while its points lie strictly inside a rectangle whose open interior is disjoint from the
degenerate box's interior. Example: `pts = [⟨10,10⟩, ⟨10,10⟩]`, `box = ⟨10,10,0,0⟩`, and
`rect = ⟨0,0,20,20⟩` satisfy confinement and `Disjoint box rect`, yet `hitsRect` holds.

The transport corollaries apply the same `PipelineImpl.shiftPoint` / `shiftRect` /
`orientPoint` / `orientRect` maps that packing and scene assembly use, so a component-local
route that lies in its part box misses any box that is disjoint from that part box. -/

namespace Elegant
namespace Layered

/-- Closed containment of a point in a rectangle. -/
def PointIn (box : Rect) (p : Point) : Prop :=
  box.x ≤ p.x ∧ p.x ≤ box.x + box.w ∧ box.y ≤ p.y ∧ p.y ≤ box.y + box.h

/-- Two disjoint rectangles with nonempty interiors are separated on one axis. -/
theorem disjoint_axis_separated {box rect : Rect}
    (hbw : 0 < box.w) (hbh : 0 < box.h) (hrw : 0 < rect.w) (hrh : 0 < rect.h)
    (hd : Disjoint box rect) :
    box.x + box.w ≤ rect.x ∨ rect.x + rect.w ≤ box.x ∨
      box.y + box.h ≤ rect.y ∨ rect.y + rect.h ≤ box.y := by
  unfold Disjoint Rect.meetsInterior at hd
  omega

/-- A segment whose endpoints lie in `box` misses every rectangle separated from `box` on
an axis. -/
theorem segMisses_of_pointIn_of_separated {box rect : Rect} {p q : Point}
    (hsep : box.x + box.w ≤ rect.x ∨ rect.x + rect.w ≤ box.x ∨
      box.y + box.h ≤ rect.y ∨ rect.y + rect.h ≤ box.y)
    (hp : PointIn box p) (hq : PointIn box q) :
    Polyline.segMisses p q rect := by
  unfold PointIn at hp hq
  rcases hsep with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))

/-- Every segment of a polyline confined to `box` misses a rectangle separated from
`box`. -/
theorem allSegsMiss_of_pointIn_of_separated {box rect : Rect}
    (hsep : box.x + box.w ≤ rect.x ∨ rect.x + rect.w ≤ box.x ∨
      box.y + box.h ≤ rect.y ∨ rect.y + rect.h ≤ box.y) :
    ∀ (pts : List Point), (∀ p ∈ pts, PointIn box p) →
      Polyline.allSegsMiss pts rect := by
  intro pts
  induction pts with
  | nil => intro _; trivial
  | cons p rest ih =>
    intro hin
    cases rest with
    | nil => trivial
    | cons q rest' =>
      exact ⟨segMisses_of_pointIn_of_separated hsep (hin p (by simp))
          (hin q (by simp)),
        ih (fun z hz => hin z (by simp [hz]))⟩

/-- A polyline confined to a nondegenerate rectangle misses the open interior of every
rectangle disjoint from it. -/
theorem polyline_in_box_misses_disjoint {pts : List Point} {box rect : Rect}
    (hbw : 0 < box.w) (hbh : 0 < box.h)
    (hin : ∀ p ∈ pts, PointIn box p) (hd : Disjoint box rect) :
    ¬ Polyline.hitsRect pts rect := by
  intro hhit
  obtain ⟨hrw, hrh, hmiss⟩ := hhit
  exact hmiss
    (allSegsMiss_of_pointIn_of_separated (disjoint_axis_separated hbw hbh hrw hrh hd) pts hin)

/-- Packing translation preserves closed point containment. -/
theorem pointIn_shift {box : Rect} {dx dy : Int} {p : Point} (h : PointIn box p) :
    PointIn (PipelineImpl.shiftRect dx dy box) (PipelineImpl.shiftPoint dx dy p) := by
  simp only [PointIn, PipelineImpl.shiftRect, PipelineImpl.shiftPoint] at h ⊢
  omega

/-- Direction orientation preserves closed point containment. -/
theorem pointIn_orient {box : Rect} {d : Direction} {H : Int} {p : Point}
    (h : PointIn box p) :
    PointIn (PipelineImpl.orientRect d H box) (PipelineImpl.orientPoint d H p) := by
  unfold PointIn at h ⊢
  cases d <;> simp only [PipelineImpl.orientRect, PipelineImpl.orientPoint] at * <;> omega

/-- Packing translation preserves rectangle disjointness. -/
theorem disjoint_shift_iff {a b : Rect} {dx dy : Int} :
    Disjoint (PipelineImpl.shiftRect dx dy a) (PipelineImpl.shiftRect dx dy b) ↔
      Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  simp only [PipelineImpl.shiftRect]
  constructor <;> intro h hc <;> exact h (by omega)

/-- Direction orientation preserves rectangle disjointness. -/
theorem disjoint_orient_iff {a b : Rect} {d : Direction} {H : Int} :
    Disjoint (PipelineImpl.orientRect d H a) (PipelineImpl.orientRect d H b) ↔
      Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  cases d <;> simp only [PipelineImpl.orientRect] <;>
    constructor <;> intro h hc <;> exact h (by omega)

/-- Scene assembly transport (`orient` then `shift`) preserves closed point containment. -/
theorem pointIn_scene {box : Rect} {d : Direction} {H margin : Int} {p : Point}
    (h : PointIn box p) :
    PointIn (PipelineImpl.shiftRect margin margin (PipelineImpl.orientRect d H box))
      (PipelineImpl.shiftPoint margin margin (PipelineImpl.orientPoint d H p)) :=
  pointIn_shift (pointIn_orient h)

/-- Scene assembly transport preserves rectangle disjointness. -/
theorem disjoint_scene_iff {a b : Rect} {d : Direction} {H margin : Int} :
    Disjoint (PipelineImpl.shiftRect margin margin (PipelineImpl.orientRect d H a))
      (PipelineImpl.shiftRect margin margin (PipelineImpl.orientRect d H b)) ↔
      Disjoint a b := by
  rw [disjoint_shift_iff, disjoint_orient_iff]

/-- A packed route confined to its own packed box misses every box disjoint from that
box, both given in part-local coordinates. -/
theorem route_misses_disjoint_shift {pts : List Point} {box foreign : Rect} {dx dy : Int}
    (hbw : 0 < box.w) (hbh : 0 < box.h)
    (hin : ∀ p ∈ pts, PointIn box p) (hd : Disjoint box foreign) :
    ¬ Polyline.hitsRect (pts.map (PipelineImpl.shiftPoint dx dy))
      (PipelineImpl.shiftRect dx dy foreign) := by
  refine polyline_in_box_misses_disjoint ?_ ?_ ?_ (disjoint_shift_iff.mpr hd)
  · simp only [PipelineImpl.shiftRect]; omega
  · simp only [PipelineImpl.shiftRect]; omega
  · intro p' hp'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
    exact pointIn_shift (hin p hp)

/-- A scene route confined to its component's box misses every box disjoint from that
component's box, under the exact `orient`-then-`shift` maps of scene assembly. -/
theorem route_misses_disjoint_scene {pts : List Point} {box foreign : Rect}
    {d : Direction} {H margin : Int}
    (hbw : 0 < box.w) (hbh : 0 < box.h)
    (hin : ∀ p ∈ pts, PointIn box p) (hd : Disjoint box foreign) :
    ¬ Polyline.hitsRect
      (pts.map fun p =>
        PipelineImpl.shiftPoint margin margin (PipelineImpl.orientPoint d H p))
      (PipelineImpl.shiftRect margin margin (PipelineImpl.orientRect d H foreign)) := by
  refine polyline_in_box_misses_disjoint ?_ ?_ ?_ (disjoint_scene_iff.mpr hd)
  · cases d <;> simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect] <;> omega
  · cases d <;> simp only [PipelineImpl.orientRect, PipelineImpl.shiftRect] <;> omega
  · intro p' hp'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
    exact pointIn_scene (hin p hp)

/-- Disjointness is downward closed in the second argument under closed containment:
a box contained in a rectangle disjoint from `a` is itself disjoint from `a`. -/
theorem disjoint_contained_right {a b c : Rect} (hd : Disjoint a b)
    (hsub : b.Contained c) : Disjoint a c := by
  unfold Disjoint Rect.meetsInterior Rect.Contained at *
  intro h
  exact hd ⟨by omega, by omega⟩

/-- Closed point containment is the same as containing the degenerate point rectangle. -/
theorem pointIn_contained {box : Rect} {p : Point} :
    PointIn box p ↔ box.Contained ⟨p.x, p.y, 0, 0⟩ := by
  constructor <;> intro h <;>
    simp only [PointIn, Rect.Contained] at h ⊢ <;> omega

/-- Flat C6 across components: a route confined to its own component's packed box
misses the open interior of any foreign node box contained in a different component's
packed box, whenever the packed component boxes are disjoint. The three hypotheses are
each separately establishable from repository facts: route confinement from the part's
`PartBounded` route bounds under the packing shift, foreign containment from the part's
`PartBounded` rect bounds under the same shift, and disjointness from
`pack_components_disjoint`. -/
theorem componentRoute_misses_foreign_component_box {pts : List Point}
    {own foreign foreignPacked : Rect}
    (hbw : 0 < own.w) (hbh : 0 < own.h)
    (hin : ∀ p ∈ pts, PointIn own p)
    (hsub : foreignPacked.Contained foreign)
    (hd : Disjoint own foreignPacked) :
    ¬ Polyline.hitsRect pts foreign :=
  polyline_in_box_misses_disjoint hbw hbh hin (disjoint_contained_right hd hsub)

end Layered
end Elegant
